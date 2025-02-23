/*
 *     The Certora Prover
 *     Copyright (C) 2025  Certora Ltd.
 *
 *     This program is free software: you can redistribute it and/or modify
 *     it under the terms of the GNU General Public License as published by
 *     the Free Software Foundation, version 3 of the License.
 *
 *     This program is distributed in the hope that it will be useful,
 *     but WITHOUT ANY WARRANTY; without even the implied warranty of
 *     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *     GNU General Public License for more details.
 *
 *     You should have received a copy of the GNU General Public License
 *     along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package utils

import datastructures.stdcollections.*

/*
    Lazy initialization wrappers that fail fast on initializer recursion

    Our extensive use of `parallelStream` and `ForkJoinPool` makes accidental recursive initialization very likely.  For
    example, consider the following:

    ```
        val lazyStuff = lazy {
            b.parallelStream().map {
                b.foo()
            }.toList()
        }

        ...

        val analyzedA = a.parallelStream().map {
            a.analyze(lazyStuff)
        }.toList()
    ```

    If `lazyStuff` is not yet initialized when `analyszedA` is being computed, the `lazyStuff` lazy initializer will be
    triggered from within the parallel map operation.  This results in a nested parallel map operation inside of the
    initializer lambda.  That parallel stream operation may reach a point where it decides to "steal" work from other
    threads, at which point is may end up trying to execute more iterations of the outer parallel map operation.  This
    in turn will try to evaluate the lazy initializer again, recursively.

    This in turn breaks the fork/join framework's assumptions about the structure of the computation graph (that it's a
    DAG), and can lead to non-deterministic deadlocks and other failures.

    So, we have our own version of `lazy`, which will fail fast if the initializer is re-entered recursively.  We
    require the use of this version, rather than the standard library version, to ensure that we don't accidentally
    introduce recursive lazy initialization bugs.
 */

@Suppress("ForbiddenMethodCall")
fun <T> lazy(mode: LazyThreadSafetyMode, initializer: () -> T ): Lazy<T> {
    lateinit var lazy: Lazy<T>
    lazy = kotlin.lazy(mode) {
        recursionGuard(lazy) {
            initializer()
        }
    }
    return lazy
}

fun <T> lazy(initializer: () -> T): Lazy<T> = lazy(LazyThreadSafetyMode.SYNCHRONIZED, initializer)


@PublishedApi
internal val recursionGuardTokens = ThreadLocal.withInitial { mutableSetOf<Any>() }

/**
    Fail-fast recursion guard.  If the same token is passed to this function more than once on the same call stack, an
    error will be thrown.  This is useful for detecting accidental recursion as described above.
 */
inline fun <T> recursionGuard(token: Any, action: () -> T): T {
    val localTokens = recursionGuardTokens.get()
    if (!localTokens.add(token)) {
        error("Re-entered $token")
    }
    try {
        return action()
    } finally {
        localTokens.remove(token)
    }
}
