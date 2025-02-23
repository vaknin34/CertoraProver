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

package tac

import com.certora.collect.*
import datastructures.stdcollections.*
import utils.CertoraInternalErrorType
import utils.CertoraInternalException
import utils.*

// Tags map from [T], a variable type, to a [Tag].  The mapping is primarily defined by T itself, but may be overridden.

@Treapable
data class Tags<@Treapable T : Tagged> private constructor(
    private val tagged: TreapSet<T> = treapSetOf<T>(),
    private val overrides: TreapMap<T, Tag> = treapMapOf<T, Tag>()
) : java.io.Serializable {

    constructor(tagged: Set<T>) : this(tagged.toTreapSet())

    fun isEmpty() = tagged.isEmpty()

    fun builder() = Builder(this)

    inline fun mutate(mutate: (Builder<T>) -> Unit) = builder().also { mutate(it) }.build()

    operator fun get(key: T) = overrides[key] ?: tagged.findEqual(key)?.tag

    operator fun contains(key: T) = key in tagged

    val keys get() = tagged

    fun forEach(action: (T, Tag) -> Unit) {
        tagged.forEach {
            action(it, overrides[it] ?: it.tag)
        }
    }

    fun asSequence() = tagged.asSequence().zip(tagged.asSequence().map { overrides[it] ?: it.tag })

    /**
     * first sort all the tagged items, then iterate it similar to [asSequence] - with the override version
     */
    fun <R: Comparable<R>> sortedSequence(selector: (T) -> R?) = tagged.asSequence().sortedBy<T,R>(selector).let {
        it.asSequence().zip(it.asSequence().map { overrides[it] ?: it.tag })
    }

    fun overwriteTags(other: Tags<T>): Tags<T> = mutate { it.overwriteTags(other) }
    fun overwriteTags(other: Set<T>): Tags<T> = mutate { it.overwriteTags(other) }
    fun mergeTags(other: Tags<T>): Tags<T> = mutate { it.mergeTags(other) }
    fun mergeTags(other: Set<T>): Tags<T> = mutate { it.mergeTags(other) }

    class Builder<@Treapable T : Tagged> private constructor(
        private var tagged: TreapSet<T>,
        private var overrides: TreapMap<T, Tag>
    ) {
        constructor(tags: Tags<T>) : this(tags.tagged, tags.overrides)

        fun build() = Tags(tagged, overrides)

        operator fun get(key: T) = overrides[key] ?: tagged.findEqual(key)?.tag

        operator fun set(k: T, v: Tag) {
            val prevKey = tagged.findEqual(k)
            if (prevKey == null) {
                tagged += k
                if (k.tag != v) {
                    overrides += k to v
                }
            } else {
                val prevVal = overrides[k] ?: prevKey.tag
                if (prevVal != v) {
                    if (prevKey.tag == v) {
                        overrides -= k
                    } else {
                        overrides += k to v
                    }
                }
            }
        }

        fun safePut(k: T, v: Tag) {
            val prev = get(k)
            if (prev != null) {
                tagsCheck(prev == v) { "Failed to put $k with tag $v since it already exists with tag $prev" }
            }
            set(k, v)
        }

        fun mergeTags(other: Tags<T>) {
            other.forEach { k, v ->
                val prev = get(k)
                tagsCheck(prev == null || prev == v) { "Got collision on variable ${k}. Existing tag is ${prev}, new tag is ${v}" }
            }
            overwriteTags(other)
        }

        fun mergeTags(other: Set<T>) {
            other.forEach { k ->
                val prev = get(k)
                tagsCheck(prev == null || prev == k.tag) { "Got collision on variable ${k}. Existing tag is ${prev}, new tag is ${k.tag}" }
            }
            overwriteTags(other)
        }

        fun overwriteTags(other: Tags<T>) {
            /*
             Some Tagged types have weird equality semantics that ignore the tag.  (I'm looking at you, TACSymbol.Var!)
             And we depend, intentionally or otherwise, on our Tags collection containing the tag from the first
             instance that was added to it, and not getting overwritten by new Tagged instances that compare equal to
             old ones, but have a different tag.

             The underlying treap-based implementation of our `tagged` set takes equality comparisons very literally,
             and feels free to substitute one object for another as long as they compare equal.  It uses this to
             optimize memory usage in some cases.  But we can't have that here, because of those broken equality
             semantics.

             So...we have to be careful to only add Tagged instances that *don't* compare equal to existing instances.

             So, in this case, `tagged + other.tagged` is materially different from `tagged + (other.tagged - tagged)`,
             despite what you might think about set theory.

             The TACSymbol.Var equality issue is covered by CER-1455.  This workaround can hopefully be removed when
             that is complete.
             */
            tagged += other.tagged - tagged

            /*
             Overrides aren't subject to the weirdness above, since we don't get the tag from the key.
             */
            overrides = overrides.union(other.overrides) { _, _, v2 -> v2 }
        }

        fun overwriteTags(other: Set<T>) = overwriteTags(Tags(other))
    }

    companion object {
        private val _empty = Tags<Nothing>()
        fun <@Treapable T : Tagged> emptyOf() = _empty.uncheckedAs<Tags<T>>()

        private inline fun tagsCheck(cond: Boolean, msg: (() -> String)) {
            if (!cond) {
                throw TagsException(msg().let { "Bad Tags: $it" })
            }
        }
    }
}


class TagsException(msg: String): CertoraInternalException(CertoraInternalErrorType.TAC_TYPING, msg)

fun <@Treapable T : Tagged> emptyTags() = Tags.emptyOf<T>()
fun <@Treapable T : Tagged> tagsBuilder() = emptyTags<T>().builder()
