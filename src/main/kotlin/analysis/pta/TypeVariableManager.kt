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

package analysis.pta

import analysis.CmdPointer
import analysis.LTACCmd
import com.certora.collect.*
import log.Logger
import log.LoggerTypes
import utils.*

private val logger = Logger(LoggerTypes.POINTS_TO)

/**
A "Type" variable represents an instance where we encounter the constant 0x60 and do not immediately know if
it represents the "polymorphic" empty array constant, or the constant 96. Each occurrence is mapped to a unique,
singleton type variable. These type variables are lazily resolved during analysis using context clues. These
clues are heuristic, but in general, a type variable is resolved in the following situations:

1) When joined with a known resolved type/value: to whatever the other type/value is)
2) when used in any arithmetic operation (including addition, where it could plausibly still be a pointer): to INT
3) When used to index into memory: to POINTER

Generally, the values that wrap around the type variable expose the following high level operations:

1) tryResolve(): if the wrapped value is a resolved type variable, eagerly resolve it, otherwise no-op. No-op on non-var types
2) tryResolveX(): if the wrapped value is *NOT* yet resolved, resolve it as an X. May fail on resolved pointers. No-op on non-var types
3) expectX(): if the wrapped value is *not* yet resolved, resolve it as an X. May fail on resolved pointer. On non-var types, may fail as well.
 */

open class TypeVariableInfrastructure<T: TypeVariableInfrastructure<T>> {
    private var resolved = false
    private var resolvedLeft = false
    private var unificand: T? = null

    fun T.unifyImpl(other: T) : T {
        val uf = this.findImpl()
        val otherF = other.findImpl()
        if(uf === otherF) {
            return uf
        }
        if(otherF.resolved) {
            if (uf.resolved) {
                check(uf.resolvedLeft == other.resolvedLeft)
            }
            uf.unificand = otherF
            return otherF
        }
        otherF.unificand = uf
        return uf
    }

    fun findWeak(): TypeVariableInfrastructure<*> {
        val uf = this.unificand
        return if (uf != null) {
                val parent = uf.findImpl()
                this.unificand = parent
                parent
        } else {
            this
        }
    }

    fun T.findImpl(): T {
        val uf = this.unificand
        return if (uf != null) {
            val parent = uf.findImpl()
            this.unificand = parent
            parent
        } else {
            this
        }
    }

    private fun resolveFlag(resolveToLeft: Boolean) {
        if (resolved && resolvedLeft != resolveToLeft)  {
            throw AnalysisFailureException("Mismatched type variable")
        } else {
            resolved = true
            resolvedLeft = resolveToLeft
        }
    }

    fun isUnifiedWithImpl(other: T): Boolean = this.findWeak() === other.findWeak()
    fun isResolvedImpl() = findWeak().resolved


    fun isResolvedLeft(): Boolean {
        val r = findWeak()
        return r.resolved && r.resolvedLeft
    }
    fun isResolvedRight(): Boolean {
        val r = findWeak()
        return r.resolved && !r.resolvedLeft
    }

    protected fun expectLeft() = findWeak().resolveFlag(true)
    protected fun expectRight() = findWeak().resolveFlag(false)

    protected fun <R> expectLeft(iVal: R): R {
        findWeak().resolveFlag(true)
        return iVal
    }

    protected fun <R> expectRight(pVal: R): R {
        findWeak().resolveFlag(false)
        return pVal
    }

    protected fun <R> ifResolvedChoose(leftChoice: R, rightChoice: R): R? {
        val ptr = findWeak()
        if (!ptr.resolved) {
            return null
        }
        return if (ptr.resolvedLeft) {
            leftChoice
        } else {
            rightChoice
        }
    }

}

sealed class PointerClassificationVar<T: TypeVariableInfrastructure<T>> : TypeVariableInfrastructure<T>() {
    open fun isResolvedArray() = this.isResolvedRight()

    open fun <R> expectPointer(v: R) : R {
        return expectRight(v)
    }
}

fun <T: TypeVariableInfrastructure<T>> T.unify(other: T) = unifyImpl(other)
fun <T: TypeVariableInfrastructure<T>> T.find() = findImpl()
fun <T: TypeVariableInfrastructure<T>> TypeVariableInfrastructure<T>.isResolved() = isResolvedImpl()
fun <T: TypeVariableInfrastructure<T>> TypeVariableInfrastructure<T>.isUnifiedWith(other: T) = isUnifiedWithImpl(other)

// Take care when serializing these.  The type variables here implement union find, which means that the sharing that is
// thrown away by kotlin serialization will cause significant memory expansion.  the only time we'll ever be serializing
// these results is after the graph of type variables has stabilized, so it's probably not a terrible issue in practice.
@KSerializable
@Treapable
class TypeVariable(private val typeId: Int, val where: LTACCmd) : PointerClassificationVar<TypeVariable>() {
    override fun hashCode() = hash { it + typeId + where }

    fun <R> expectInt(iVal: R): R {
        try {
            return expectLeft(iVal)
        } catch(e: AnalysisFailureException) {
            logger.warn(e) { "For a type variable $typeId (for const at $where) we expected Int but found it was already resolved to Pointer" }
            throw e
        }
    }

    override fun <R> expectPointer(v: R): R {
        try {
            return expectRight(v)
        } catch(e: AnalysisFailureException) {
            logger.warn(e) { "For a type variable $typeId (for const at $where) we expected Pointer but found it was already resolved to Int" }
            throw e
        }
    }

    fun <R> ifResolved(intChoice: R, ptrChoice: R): R? {
        return ifResolvedChoose(intChoice, ptrChoice)
    }

    fun resolvedInt(): Boolean {
        return isResolvedLeft()
    }

    override fun toString(): String {
        return "\$$typeId = {r=${this.isResolved()}, i=${this.resolvedInt()}}"
    }
}

class TypeVariableAlloc(private val typeId: Int, val where: L) : PointerClassificationVar<TypeVariableAlloc>() {
    fun expectBlock() {
        try {
            expectLeft()
        } catch (e: AnalysisFailureException) {
            logger.warn { "For a type variable alloc $typeId (for alloc at $where) we expected Block but found it was already resolved to EmptyArray" }
            throw e
        }
    }

    fun expectEmptyArray() {
        try {
            expectRight()
        } catch (e: AnalysisFailureException) {
            logger.warn { "For a type variable alloc $typeId (for alloc at $where) we expected EmptyArray but found it was already resolved to Block" }
            throw e
        }
    }

    fun isResolvedBlock(): Boolean = isResolvedLeft()
    override fun isResolvedArray(): Boolean = isResolvedRight()

    override fun toString(): String {
        return "\$$typeId = {r=${this.isResolved()}, b=${this.isResolvedBlock()}}"
    }
}

class TypeVariableManager {
    private var idCounter = 0

    private val cache = mutableMapOf<CmdPointer, TypeVariable>()
    private val cacheAlloc = mutableMapOf<L,TypeVariableAlloc>()

    fun getVariableForSite(where: LTACCmd): TypeVariable {
        return cache.computeIfAbsent(where.ptr) {
            TypeVariable(idCounter++, where)
        }
    }

    fun getVariableForAlloc(where: L): TypeVariableAlloc {
        return cacheAlloc.computeIfAbsent(where) {
            TypeVariableAlloc(idCounter++, where)
        }
    }

    fun getVariableForAllocOrNull(where: L): TypeVariableAlloc? {
        return cacheAlloc[where]
    }
}
