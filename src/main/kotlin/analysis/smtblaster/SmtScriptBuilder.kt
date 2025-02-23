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

package analysis.smtblaster

abstract class SmtScriptBuilder<SortType, ReprType>(protected val v: ISMTTermBuilder<SortType, ReprType>) :
    ISMTTermBuilder<SortType, ReprType> by v {
    fun assert(f: SmtScriptBuilder<SortType, ReprType>.() -> ReprType) {
        this.addAssert(this.f())
    }

    fun declare(s: String) {
        this.declare(s, v.numericType)
    }

    fun declareFun(s: String, arity: Int) {
        this.declareFun(s, List(arity) {
            v.numericType
        }, v.numericType)
    }

    override fun plus(vararg ops: ReprType): ReprType {
        return super.plus(*ops)
    }

    override fun mult(vararg ops: ReprType): ReprType {
        return super.mult(*ops)
    }

    abstract protected fun declareFun(nm: String, args: List<SortType>, ret: SortType)

    abstract infix fun ReprType.implies(other: ReprType): ReprType

    abstract fun forall(f: SmtScriptBuilder<SortType, ReprType>.(ReprType) -> ReprType): ReprType

    abstract fun forall(f: SmtScriptBuilder<SortType, ReprType>.(ReprType, ReprType) -> ReprType): ReprType

    fun define(s: String, f: ISMTTermBuilder<SortType, ReprType>.() -> ReprType) {
        this.define(s, v.numericType, v.f())
    }

    abstract fun checkSat()

    abstract protected fun declare(s: String, numericType: SortType)

    abstract protected fun define(s: String, numericType: SortType, body: ReprType)

    abstract protected fun addAssert(f: ReprType)

    abstract fun fork(): SmtScriptBuilder<SortType, ReprType>
}

