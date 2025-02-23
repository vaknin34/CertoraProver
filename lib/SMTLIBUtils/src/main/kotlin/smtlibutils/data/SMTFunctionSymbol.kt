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

package smtlibutils.data

import datastructures.stdcollections.*

private const val DUMMY_BITWIDTH: Int = -1

abstract class SmtFunctionSymbol(open val name: Identifier, open val rank: Rank) : java.io.Serializable {
    constructor(name: String, rank: Rank) : this(Identifier.Simple(name), rank)

    companion object {
        fun fromIdentifier(id: Identifier, symbolTable: SmtSymbolTable): SmtFunctionSymbol {
            val knownFs = getKnownFunctionSymbol(id)
            if (knownFs != null) return knownFs
            return symbolTable.lookUpFunction(id)?.functionSymbol ?: error("$this: lookup of $id failed")
        }

        fun fromIdentifier(id: Identifier): SmtFunctionSymbol {
            val knownFs = getKnownFunctionSymbol(id)
            if (knownFs != null) return knownFs
            return SmtUnintpFunctionSymbol(id, Rank.Unknown)
        }

    }

    open fun toSMTLIBString(): String = name.toString()

    open fun instantiateParamSorts(paramSorts: List<Sort>): SmtFunctionSymbol =
        SmtUnintpFunctionSymbol(name, Sort.Unification.unifyParamSorts(this.rank, paramSorts))

    open fun instantiateResultSort(resultSort: Sort): SmtFunctionSymbol =
        SmtUnintpFunctionSymbol(name, Sort.Unification.unifyResultSort(this.rank, resultSort))

    fun isBoolAtomWhenApplied() =
        rank.resultSort == Sort.BoolSort && (rank.paramSorts.any { it != Sort.BoolSort } || rank.paramSorts.isEmpty())

    fun isBooleanConnective() = rank.paramSorts.all { it == Sort.BoolSort } && rank.resultSort == Sort.BoolSort

    fun getConcreteResultSortOrNull(): Sort? {
        return if (rank == Rank.Unknown || rank.resultSort.isParametrized()) null else rank.resultSort
    }
}

/**
 * If [functionSymbolName] matches the name of any of the function symbols we have a fixed meaning for (e.g. "+", or
 *  "uninterp_mul", etc.)
 */
fun getKnownFunctionSymbol(functionSymbolName: Identifier): SmtFunctionSymbol? {
    val smtfs = SmtIntpFunctionSymbol.fromIdentifier(functionSymbolName)
    if (smtfs != null) return smtfs
    return null
}

open class SmtUnintpFunctionSymbol(
    override val name: Identifier, override val rank: Rank
) : SmtFunctionSymbol(name, rank) {

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as SmtUnintpFunctionSymbol

        if (name != other.name) return false
        if (rank != other.rank) return false

        return true
    }

    override fun hashCode(): Int {
        var result = name.hashCode()
        result = 31 * result + rank.hashCode()
        return result
    }
}

sealed class SmtIntpFunctionSymbol(
    override val name: Identifier,
    override val rank: Rank,
) : SmtFunctionSymbol(name, rank) {

    companion object {
        fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? {
            return Array.fromIdentifier(id) ?: BV.fromIdentifier(id) ?: Core.fromIdentifier(id) ?: DT.fromIdentifier(id)
            ?: IRA.fromIdentifier(id) ?: Reals.fromIdentifier(id) ?: Ints.fromIdentifier(id)
        }

        val defaultSortParamA = Sort.Param("A")
        val defaultSortParamN = Sort.Param("N")
    }

    sealed class Array(
        override val name: Identifier, override val rank: Rank
    ) : SmtIntpFunctionSymbol(name, rank) {
        constructor(name: String, rank: Rank) : this(
            Identifier.Simple(name), rank
        )

        /** (par (X Y) (select (Array X Y) X Y))
         *  NB: don't use copy() as it circumvents caching. */
        data class Select(val X: Sort = Sort.Param("X"), val Y: Sort = Sort.Param("Y")) : Array(
            fsIdName, Rank(Sort.arraySort(X, Y), X, Y)
        ) {
            override fun instantiateParamSorts(paramSorts: List<Sort>): SmtIntpFunctionSymbol {
                check(paramSorts.size == 2)
                val instantiatedParamSorts = Sort.Unification.unifyParamSorts(this.rank, paramSorts)
                return Select(instantiatedParamSorts.paramSorts[1], instantiatedParamSorts.resultSort)
            }

            override fun instantiateResultSort(resultSort: Sort): SmtFunctionSymbol {
                return Select(X = this.X, Y = resultSort)
            }

            companion object {
                const val fsIdName = "select"
                fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? =
                    (id as? Identifier.Simple)?.let { if (it.sym == fsIdName) Select() else null }
            }
        }

        /** (par (X Y) (store (Array X Y) X Y (Array X Y)))
         * NB: don't use copy(), as it circumvents hashing. */
        class Store(val X: Sort = Sort.Param("X"), val Y: Sort = Sort.Param("Y")) : Array(
            fsIdName, Rank(Sort.arraySort(X, Y), X, Y, Sort.arraySort(X, Y))
        ) {
            override fun instantiateParamSorts(paramSorts: List<Sort>): SmtIntpFunctionSymbol {
                check(paramSorts.size == 3)
                val instantiatedParamSorts = Sort.Unification.unifyParamSorts(this.rank, paramSorts)
                return Store(instantiatedParamSorts.paramSorts[1], instantiatedParamSorts.paramSorts[2])
            }

            override fun instantiateResultSort(resultSort: Sort): SmtFunctionSymbol {
                check(resultSort is Sort.Apply && resultSort.symbol == SortSymbol.Intp.Array)
                return Store(resultSort.params[0], resultSort.params[1])
            }

            companion object {
                const val fsIdName = "store"
                fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? =
                    (id as? Identifier.Simple)?.let { if (it.sym == fsIdName) Store() else null }
            }
        }

        /**
         * Takes a constant and yields an array has that constant at every index. Index type must be specified via
         * `as ..`-syntax.
         *
         * Note that it is not quite clear how solver-specific this is, it's not specified on
         *   [http://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml],
         *  but I think it is very common (z3, cvc4, smtinterpol all support it)
         *
         *  NB: don't use copy(), as it circumvents hashing.
         * */
        data class Const(val X: Sort = Sort.Param("X"), val Y: Sort = Sort.Param("Y")) : Array(
            fsIdName, Rank(X, Sort.arraySort(Y, X))
        ) {
            override fun instantiateParamSorts(paramSorts: List<Sort>): SmtIntpFunctionSymbol {
                check(paramSorts.size == 1)
                val instantiatedParamSorts = Sort.Unification.unifyParamSorts(this.rank, paramSorts)
                val resultSort = instantiatedParamSorts.resultSort
                check(resultSort is Sort.Apply)
                check(resultSort.symbol == SortSymbol.Intp.Array)
                check(resultSort.params[1] == instantiatedParamSorts.paramSorts[0])
                return Const(instantiatedParamSorts.paramSorts[0], Y)
            }

            override fun instantiateResultSort(resultSort: Sort): SmtFunctionSymbol {
                val instantiatedResultSort = Sort.Unification.unifyResultSort(this.rank, resultSort)

                @Suppress("NAME_SHADOWING") val resultSort = instantiatedResultSort.resultSort
                check(resultSort is Sort.Apply)
                check(resultSort.symbol == SortSymbol.Intp.Array)
                check(resultSort.params[1] == instantiatedResultSort.paramSorts[0])
                return Const(
                    X = resultSort.params[1], Y = resultSort.params[0]
                )
            }

            override fun toSMTLIBString() = "(as $fsIdName (Array $Y $X))"

            companion object {
                const val fsIdName = "const"
                fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? =
                    (id as? Identifier.Simple)?.let { if (it.sym == fsIdName) Const() else null }
            }
        }


        companion object {
            fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? =
                Select.fromIdentifier(id) ?: Store.fromIdentifier(id) ?: Const.fromIdentifier(id)
        }
    }

    sealed class BV(
        override val name: Identifier,
        override val rank: Rank,
    ) : SmtIntpFunctionSymbol(name, rank) {
        /**
         * Represents the SMT-LIB extract operator. Note that i >= j >= 0.
         * The parameter type is left as a parameter and instantiated on demand.
         */
        data class Extract(val i: Int, val j: Int) : BV(
            Identifier.Indexed(fsIdName, listOf("$i", "$j")), Rank(Sort.Param("X"), Sort.bitVecSort(i - j + 1))
        ) {
            init {
                check(i >= j && j >= 0) { "Extract($i, $j) does not satisfy SMT-LIB definition" }
            }

            override fun instantiateParamSorts(paramSorts: List<Sort>): SmtIntpFunctionSymbol {
                check(paramSorts.size == 1)
                val mNew = paramSorts[0].getBitVecSortWidth()
                check(mNew > i && i >= j && j >= 0) { "Instantiated (_ extract ${i} ${j}) on BV${mNew} does not satisfy the SMT-LIB standard" }
                return Extract(this.i, this.j)
            }

            override fun instantiateResultSort(resultSort: Sort): SmtFunctionSymbol =
                throw UnsupportedOperationException("not implemented (this = $this) -- is there an override missing?")

            override fun toSMTLIBString(): String = "(_ $fsIdName $i $j)"

            companion object {
                const val fsIdName = "extract"
                fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? = (id as? Identifier.Indexed)?.let {
                    if (it.sym == fsIdName && it.indices.size == 2) Extract(
                        Integer.parseInt(it.indices[0]), Integer.parseInt(it.indices[1])
                    )
                    else null
                }
            }
        }

        data class Concat(val i: Int = -1, val j: Int = -1) : BV(
            Identifier.Simple(fsIdName), Rank(Sort.bitVecSort(i), Sort.bitVecSort(j), Sort.bitVecSort(i + j))
        ) {

            override fun instantiateParamSorts(paramSorts: List<Sort>): SmtIntpFunctionSymbol {
                check(paramSorts.size == 2)
                check(paramSorts[0].isBitVecSort() && paramSorts[1].isBitVecSort())
                val i = paramSorts[0].getBitVecSortWidth()
                val j = paramSorts[1].getBitVecSortWidth()
                check(i > 0)
                check(j > 0)
                return Concat(i, j)
            }

            override fun instantiateResultSort(resultSort: Sort): SmtFunctionSymbol {
                // TODO: a bit unclear: what to do if result sort is instantiated before param sorts? (CERT-8094)
                check(resultSort == Sort.bitVecSort(i + j))
                return this
            }

            companion object {
                const val fsIdName = "concat"
                fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? = (id as? Identifier.Simple)?.let {
                    if (it.sym == fsIdName) Concat()
                    else null
                }
            }
        }

        /**
         * Represents the SMT-LIB sign_extend operator. Note that i >= 0.
         * The parameter type is left as a parameter and instantiated on demand.
         */
        data class SignExtend(val i: Int, val X: Sort = Sort.Param("X"), val Y: Sort = Sort.Param("Y")) : BV(
            Identifier.Indexed(fsIdName, listOf("$i")), Rank(X, Y)
        ) {
            init {
                check(i >= 0) { "SignExtend($i) does not satisfy SMT-LIB definition" }
            }

            override fun instantiateParamSorts(paramSorts: List<Sort>): SmtIntpFunctionSymbol {
                check(paramSorts.size == 1)
                val arg = paramSorts.single()
                check(arg.isBitVecSort())
                val width = arg.getBitVecSortWidth()
                check(width > 0)
                return SignExtend(this.i, arg, Sort.bitVecSort(width + i))
            }

            override fun instantiateResultSort(resultSort: Sort) = this

            companion object {
                const val fsIdName = "sign_extend"
            }
        }

        /**
         * Represents the SMT-LIB zero_extend operator. Note that i >= 0.
         * The parameter type is left as a parameter and instantiated on demand.
         */
        data class ZeroExtend(val i: Int, val X: Sort = Sort.Param("X"), val Y: Sort = Sort.Param(">")) : BV(
            Identifier.Indexed(fsIdName, listOf("$i")), Rank(X, Y)
        ) {
            init {
                check(i >= 0) { "ZeroExtend($i) does not satisfy SMT-LIB definition" }
            }

            override fun instantiateParamSorts(paramSorts: List<Sort>): SmtIntpFunctionSymbol {
                check(paramSorts.size == 1)
                val arg = paramSorts.single()
                check(arg.isBitVecSort())
                val width = arg.getBitVecSortWidth()
                check(width > 0)
                return ZeroExtend(this.i, arg, Sort.bitVecSort(width + i))
            }

            override fun instantiateResultSort(resultSort: Sort) = this

            companion object {
                const val fsIdName = "zero_extend"
            }
        }

        sealed class Un(override val name: Identifier, open val m: Int) :
            BV(name, Rank(Sort.bitVecSort(m), Sort.bitVecSort(m))) {

            override fun instantiateParamSorts(paramSorts: List<Sort>): SmtIntpFunctionSymbol {
                check(paramSorts.size == 1)
                check(paramSorts[0].isBitVecSort())
                val width = paramSorts[0].getBitVecSortWidth()
                check(width > 0)
                return when (this) {
                    is BvNeg -> BvNeg(width)
                    is BvNot -> BvNot(width)
                }
            }

            override fun instantiateResultSort(resultSort: Sort): SmtFunctionSymbol =
                instantiateParamSorts(listOf(resultSort))

            /** bitwise not */
            data class BvNot(override val m: Int = DUMMY_BITWIDTH) : Un(Identifier.Simple(fsIdName), m) {
                companion object {
                    const val fsIdName = "bvnot"
                }
            }

            /** negation in two's complement */
            data class BvNeg(override val m: Int = DUMMY_BITWIDTH) : Un(Identifier.Simple(fsIdName), m) {
                companion object {
                    const val fsIdName = "bvneg"
                }
            }

            companion object {
                fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? = (id as? Identifier.Simple)?.let {
                    when (it.sym) {
                        BvNot.fsIdName -> BvNot()
                        BvNeg.fsIdName -> BvNeg()
                        else -> null
                    }
                }
            }
        }

        sealed class BinOp(override val name: Identifier, m: Int) :
            BV(name, Rank(Sort.bitVecSort(m), Sort.bitVecSort(m), Sort.bitVecSort(m))) {
            abstract val m: Int

            override fun instantiateParamSorts(paramSorts: List<Sort>): SmtIntpFunctionSymbol {
                check(paramSorts.size == 2)
                check(paramSorts[0].isBitVecSort() && paramSorts[1].isBitVecSort())
                check(paramSorts[0].getBitVecSortWidth() == paramSorts[1].getBitVecSortWidth())
                val width = paramSorts[0].getBitVecSortWidth()
                check(width > 0)
                return when (this) {
                    is BvAnd -> BvAnd(width)
                    is BvOr -> BvOr(width)
                    is BvNAnd -> BvNAnd(width)
                    is BvNOr -> BvNOr(width)
                    is BvXNOr -> BvXNOr(width)
                    is BvXOr -> BvXOr(width)
                    is BvAdd -> BvAdd(width)
                    is BvSub -> BvSub(width)
                    is BvMul -> BvMul(width)
                    is BvUDiv -> BvUDiv(width)
                    is BvSDiv -> BvSDiv(width)
                    is BvURem -> BvURem(width)
                    is BvSRem -> BvSRem(width)
                    is BvShL -> BvShL(width)
                    is BvLShr -> BvLShr(width)
                    is BvAShr -> BvAShr(width)
                    is Z3Specific.BvUDivI -> Z3Specific.BvUDivI(width)
                }
            }

            override fun instantiateResultSort(resultSort: Sort): SmtFunctionSymbol =
                instantiateParamSorts(listOf(resultSort, resultSort))

            data class BvAnd(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvand"
                }
            }

            data class BvOr(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvor"
                }
            }

            data class BvNOr(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvnor"
                }
            }

            data class BvXNOr(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvxnor"
                }
            }

            data class BvXOr(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvxor"
                }
            }

            data class BvNAnd(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvnand"
                }
            }

            data class BvAdd(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvadd"
                }
            }

            data class BvSub(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvsub"
                }
            }

            data class BvMul(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvmul"
                }
            }

            data class BvUDiv(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvudiv"
                }
            }

            data class BvSDiv(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvsdiv"
                }
            }


            data class BvURem(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvurem"
                }
            }

            data class BvSRem(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvsrem"
                }
            }

            data class BvShL(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvshl"
                }
            }

            data class BvLShr(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvlshr"
                }
            }

            data class BvAShr(override val m: Int = DUMMY_BITWIDTH) : BinOp(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvashr"
                }
            }

            companion object {
                fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? = (id as? Identifier.Simple)?.let {
                    when (it.sym) {
                        BvAnd.fsName -> BvAnd()
                        BvOr.fsName -> BvOr()
                        BvNOr.fsName -> BvNOr()
                        BvXNOr.fsName -> BvXNOr()
                        BvXOr.fsName -> BvXOr()
                        BvNAnd.fsName -> BvNAnd()
                        BvAdd.fsName -> BvAdd()
                        BvSub.fsName -> BvSub()
                        BvMul.fsName -> BvMul()
                        BvUDiv.fsName -> BvUDiv()
                        BvSDiv.fsName -> BvSDiv()
                        BvURem.fsName -> BvURem()
                        BvSRem.fsName -> BvSRem()
                        BvShL.fsName -> BvShL()
                        BvLShr.fsName -> BvLShr()
                        BvAShr.fsName -> BvAShr()
                        else -> null
                    }
                } ?: Z3Specific.fromIdentifier(id)
            }

            /**
             * Function symbols that z3 uses internally, and sometimes also outputs, e.g. in CNF conversion.
             * See [https://github.com/Z3Prover/z3/issues/1132]
             */
            sealed class Z3Specific(name: Identifier, m: Int, val smtLibEquivalent: SmtIntpFunctionSymbol?) :
                BinOp(name, m) {

                data class BvUDivI(override val m: Int = DUMMY_BITWIDTH) : Z3Specific(
                    Identifier.Simple(fsName), m, BvUDiv(m)
                ) {
                    companion object {
                        const val fsName = "bvudiv_i"
                    }
                }

                companion object {
                    fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? = (id as? Identifier.Simple)?.let {
                        when (it.sym) {
                            BvUDivI.fsName -> BvUDivI()
                            else -> null
                        }
                    }
                }
            }
        }

        sealed class Rel(override val name: Identifier, open val m: Int) :
            BV(name, Rank(Sort.bitVecSort(m), Sort.bitVecSort(m), Sort.BoolSort)) {

            override fun instantiateParamSorts(paramSorts: List<Sort>): SmtIntpFunctionSymbol {
                check(paramSorts.size == 2)
                check(paramSorts[0].isBitVecSort() && paramSorts[1].isBitVecSort())
                check(paramSorts[0].getBitVecSortWidth() == paramSorts[1].getBitVecSortWidth())
                val width = paramSorts[0].getBitVecSortWidth()
                check(width > 0)
                // a copy method would make this much nicer .. but it would have about the same shape ..
                return when (this) {
                    is BvULt -> BvULt(width)
                    is BvULe -> BvULe(width)
                    is BvUGt -> BvUGt(width)
                    is BvUGe -> BvUGe(width)

                    is BvSLt -> BvSLt(width)
                    is BvSLe -> BvSLe(width)
                    is BvSGt -> BvSGt(width)
                    is BvSGe -> BvSGe(width)

                    is BvSAddO -> BvSAddO(width)
                    is BvUAddO -> BvUAddO(width)
                    is BvSMulO -> BvSMulO(width)
                    is BvUMulO -> BvUMulO(width)
                    is BvSSubO -> BvSSubO(width)
                    is BvUSubO -> BvUSubO(width)
                    is BvSDivO -> BvSDivO(width)

                    is Z3Specific.BvSMulNoOfl -> Z3Specific.BvSMulNoOfl(width)
                    is Z3Specific.BvSMulNoUdfl -> Z3Specific.BvSMulNoUdfl(width)
                    is Z3Specific.BvUMulNoOfl -> Z3Specific.BvUMulNoOfl(width)
                }
            }

            override fun instantiateResultSort(resultSort: Sort): SmtFunctionSymbol {
                check(resultSort == Sort.BoolSort)
                return this
            }

            data class BvULt(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvult"
                }
            }

            data class BvULe(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvule"
                }
            }

            data class BvUGt(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvugt"
                }
            }


            data class BvUGe(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvuge"
                }
            }


            data class BvSLt(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvslt"
                }
            }

            data class BvSLe(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvsle"
                }
            }

            data class BvSGt(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvsgt"
                }
            }


            data class BvSGe(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvsge"
                }
            }

            /* "may over-/underflow" functions; only the add and mul versions are on
             * https://smt-lib.org/theories-FixedSizeBitVectors.shtml, however it seems that the solvers that support
             * those also support the Sub snd Div variants (z3, bitwuzla, cvc5, as of Oct 2024)
             *
             * Note that we do our own modeling of Add, Sub, Neg overflows -- those cases are not complex to check
             * within regular BV. We're having them here for completeness, they might be useful if we ever need to parse
             * smtlib files that contain them.
             */

            data class BvUAddO(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvuaddo"
                }
            }

            data class BvSAddO(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvsaddo"
                }
            }


            data class BvUMulO(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvumulo"
                }
            }

            data class BvSMulO(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvsmulo"
                }
            }

            data class BvUSubO(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvusubo"
                }
            }

            data class BvSSubO(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvssubo"
                }
            }

            data class BvSDivO(override val m: Int = DUMMY_BITWIDTH) : Rel(Identifier.Simple(fsName), m) {
                companion object {
                    const val fsName = "bvsdivo"
                }
            }


            /**
             * Function symbols that z3 uses internally, and sometimes also outputs, e.g. in CNF conversion.
             * See [https://github.com/Z3Prover/z3/issues/1132]
             * (i.e. we keep these around just in case we need to parse z3 output at some later point)
             */
            sealed class Z3Specific(name: Identifier, m: Int) : Rel(name, m) {

                data class BvUMulNoOfl(override val m: Int = DUMMY_BITWIDTH) :
                    Z3Specific(Identifier.Simple(fsName), m) {
                    companion object {
                        const val fsName = "bvumul_noovfl"
                    }
                }

                data class BvSMulNoOfl(override val m: Int = DUMMY_BITWIDTH) :
                    Z3Specific(Identifier.Simple(fsName), m) {

                    companion object {
                        const val fsName = "bvsmul_noovfl"
                    }
                }

                data class BvSMulNoUdfl(override val m: Int = DUMMY_BITWIDTH) :
                    Z3Specific(Identifier.Simple(fsName), m) {
                    companion object {
                        const val fsName = "bvsmul_noudfl"
                    }
                }
            }

            companion object {

                fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? = (id as? Identifier.Simple)?.let {
                    when (it.sym) {
                        BvULt.fsName -> BvULt()
                        BvULe.fsName -> BvULe()
                        BvUGt.fsName -> BvUGt()
                        BvUGe.fsName -> BvUGe()

                        BvSLt.fsName -> BvSLt()
                        BvSLe.fsName -> BvSLe()
                        BvSGt.fsName -> BvSGt()
                        BvSGe.fsName -> BvSGe()

                        BvUAddO.fsName -> BvUAddO()
                        BvSAddO.fsName -> BvSAddO()
                        BvUMulO.fsName -> BvUMulO()
                        BvSMulO.fsName -> BvSMulO()
                        BvUSubO.fsName -> BvUSubO()
                        BvSSubO.fsName -> BvSSubO()
                        BvSDivO.fsName -> BvSDivO()


                        Z3Specific.BvUMulNoOfl.fsName -> Z3Specific.BvUMulNoOfl()
                        Z3Specific.BvSMulNoOfl.fsName -> Z3Specific.BvSMulNoOfl()
                        Z3Specific.BvSMulNoUdfl.fsName -> Z3Specific.BvSMulNoUdfl()

                        else -> null
                    }
                }
            }
        }

        companion object {
            fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? =
                Extract.fromIdentifier(id) ?: Concat.fromIdentifier(id) ?: Un.fromIdentifier(id)
                ?: BinOp.fromIdentifier(id) ?: Rel.fromIdentifier(id)


        }
    }

    sealed class Core(
        override val name: Identifier, override val rank: Rank
    ) : SmtIntpFunctionSymbol(name, rank) {
        constructor(name: String, rank: Rank) : this(
            Identifier.Simple(name), rank
        )

        object True : Core("true", Rank(Sort.BoolSort)) {
            private fun readResolve(): Any = True
            override fun hashCode(): Int = utils.hashObject(this)
        }

        object False : Core("false", Rank(Sort.BoolSort)) {
            private fun readResolve(): Any = False
            override fun hashCode(): Int = utils.hashObject(this)
        }

        object LNot : Core("not", Rank(Sort.BoolSort, Sort.BoolSort)) {
            private fun readResolve(): Any = LNot
            override fun hashCode(): Int = utils.hashObject(this)
        }

        object LImplies : Core("=>", Rank(Sort.BoolSort, Sort.BoolSort, Sort.BoolSort)) {
            private fun readResolve(): Any = LImplies
            override fun hashCode(): Int = utils.hashObject(this)
        }

        object LAnd : Core("and", Rank(Sort.BoolSort, Sort.BoolSort, Sort.BoolSort)) {
            private fun readResolve(): Any = LAnd
            override fun hashCode(): Int = utils.hashObject(this)
        }

        object LOr : Core("or", Rank(Sort.BoolSort, Sort.BoolSort, Sort.BoolSort)) {
            private fun readResolve(): Any = LOr
            override fun hashCode(): Int = utils.hashObject(this)
        }

        object LXor : Core("xor", Rank(Sort.BoolSort, Sort.BoolSort, Sort.BoolSort)) {
            private fun readResolve(): Any = LXor
            override fun hashCode(): Int = utils.hashObject(this)
        }


        data class Eq(val A: Sort = defaultSortParamA) : Core(
            fsName, Rank(A, A, Sort.BoolSort)
        ) {
            companion object {
                const val fsName = "="
            }
        }

        data class Distinct(val A: Sort = defaultSortParamA) : Core(
            fsName, Rank(A, A, Sort.BoolSort)
        ) {
            companion object {
                const val fsName = "distinct"
            }
        }

        data class Ite(val A: Sort = defaultSortParamA) : Core(fsName, Rank(Sort.BoolSort, A, A, A)) {
            companion object {
                const val fsName = "ite"
            }
        }

        override fun instantiateParamSorts(paramSorts: List<Sort>): SmtIntpFunctionSymbol = when (this) {
            True, False -> {
                check(paramSorts.isEmpty())
                this
            }

            LNot -> {
                check(paramSorts.size == 1)
                check(paramSorts[0] == Sort.BoolSort)
                this
            }

            LImplies, LAnd, LOr, LXor -> {
                check(paramSorts.size >= 2) // TODO: maybe have a non-strict mode?
                check(paramSorts.all { it == paramSorts[0] && it == Sort.BoolSort })
                this
            }

            is Eq, is Distinct -> {
                check(paramSorts.size >= 2) { "equals function needs two or more arguments" }
                check(paramSorts.all { it == paramSorts[0] }) { "all arguments to the equals function need to be of the same sort" }
                val sort = paramSorts[0]
                when (this) {
                    is Eq -> Eq(sort)
                    is Distinct -> Distinct(sort)
                    else -> error { "?" }
                }
            }

            is Ite -> {
                check(paramSorts.size == 3)
                check(paramSorts[0] == Sort.BoolSort)
                check(paramSorts[1] == paramSorts[2])
                Ite(paramSorts[1])
            }
        }

        override fun instantiateResultSort(resultSort: Sort): SmtIntpFunctionSymbol = when (this) {
            is Ite -> Ite(resultSort)
            else -> {
                check(resultSort == Sort.BoolSort)
                this
            }
        }

        companion object {
            fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? = (id as? Identifier.Simple)?.let {
                when (it.sym) {
                    True.toSMTLIBString() -> True
                    False.toSMTLIBString() -> False
                    LNot.toSMTLIBString() -> LNot
                    LImplies.toSMTLIBString() -> LImplies
                    LOr.toSMTLIBString() -> LOr
                    LXor.toSMTLIBString() -> LXor
                    LAnd.toSMTLIBString() -> LAnd
                    Eq.fsName -> Eq()
                    Distinct.fsName -> Distinct()
                    Ite.fsName -> Ite()
                    else -> null
                }
            }
        }
    }

    sealed class DT(
        override val name: Identifier, override val rank: Rank
    ) : SmtIntpFunctionSymbol(name, rank) {

        data class Is(val A: Sort = defaultSortParamA, val subType: String) :
            DT(Identifier.Indexed(fsName, listOf(subType)), Rank(A, Sort.BoolSort)) {

            override fun toSMTLIBString(): String = "(_ $fsName $subType)"

            companion object {
                const val fsName = "is"
            }
        }

        override fun instantiateParamSorts(paramSorts: List<Sort>): SmtFunctionSymbol {
            return when (this) {
                is Is -> {
                    check(paramSorts.size == 1)
                    // TODO (potential): check that paramSort[0] matches the result type of the data type constructor
                    //    [subtype]
                    Is(A = paramSorts.first(), this.subType)
                }
            }
        }

        companion object {
            fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? = (id as? Identifier.Indexed)?.let {
                when (it.sym) {
                    Is.fsName -> {
                        check(id.indices.size == 1) { "wrong number of indices for \"is\"" }
                        Is(subType = id.indices.first())
                    }

                    else -> null
                }
            }

        }
    }


    sealed class IRA(
        override val name: Identifier, override val rank: Rank
    ) : SmtIntpFunctionSymbol(name, rank) {
        constructor(name: String, rank: Rank) : this(
            Identifier.Simple(name), rank
        )

        protected fun Sort.checkSortIsIRA() = also {
            check(this == defaultSortParamN || this == Sort.RealSort || this == Sort.IntSort || this is Sort.Param) {
                "IRA symbols can only be instantiated with sorts Int or Real (but got $this)."
            }
        }

        /** an easy way to see whether an IRA - function symbol was instantiated (to Int or Real) already, null means
         * "unknown" */
        abstract val intOrRealParamSort: Sort?

        /** integer negation/unary minus */
        data class Neg(val N: Sort = defaultSortParamN) : IRA(fsName, Rank(N, N)) {
            init {
                N.checkSortIsIRA()
            }

            override val intOrRealParamSort: Sort get() = N

            companion object {
                const val fsName = "-"
            }
        }

        data class Sub(val N: Sort = defaultSortParamN) : IRA(fsName, Rank(N, N, N)) {
            init {
                N.checkSortIsIRA()
            }

            override val intOrRealParamSort: Sort get() = N

            companion object {
                const val fsName = "-"
            }
        }

        data class Add(val N: Sort = defaultSortParamN) : IRA(fsName, Rank(N, N, N)) {
            init {
                N.checkSortIsIRA()
            }

            override val intOrRealParamSort: Sort get() = N

            companion object {
                const val fsName = "+"
            }
        }

        data class Mul(val N: Sort = defaultSortParamN) : IRA(fsName, Rank(N, N, N)) {
            init {
                N.checkSortIsIRA()
            }

            override val intOrRealParamSort: Sort get() = N

            companion object {
                const val fsName = "*"
            }
        }

        data class Le(val N: Sort = defaultSortParamN) : IRA(fsName, Rank(N, N, Sort.BoolSort)) {
            init {
                N.checkSortIsIRA()
            }

            override val intOrRealParamSort: Sort get() = N

            companion object {
                const val fsName = "<="
            }
        }

        data class Lt(val N: Sort = defaultSortParamN) : IRA(fsName, Rank(N, N, Sort.BoolSort)) {
            init {
                N.checkSortIsIRA()
            }

            override val intOrRealParamSort: Sort get() = N

            companion object {
                const val fsName = "<"
            }
        }

        data class Ge(val N: Sort = defaultSortParamN) : IRA(fsName, Rank(N, N, Sort.BoolSort)) {
            init {
                N.checkSortIsIRA()
            }

            override val intOrRealParamSort: Sort get() = N

            companion object {
                const val fsName = ">="
            }
        }

        data class Gt(val N: Sort = defaultSortParamN) : IRA(fsName, Rank(N, N, Sort.BoolSort)) {
            init {
                N.checkSortIsIRA()
            }

            override val intOrRealParamSort: Sort get() = N

            companion object {
                const val fsName = ">"
            }
        }

        override fun instantiateParamSorts(paramSorts: List<Sort>): IRA = when (this) {
            is Neg -> {
                check(paramSorts.size == 1)
                val numberSort = paramSorts.first()
                check(paramSorts.all { it == numberSort })
                check(numberSort == Sort.IntSort || numberSort == Sort.RealSort)
                Neg(numberSort)
            }

            is Sub -> {
                check(paramSorts.isNotEmpty())
                val numberSort = paramSorts.first()
                check(paramSorts.all { it == numberSort })
                check(numberSort == Sort.IntSort || numberSort == Sort.RealSort)
                when (paramSorts.size) {
                    1 -> Neg(numberSort)
                    /** also see [Companion.fromIdentifier] */
                    else -> Sub(numberSort)
                }
            }

            is Add, is Mul, is Le, is Lt, is Ge, is Gt -> {
                check(paramSorts.size >= 2)
                val numberSort = paramSorts.first()
                check(paramSorts.all { it == numberSort }) { "Failed to sort function symbol $this: not all arguments have the same sort (argument sorts: $paramSorts)." }
                check(numberSort == Sort.IntSort || numberSort == Sort.RealSort) {
                    "Failed to sort function symbol $this: arguments are only allowed to be of sorts Int or Real " + "(argument sorts: $paramSorts)."
                }
                when (this) {
                    is Add -> Add(numberSort)
                    is Mul -> Mul(numberSort)
                    is Le -> Le(numberSort)
                    is Lt -> Lt(numberSort)
                    is Ge -> Ge(numberSort)
                    is Gt -> Gt(numberSort)
                    else -> error("shouldn't be reachable")
                }
            }

            IsInt -> this
            ToInt -> this
            ToReal -> this
        }

        object ToReal : IRA("to_real", Rank(Sort.IntSort, Sort.RealSort)) {
            private fun readResolve(): Any = ToReal
            override fun hashCode(): Int = utils.hashObject(this)
            override val intOrRealParamSort: Sort
                get() = error("this method (intOrRealParamSort) does not apply here ($name)")
        }

        /** SmtLib: "By definition of to_int, (to_int (- 1.3)) is equivalent to (- 2), not (- 1)." */
        object ToInt : IRA("to_int", Rank(Sort.RealSort, Sort.IntSort)) {
            private fun readResolve(): Any = ToInt
            override fun hashCode(): Int = utils.hashObject(this)
            override val intOrRealParamSort: Sort
                get() = error("this method (intOrRealParamSort) does not apply here ($name)")
        }

        /** SmtLib: "is_int as the function that maps to true all and only the reals in the image of to_real" */
        object IsInt : IRA("is_int", Rank(Sort.RealSort, Sort.BoolSort)) {
            private fun readResolve(): Any = IsInt
            override fun hashCode(): Int = utils.hashObject(this)
            override val intOrRealParamSort: Sort
                get() = error("this method (intOrRealParamSort) does not apply here ($name)")
        }

        companion object {
            /**  note that [name] = "-" is somewhat of a special case, since [Neg] and [Sub] share that name;
             *  we always build a [Sub] here and replace with Neg with it in instantiateRank! */
            fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? = (id as? Identifier.Simple)?.let {
                when (it.sym) {
                    Sub.fsName -> Sub()
                    Add.fsName -> Add()
                    Mul.fsName -> Mul()
                    Le.fsName -> Le()
                    Lt.fsName -> Lt()
                    Ge.fsName -> Ge()
                    Gt.fsName -> Gt()
                    ToReal.toSMTLIBString() -> ToReal
                    ToInt.toSMTLIBString() -> ToInt
                    IsInt.toSMTLIBString() -> IsInt
                    else -> null
                }
            }
        }
    }

    sealed class Reals(
        override val name: Identifier, override val rank: Rank
    ) : SmtIntpFunctionSymbol(name, rank) {
        constructor(name: String, rank: Rank) : this(
            Identifier.Simple(name), rank
        )

        object Div : Reals("/", Rank(Sort.RealSort, Sort.RealSort, Sort.RealSort)) {
            private fun readResolve(): Any = Div
            override fun hashCode(): Int = utils.hashObject(this)
        }

        override fun instantiateParamSorts(paramSorts: List<Sort>): Reals = when (this) {
            Div -> {
                check(paramSorts.all { it == Sort.RealSort })
                check(paramSorts.size >= 2)
                this
            }
        }

        companion object {
            fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? = (id as? Identifier.Simple)?.let {
                when (it.sym) {
                    Div.toSMTLIBString() -> Div
                    else -> null
                }
            }
        }
    }

    sealed class Ints(
        override val name: Identifier,
        override val rank: Rank,
    ) : SmtIntpFunctionSymbol(name, rank) {
        constructor(name: String, rank: Rank) : this(
            Identifier.Simple(name), rank
        )

        object Div : Ints("div", Rank(Sort.IntSort, Sort.IntSort, Sort.IntSort)) {
            private fun readResolve(): Any = Div
            override fun hashCode(): Int = utils.hashObject(this)
        }

        object Mod : Ints("mod", Rank(Sort.IntSort, Sort.IntSort, Sort.IntSort)) {
            private fun readResolve(): Any = Mod
            override fun hashCode(): Int = utils.hashObject(this)
        }

        object Abs : Ints("abs", Rank(Sort.IntSort, Sort.IntSort)) {
            private fun readResolve(): Any = Abs
            override fun hashCode(): Int = utils.hashObject(this)
        }

        override fun instantiateParamSorts(paramSorts: List<Sort>): Ints = when (this) {
            Div -> {
                check(paramSorts.all { it == Sort.IntSort })
                check(paramSorts.size >= 2)
                this
            }

            Mod, Abs -> {
                check(paramSorts.all { it == Sort.IntSort })
                check(paramSorts.size == 2)
                this
            }
        }

        companion object {
            fun fromIdentifier(id: Identifier): SmtIntpFunctionSymbol? = (id as? Identifier.Simple)?.let {
                when (it.sym) {
                    Div.toSMTLIBString() -> Div
                    Mod.toSMTLIBString() -> Mod
                    Abs.toSMTLIBString() -> Abs
                    else -> null
                }
            }
        }
    }

}
