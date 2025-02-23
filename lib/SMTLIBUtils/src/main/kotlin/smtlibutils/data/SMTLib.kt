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

import com.certora.collect.*
import datastructures.stdcollections.*
import evm.EVM_BITWIDTH256
import smtlibutils.algorithms.*
import smtlibutils.algorithms.IsSorted.Companion.isSorted
import smtlibutils.cmdprocessor.SmtFormula
import smtlibutils.data.SmtIntpFunctionSymbol.IRA
import smtlibutils.data.Sort.Companion.arraySort
import smtlibutils.parser.SMTParser
import smtlibutils.parser.SmtSymbolQuoter
import utils.*
import java.io.Serializable
import java.math.BigDecimal
import java.math.BigInteger
import java.util.*
import java.util.concurrent.ConcurrentHashMap
import kotlin.reflect.KClass

data class SMT(val cmds: List<Cmd>) {

    fun sort(smtScript: SmtScript = SmtScript()): SMT {
        val sorter = Sorter(smtScript)
        val sorted = sorter.smt(this)
        assert(isSorted(sorted)) { "must be sorted at this point, but is not" }
        return sorted
    }

    override fun toString(): String {
        return cmds.joinToString("\n")
    }

    fun toSmtFormula() = SmtFormula.fromSmt(this)
}

data class Stat(val statName: String, val value: String)

data class ValDef(val exp: SmtExp, val value: SmtExp) {
    override fun toString(): String {
        return "($exp $value)"
    }
}

data class SortDec(val name: String, val arity: Int) {
    override fun toString(): String {
        return "${SmtSymbolQuoter.quoteIfNecessary(name)} $arity"
    }
}

data class DatatypeConstructorDec(val name: String, val selectors: List<SortedVar>) {
    override fun toString(): String {
        return "(${SmtSymbolQuoter.quoteIfNecessary(name)} ${selectors.joinToString(" ")})"
    }
}

data class VarBinding(val id: String, val def: SmtExp) {
    override fun toString(): String = "($id $def)"
}

data class SortedVar(val id: String, val sort: Sort) {
    fun toQualId(script: ISmtScript = FactorySmtScript) =
        script.qualIdentifier(script.simpleIdentifier(id), null, sort)

    override fun toString(): String = "($id $sort)"
}

@Treapable
sealed class Identifier: Serializable {
    abstract val sym: String

    data class Simple(override val sym: String) : Identifier() {
        override fun toString(): String = SmtSymbolQuoter.quoteIfNecessary(sym)
    }

    data class Indexed(override val sym: String, val indices: List<String>) : Identifier() {
        override fun toString(): String {
            return "(_ ${SmtSymbolQuoter.quoteIfNecessary(sym)} ${indices.joinToString(" ")})"
        }
    }
}

interface HasSmtExp {
    val exp: SmtExp
    fun mapExp(mapper: (SmtExp) -> SmtExp): HasSmtExp
}

/**
 * .. might even attach a meta map or something?..
 */
open class SmtExpWithComment(override val exp: SmtExp, val comment: String?) : HasSmtExp {
    override fun mapExp(mapper: (SmtExp) -> SmtExp): HasSmtExp = SmtExpWithComment(mapper(exp), comment)
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as SmtExpWithComment

        if (exp != other.exp) return false
        if (comment != other.comment) return false

        return true
    }

    override fun hashCode(): Int {
        var result = exp.hashCode()
        result = 31 * result + (comment?.hashCode() ?: 0)
        return result
    }

    override fun toString(): String = if (comment == null) { "$exp"  } else { "$exp ; $comment" }
}


sealed class SmtExp : HasSmtExp, SExp<SmtExp, SmtFunctionSymbol>, Serializable {

    /* for HasSmtExp interface */
    override val exp: SmtExp
        get() = this

    override fun mapExp(mapper: (SmtExp) -> SmtExp): HasSmtExp = mapper(this)

    abstract val sort: Sort?

    companion object {
        fun fromString(
            expString: String,
            script: ISmtScript,
            smtSymbolTable: SmtSymbolTable
        ): SmtExp = fromString(expString, script, Sorter.TypeScope.getEmpty(smtSymbolTable))

        fun fromString(
            expString: String,
            smtScript: ISmtScript,
            symbolTable: Sorter.TypeScope
        ): SmtExp {
            // parser needs the symbol table for the function symbols here
            val exp = SMTParser.parseExp(expString, smtScript.withSymbolTable(symbolTable.symbolTable))
            return Sorter(smtScript, symbolTable.symbolTable).sort(exp, symbolTable)
        }
    }

    class Unification(script: ISmtScript) : AbstractUnification<SmtExp, SmtFunctionSymbol>(
        applyExp = script::apply,
        auxTupleConstr = { SmtFunctionSymbol.fromIdentifier(script.simpleIdentifier("certora_aux_tuple")) }
    )

    /** Is a Boolean literal like `(not A)`, `B`, or `true`. */
    fun isBooleanLiteral() =
        this.isAtom() ||
                this.isApp(SmtIntpFunctionSymbol.Core.LNot::class) && (this as Apply).args[0].isAtom()

    fun isAtom(): Boolean = when (this) {
        is QualIdentifier -> this.sort == Sort.BoolSort
        is Apply -> this.fs.isBoolAtomWhenApplied()
        is BoolLiteral -> true
        is Let -> this.unlet().isAtom()
        is Lambda -> throw UnsupportedOperationException("case not implemented (this = $this)")
        else -> false
    }

    fun isBooleanConnective() = this is Apply && this.fs.isBooleanConnective()

    /** checks if the "this" is an application of function symbol [fs] */
    fun isApp(fs: KClass<out SmtFunctionSymbol>) = when (this) {
        is Apply -> fs.isInstance(this.fs)
        else -> false
    }

    fun isConstantArray(): Boolean = this.isApp(SmtIntpFunctionSymbol.Array.Const::class)

    /** Checks if this is a value literal like `1`, `true`, `(_ bv32 Bit4)`, `((as const (Array Int Int)) 13)`.
     * (not to be confused with a boolean literal; that's checked by [isBooleanValueLit] */
    fun isValueLiteral(symbolTable: SmtSymbolTable? = null): Boolean =
        this.isBooleanValueLit() ||
                this.isIntLiteral() ||
                this.isDecLiteral() ||
                this.isFractionLiteral() || // some solvers give fractions in models
                this.isBitVectorLiteral() ||
                this.isConstantArray() ||
                this.isDatatypeLiteral(symbolTable) ||
                this.isMapDefinitionLiteral(symbolTable)

    /**
     * Returns true if this is a definitions of a map that we can recognize as such. Since the format of these maps
     * differs from solver to solver, this method will have to grow on demand as we see more complex models being
     * returned from our solvers.
     *
     * Examples of formats:
     *  - z3 likes to return models of the form `(store ((as const Array) 0) 1 2)`
     *  - cvc5 (prob. also cvc4) likes to return models of the form `(lambda (boundVar) (ite (= boundVar 1) 2 0))`
     * */
    fun isMapDefinitionLiteral(symbolTable: SmtSymbolTable?): Boolean {
        return when (this) {
            is Apply -> when (fs) {
                is SmtIntpFunctionSymbol.Array.Store ->
                    args[0].isMapDefinitionLiteral(symbolTable) &&
                        args[1].isValueLiteral(symbolTable) &&
                        args[2].isValueLiteral(symbolTable)
                is SmtIntpFunctionSymbol.Array.Const ->
                    args[0].isValueLiteral(symbolTable)
                else -> false
            }

            is Lambda ->
                true

            else -> false
        }
    }

    /** true iff this expression is only made up of data type constructors (declared in [symbolTable]) and other value
     * literals */
    fun isDatatypeLiteral(symbolTable: SmtSymbolTable?): Boolean =
        symbolTable != null &&
                ((this is Apply &&
                        symbolTable.isDatatypeConstructor(this.fs) &&
                        this.args.all { it.isValueLiteral(symbolTable) }) ||
                        this is QualIdentifier && symbolTable.isDatatypeConstructor(this.id))


    /** Added just for uniformity. */
    fun isBitVectorLiteral(): Boolean = this is BitvectorLiteral

    /**
     * E.g 1 counts as an integer literal, and also (- 1).
     */
    fun isIntLiteral() = asBigIntOrNull() != null

    /**
     * E.g 1.0 counts as a decimal literal, and also (- 1.0).
     */
    fun isDecLiteral(): Boolean = when (this) {
        is DecLiteral -> true
        is Apply.Unary -> {
            // bit hacky but Sub may be used unary when expression hasn't been sorted, yet
            (fs is IRA.Neg || fs is IRA.Sub) && args.single().isDecLiteral()
        }
        else -> false
    }

    fun isFractionLiteral(): Boolean = when (this) {
        is Apply ->
            if (args.size == 1) {
                // bit hacky but Sub may be used unary when expression hasn't been sorted, yet
                (fs is IRA.Neg || fs is IRA.Sub) && args[0].isFractionLiteral()
            } else if (args.size == 2 && fs == SmtIntpFunctionSymbol.Reals.Div) {
                // z3 does this, I think -- although it's not well-sorted, strictly speaking..
                (args[0].isIntLiteral() && args[1].isIntLiteral()) || (args[0].isDecLiteral() && args[1].isDecLiteral())
            } else {
                false
            }
        else -> false
    }

    fun asBigIntOrNull(): BigInteger? =
        when (this) {
            is IntLiteral -> this.i
            is BitvectorLiteral -> this.n
            is Apply.Unary -> {
                val negatedLiteral = args.single().takeIf { fs is IRA.Neg || fs is IRA.Sub }

                negatedLiteral?.asBigIntOrNull()?.negate()
            }
            else -> null
        }

    fun asBigInt(): BigInteger =
        asBigIntOrNull() ?: throw UnsupportedOperationException("$this should be an int or bitvector literal")

    /** Has a constant Boolean value, i.e., is `true` or `false`. As opposed to Boolean literals like `(not A)`. */
    fun isBooleanValueLit(): Boolean = when (this) {
        BoolLiteral.True -> true
        BoolLiteral.False -> true
        else -> false
    }

    fun asBoolean(): Boolean = when (this) {
        BoolLiteral.True -> true
        BoolLiteral.False -> false
        else -> error("this may only be called on BoolLiteral expressions")
    }

    data class QualIdentifier(val id: Identifier, val qualification: Sort?, override val sort: Sort? = null) :
        SmtExp(), SExpSym<SmtExp, SmtFunctionSymbol> {
        override fun toString(): String = if (qualification == null) "$id" else "(as $id $qualification)"

        companion object {
            fun simpleFromString(name: String, sort: Sort?, script: ISmtScript) {
                script.qualIdentifier(script.simpleIdentifier(name), null, sort)
            }
        }
    }

    sealed class Apply constructor(final override val fs: SmtFunctionSymbol, override val sort: Sort? = null)
        : SmtExp(), SExpApply<SmtExp, SmtFunctionSymbol> {
        abstract override val args: List<SmtExp>

        /** a nullary function is a constant */
        val isConstant get() = args.isEmpty()

        class Nullary(fs: SmtFunctionSymbol, sort: Sort? = null) : Apply(fs, sort) {
            override val args: List<SmtExp>
                get() = listOf()
        }

        class Unary(fs: SmtFunctionSymbol, private val arg1: SmtExp, sort: Sort? = null) : Apply(fs, sort) {
            override val args: List<SmtExp>
                get() = listOf(arg1)

            override fun equals(other: Any?): Boolean {
                return other is Unary && other.fs == this.fs && other.sort == this.sort && other.arg1 == this.arg1
            }

            override fun hashCode(): Int {
                return Objects.hash(
                    fs, sort, arg1
                )
            }
        }

        class Binary(fs: SmtFunctionSymbol, private val arg1: SmtExp, private val arg2: SmtExp, sort: Sort? = null) :
            Apply(fs, sort) {
            override val args: List<SmtExp>
                get() = listOf(arg1, arg2)

            override fun equals(other: Any?): Boolean {
                return other is Binary && other.fs == this.fs && other.sort == this.sort && other.arg1 == this.arg1 && other.arg2 == this.arg2
            }

            override fun hashCode(): Int {
                return Objects.hash(
                    fs, sort, arg1, arg2
                )
            }
        }

        class Ternary(
            fs: SmtFunctionSymbol,
            private val arg1: SmtExp,
            private val arg2: SmtExp,
            private val arg3: SmtExp,
            sort: Sort? = null
        ) : Apply(fs, sort) {
            override val args: List<SmtExp>
                get() = listOf(arg1, arg2, arg3)

            override fun equals(other: Any?): Boolean {
                return other is Ternary && other.fs == this.fs && other.sort == this.sort && other.arg1 == this.arg1 && other.arg2 == this.arg2 && other.arg3 == this.arg3
            }

            override fun hashCode(): Int {
                return Objects.hash(
                    fs, sort, arg1, arg2, arg3
                )
            }
        }

        class Quaternary(
            fs: SmtFunctionSymbol,
            private val arg1: SmtExp,
            private val arg2: SmtExp,
            private val arg3: SmtExp,
            private val arg4: SmtExp,
            sort: Sort? = null
        ) : Apply(fs, sort) {
            override val args: List<SmtExp>
                get() = listOf(arg1, arg2, arg3, arg4)

            override fun equals(other: Any?): Boolean {
                return other is Quaternary && other.fs == this.fs && other.sort == this.sort && other.arg1 == this.arg1 && other.arg2 == this.arg2 && other.arg3 == this.arg3 && other.arg4 == this.arg4
            }

            override fun hashCode(): Int {
                return Objects.hash(
                    fs, sort, arg1, arg2, arg3, arg4
                )
            }
        }

        class Nary(fs: SmtFunctionSymbol, override val args: List<SmtExp>, sort: Sort? = null) : Apply(fs, sort) {
            override fun equals(other: Any?): Boolean {
                return other is Nary && other.fs == this.fs && other.args == this.args
            }

            override fun hashCode(): Int {
                return Objects.hash(fs, args)
            }
        }

        override fun toString(): String =
            if (isConstant) {
                fs.toSMTLIBString()
            } else {
                "(${fs.toSMTLIBString()} ${args.joinToString(" ")})"
            }

        companion object {
            operator fun invoke(f: SmtFunctionSymbol, vararg args: SmtExp, sort: Sort? = null) =
                when (args.size) {
                    0 -> Nullary(f, sort)
                    1 -> Unary(f, args[0], sort)
                    2 -> Binary(f, args[0], args[1], sort)
                    3 -> Ternary(f, args[0], args[1], args[2], sort)
                    4 -> Quaternary(f, args[0], args[1], args[2], args[3], sort)
                    else -> Nary(f, args.toList(), sort)
                }

            operator fun invoke(f: SmtFunctionSymbol, args: List<SmtExp>, sort: Sort? = null): Apply {
                return when (args.size) {
                    0 -> Nullary(f, sort)
                    1 -> Unary(f, args[0], sort)
                    2 -> Binary(f, args[0], args[1], sort)
                    3 -> Ternary(f, args[0], args[1], args[2], sort)
                    4 -> Quaternary(f, args[0], args[1], args[2], args[3], sort)
                    else -> Nary(f, args, sort)
                }

            }
        }
    }

    data class Lambda(val args: List<SortedVar>, val e: SmtExp, override val sort: Sort? = null)
        : SmtExp(), SExpSym<SmtExp, SmtFunctionSymbol> {
        override fun toString(): String {
            return "(lambda (${args.joinToString(separator = " ")}) $e)"
        }
    }


    data class Let(val defs: List<VarBinding>, val body: SmtExp, override val sort: Sort? = null) : SmtExp() {
        override fun toString(): String = "(let (${defs.joinToString(" ")}) $body)"

        /** inlines the definitions of this [Let] into its [body] */
        fun unlet(): SmtExp {
            val subst =
                Substitutor(defs.map {
                    QualIdentifier(
                        Identifier.Simple(it.id),
                        null,
                        it.def.sort
                    ) to it.def
                }.toMap())
            return subst.expr(body, Unit)
        }
    }

    sealed class Quant : SmtExp() {
        abstract val boundVars: List<SortedVar>
        abstract val body: SmtExp

        override val sort: Sort
            get() = Sort.BoolSort

        abstract val quantString: String

        override fun toString(): String = "($quantString (${boundVars.joinToString(" ")}) $body)"

        protected fun checkBoundVars() {
            check(boundVars.isNotEmpty())
            { "Cannot create a quantified formula without bound variables. Quantifier: $quantString, body: $body" }
        }

        data class ForAll(override val boundVars: List<SortedVar>, override val body: SmtExp) : Quant() {
            init {
                checkBoundVars()
            }

            override val quantString: String = "forall"

            override fun toString(): String = super.toString()
        }

        data class Exists(override val boundVars: List<SortedVar>, override val body: SmtExp) : Quant() {
            init {
                checkBoundVars()
            }

            override val quantString: String = "exists"

            override fun toString(): String = super.toString()
        }
    }


    // constants
    data class BitvectorLiteral(val n: BigInteger, val width: Int) : SmtExp(), SExpSym<SmtExp, SmtFunctionSymbol> {
        override val sort: Sort? = Sort.bitVecSort(width)
        override fun toString(): String =
            "(_ bv${n.toString(10)} $width)"

        companion object {
            fun fromIndexedIdentifier(id: Identifier.Indexed, smtScript: ISmtScript, logic: Logic): BitvectorLiteral? {
                if (id.sym.startsWith("bv") &&
                    id.indices.size == 1 &&
                    logic.logicFeatures.contains(LogicFeature.BitVectors)
                ) {
                    try {
                        val bitWidth = Integer.parseUnsignedInt(id.indices.first())
                        val value = BigInteger(id.sym.substring(2), 10)
                        return smtScript.bitvector(value, bitWidth)
                    } catch (e: NumberFormatException) {
                        /* not a bv literal after all */
                    }
                }
                return null
            }
        }
    }

    data class BoolLiteral private constructor(val b: Boolean) : SmtExp(), SExpSym<SmtExp, SmtFunctionSymbol> {
        override val sort: Sort
            get() = Sort.BoolSort

        override fun toString(): String = "$b"

        companion object {
            val True = BoolLiteral(true)
            val False = BoolLiteral(false)
            operator fun invoke(b: Boolean) = if (b) True else False
        }
    }

    data class IntLiteral(val i: BigInteger) : SmtExp(), SExpSym<SmtExp, SmtFunctionSymbol> {
        override val sort: Sort
            get() = Sort.IntSort

        override fun toString(): String =
            if (i < BigInteger.ZERO) "(- ${i.abs().toString(10)})" else i.toString(10)
    }

    data class DecLiteral(val d: BigDecimal) : SmtExp(), SExpSym<SmtExp, SmtFunctionSymbol> {
        override val sort: Sort
            get() = Sort.RealSort

        override fun toString(): String =
            if (d < BigDecimal.ZERO) "(- ${d.abs()})" else d.toString()
    }

    data class AnnotatedExp(val innerExp: SmtExp, val annotation: SmtAnnotation) : SmtExp() {
        override val sort: Sort? = innerExp.sort
        override fun toString(): String = "(! $innerExp $annotation)"
    }

    /**
     * A placeholder in an [SmtExp].
     *
     * Note: This is just used for pattern matching purposes -- [QualIdentifier] already has the [SExpSym] role, so we
     *  need something else for the [SExpVar] role.
     *  So far I'm purposefully not adding it to the scripts, and the usual traversals/transformers will crash if they
     *  see it. If we want to use them with this class, this class could be treated like a variable I suppose.
     * */
    data class PlaceHolder(val name: String, override val sort: Sort?): SmtExp(), SExpVar<SmtExp, SmtFunctionSymbol>
}

/** View on an apply expression as a conjunction.
 * TODO: unclear how useful this is; how do I hide that constructor in an inline class??
 */
@JvmInline value class SmtConjunction(val conjunction: SmtExp.Apply) {
    val conjuncts: List<SmtExp>
        get() {
            check(conjunction.fs == SmtIntpFunctionSymbol.Core.LAnd) { "don't construct this from  non-conjunctions (use fromExpOrNull function)" }
            return conjunction.args
        }

    companion object {
        fun fromExpOrNull(exp: SmtExp): SmtConjunction? =
            if (exp is SmtExp.Apply && exp.fs == SmtIntpFunctionSymbol.Core.LAnd) SmtConjunction(exp)
            else null
    }
}

sealed class SmtAnnotation {
    data class NamedAnnotation(val name: String) : SmtAnnotation() {
        override fun toString(): String = ":named $name"
    }
    // add pattern annotation when we need it
}

/**
 * What SMTLib calls a rank more or less corresponds to what we call a function signature.
 *
 * SMTLib standard 2.6, 3.5.1: Each function symbol in an SMT-LIB script is associated with one or more ranks, non-empty
 * sequences of sorts.
 *
 * NB: don't use the copy method of this class, since it circumvents caching.
 */
data class Rank private constructor(val sorts: List<Sort>) : List<Sort> by sorts, Serializable {

    val paramSorts: List<Sort> = sorts.dropLast(1)
    val resultSort: Sort = sorts.last()

    val asArraySort: Sort get() = arraySort(paramSorts, resultSort)

    fun isParametrized(): Boolean = this.any { it.isParametrized() }
    companion object {
        val Unknown = Rank(listOf(), Sort.Param("DummyRankSort"))

        private var cache: MutableMap<List<Sort>, Rank>? = null

        operator fun invoke(sorts: List<Sort>): Rank {
            // note this is the only way I found to avoid an ExceptionInInitializerError that resulted from
            //  cache being null (despite being a `val` that is initialized to `ConcurrentHashMap()`)
            //  I'm uncertain if this caching is worth it ... also for the `synchronized`...
            synchronized(this) {
                if (cache == null) {
                    cache = ConcurrentHashMap()
                }
            }
            return cache!!.computeIfAbsent(sorts) { Rank(sorts) }
        }
        operator fun invoke(vararg sort: Sort): Rank = invoke(sort.toList())
        operator fun invoke(paramSorts: List<Sort>, resultSort: Sort): Rank = invoke(paramSorts + resultSort)
    }
}

/** Used for e.g. "(define-fun foo ((x Int) (y Bool)) Int)" */
data class RankWithNamedParams(val rank: Rank, val paramNames: List<String>): Serializable {
    constructor(sort: Sort) : this(Rank(listOf(), sort), listOf())

    init {
        check(rank.size == paramNames.size + 1)
    }

    val size get() = rank.size

    operator fun get(i: Int): Sort = rank.get(i)

    val paramSorts = rank.paramSorts
    val resultSort = rank.resultSort

    fun paramsAsSortedVars(script: ISmtScript) =
        rank.paramSorts.mapIndexed { index, sort -> script.sortedVar(paramNames[index], sort) }
}


/**
 * A [SortSymbol] can be used to construct sort-terms (represented by class [Sort]).
 */
@Treapable
sealed class SortSymbol: Serializable {
    abstract val identifier: Identifier
    abstract val arity: Int

    override fun toString(): String = "$identifier $arity"


    /** Sorts that are defined in some SMT theory */
    sealed class Intp(override val identifier: Identifier, override val arity: kotlin.Int) :
        SortSymbol() {
        object Int : Intp(Identifier.Simple("Int"), 0) {
            private fun readResolve(): Any = Int
            override fun hashCode(): kotlin.Int = utils.hashObject(this)
        }

        object Real : Intp(Identifier.Simple("Real"), 0) {
            private fun readResolve(): Any = Real
            override fun hashCode(): kotlin.Int = utils.hashObject(this)
        }

        object Bool : Intp(Identifier.Simple("Bool"), 0) {
            private fun readResolve(): Any = Bool
            override fun hashCode(): kotlin.Int = utils.hashObject(this)
        }

        object Array : Intp(Identifier.Simple("Array"), 2){
            private fun readResolve(): Any = Array
            override fun hashCode(): kotlin.Int = utils.hashObject(this)
        }


        /** e.g. "(_ BitVec 256)" */
        data class BitVector private constructor(val width: kotlin.Int) :
            Intp(Identifier.Indexed(keyword, listOf(width.toString())), 0) {
            companion object {
                const val keyword = "BitVec"
                fun fromIdentifier(id: Identifier): BitVector? =
                    if (id is Identifier.Indexed && id.sym == keyword) {
                        check(id.indices.size == 1)
                        BitVector(id.indices[0].toInt())
                    } else null

                val width256 = BitVector(EVM_BITWIDTH256)
                private val cache: MutableMap<kotlin.Int, BitVector> = ConcurrentHashMap()
                operator fun invoke(width: kotlin.Int): BitVector =
                    when (width) {
                        256 -> width256
                        else -> cache.computeIfAbsent(width) { BitVector(width) }
                    }
            }
        }

        companion object {
            fun fromIdentifier(s: Identifier): Intp? = when {
                s == Int.identifier -> Int
                s == Real.identifier -> Real
                s == Bool.identifier -> Bool
                s == Array.identifier -> Array
                BitVector.fromIdentifier(s) != null -> BitVector.fromIdentifier(s)
                else -> null
            }
        }
    }

    @Treapable
    data class UserDefined(override val identifier: Identifier, override val arity: Int) : SortSymbol() {
        constructor(name: String, arity: Int) : this(Identifier.Simple(name), arity)
    }

    /** For when we don't have symbol resolution available (yet). */
    data class UserDefinedUnknownArity(override val identifier: Identifier) : SortSymbol() {
        override val arity: Int
            get() = error("this function symbol ('$identifier') does not have an arity, yet")
    }

    companion object {
        fun fromIdentifier(name: Identifier): SortSymbol {
            val intpSortSym = Intp.fromIdentifier(name)
            if (intpSortSym != null) return intpSortSym
            return UserDefinedUnknownArity(name)
        }

        fun fromIdentifier(name: Identifier, symbolTable: SmtSymbolTable): SortSymbol {
            val intpSortSym = Intp.fromIdentifier(name)
            if (intpSortSym != null) return intpSortSym
            return symbolTable.lookUpSort(name.toString())?.sortSymbol ?: error { "sort $name used but not declared" }
        }
    }
}

/**
 * SmtLib standard calls this a sort-term, it represents a sort (or many, if it has parameters).
 */
@Treapable
sealed class Sort: SExp<Sort, SortSymbol>, Serializable {

    /* override fun apply(fs: SortSymbol, vararg args: Sort): Sort = Apply(fs, args.asList()) */

    /** Simple sort, like "Int" */
    data class Symbol private constructor(val symbol: SortSymbol) : Sort(), SExpSym<Sort, SortSymbol> {
        init {
            check(symbol.arity == 0) { "expecting symbol \"$symbol\" to have arity 0, got \"${symbol.arity}\""}
        }

        override fun toString(): String = "${symbol.identifier}"

        companion object {

            val IntSort = Symbol(SortSymbol.Intp.Int)
            val RealSort = Symbol(SortSymbol.Intp.Real)
            val BoolSort = Symbol(SortSymbol.Intp.Bool)
            val BV256Sort = Symbol(SortSymbol.Intp.BitVector.width256)
            val SKeySort = Symbol(SortSymbol.UserDefined(storageKeySortName, 0))

            fun userDefined(name: String) = invoke(SortSymbol.UserDefined(name, 0))

            private val cache: MutableMap<SortSymbol, Symbol> = ConcurrentHashMap()
            operator fun invoke(symbol: SortSymbol): Symbol =
                when (symbol) {
                    SortSymbol.Intp.Int -> IntSort
                    SortSymbol.Intp.Real -> RealSort
                    SortSymbol.Intp.Bool -> BoolSort
                    SortSymbol.Intp.BitVector.width256 -> BV256Sort
                    else -> cache.computeIfAbsent(symbol) { Symbol(symbol) }
                }
        }
    }

    /** Sort parameters, as in " (par (X Y) (select (Array X Y) X Y))" */
    data class Param(val name: String) : Sort(), SExpVar<Sort, SortSymbol> {
        override fun toString(): String = "(par $name)"
    }

    /** "Application of a [SortSymbol] to some sorts, as in "(Array Int Bool)" */
    data class Apply(val symbol: SortSymbol, val params: List<Sort>) : Sort(), SExpApply<Sort, SortSymbol> {
        constructor(symbol: SortSymbol, vararg params: Sort) : this(symbol, params.toList())

        init {
            check(symbol.arity == params.size)
        }

        override val fs: SortSymbol
            get() = symbol
        override val args: List<Sort>
            get() = params

        override fun toString(): String = "(${symbol.identifier} ${params.joinToString(" ")})"
    }

    fun isArraySort(): Boolean = this is Apply && this.symbol == SortSymbol.Intp.Array

    fun isBitVecSort(): Boolean = this is Symbol && this.symbol is SortSymbol.Intp.BitVector

    fun isIntSort(): Boolean = this is Symbol && this.symbol is SortSymbol.Intp.Int

    fun getBitVecSortWidth(): Int {
        check(this is Symbol && this.symbol is SortSymbol.Intp.BitVector)
        return this.symbol.width
    }

    fun isArraySort(x: Sort, y: Sort): Boolean {
        return this is Apply &&
                this.symbol == SortSymbol.Intp.Array &&
                this.params == listOf(x, y)
    }

    fun isParametrized(): Boolean = when (this) {
        is Symbol -> false
        is Param -> true
        is Apply -> this.params.any { it.isParametrized() }
    }

    fun getSortSymbols(): Set<SortSymbol> = when (this) {
        is Symbol -> setOf(this.symbol)
        is Param -> setOf()
        is Apply -> setOf(this.symbol) + this.params.flatMap { it.getSortSymbols() }
    }


    companion object {
        val IntSort get() = Symbol.IntSort
        val RealSort get() = Symbol.RealSort
        val BoolSort get() = Symbol.BoolSort
        val BV256Sort get() = Symbol.BV256Sort
        val SKeySort get() = Symbol.SKeySort
        fun bitVecSort(width: Int) = Symbol(SortSymbol.Intp.BitVector(width))
        fun arraySort(par: Sort, res: Sort) = Apply(SortSymbol.Intp.Array, listOf(par, res))
        fun arraySort(par: List<Sort>, res: Sort) = par.foldRight(res) { l, r -> arraySort(l, r) }


    }

    object Unification: AbstractUnification<Sort, SortSymbol>(
        applyExp = { sortSymbol: SortSymbol, sorts: List<Sort> -> Apply(sortSymbol, sorts) },
        auxTupleConstr = { arity -> SortSymbol.UserDefined(Identifier.Simple("certora_aux_tuple"), arity) }
    ) {
        fun unifyParamSorts(rank: Rank, instantiatedParamSorts: List<Sort>): Rank =
            Rank(unifySorts(rank, instantiatedParamSorts))

        fun unifyResultSort(rank: Rank, instantiatedResultSort: Sort): Rank =
            Rank(unifySort(rank, instantiatedResultSort))
    }
}
