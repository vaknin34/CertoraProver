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

package analysis.icfg

import allocator.SuppressRemapWarning
import analysis.*
import analysis.icfg.ObjectPathMatchingTransformer.analysis
import analysis.pta.ABICodeFinder
import analysis.pta.abi.ABIAnnotator
import analysis.pta.abi.ABIDirectRead
import analysis.pta.abi.DecoderAnalysis
import analysis.worklist.StepResult
import analysis.worklist.WorklistIteration
import com.certora.collect.*
import config.Config
import spec.CVLCompiler
import datastructures.stdcollections.*
import evm.DEFAULT_SIGHASH_SIZE
import evm.EVM_BYTE_SIZE_INT
import evm.EVM_WORD_SIZE
import evm.EVM_WORD_SIZE_INT
import instrumentation.transformers.ABIOptimizations
import spec.cvlast.CVLType
import spec.cvlast.typedescriptors.*
import tac.*
import utils.*
import vc.data.*
import vc.data.TACProgramCombiners.andThen
import vc.data.compilation.storage.InternalCVLCompilationAPI
import vc.data.tacexprutil.ExprUnfolder
import java.math.BigInteger
import java.util.concurrent.ConcurrentHashMap

/**
 * This class performs two major types of optimizations.
 *
 * First, it identifies direct reads out of calldata within an EVM function called from CVL, and rewrites those
 * accesses to directly read out of the original argument; then the calldata read is discarded.
 *
 * In addition, we try to *directly* connect values manipulated in CVL with those read in the contract code.
 * We do this by finding reads of primitive values in CVL that are proven to alias with direct reads from calldata
 * in the contract code. In this case, we create a non-deterministically initialized
 * prophecy variable, and then constrain the value read in CVL and the EVM to be equal to this prophecy variable.
 *
 * For example, suppose we have:
 *
 * ```
 * rule whatever {
 *    uint y;
 *    SomeStruct x;
 *    require(x.someArray[0].someField == y);
 *    f(x);
 * }
 *
 * function f(SomeStruct calldata arg) {
 *     use(arg.someArray[0].someField);
 * }
 * ```
 *
 * we effectively instrument this to be:
 *
 * ```
 * someFieldProphecy = *
 * t = x.someArray[0].someField;
 * require(someFieldProphecy == t)
 * require(t == y)
 *
 * ...
 * t = arg.someArray[0].someField
 * require(t == someFieldProphecy)
 * use(t)
 *
 * ```
 *
 * Currently we only do this matching for direct calldata reads, although we could this with decodes with some extra work.
 */
object ObjectPathMatchingTransformer {

    /**
     * The root of any Access Path. A root must be a cvl variable that was declared (via the
     * [spec.CVLCompiler.Companion.TraceMeta.VariableDeclaration] annotation) at the pointer [where].
     * All aliases (recorded in [AliasInformation] below) must have one of these declarations as a root. The only other
     * "source" of complex types outside of those non-deterministically generated with
     * [spec.CVLCompiler.Companion.TraceMeta.VariableDeclaration] are those returned from external functions. The use case
     * for tracking aliases with values returned from external calls is not clear, and so we intentionally omit handling
     * for it for the time being.
     */
    private data class APRoot(
        val c: CVLCompiler.Companion.TraceMeta.ValueIdentity.CVLVar,
        val where: CmdPointer
    )

    /**
     * Information attached to a [spec.CVLCompiler.Companion.TraceMeta.ValueIdentity] indicating it must alias
     * the value reached via the steps in [ap] starting from [root]. [idxValuation] provides a constant
     * valuation for the index variables that appear in [spec.CVLCompiler.Companion.TraceMeta.CVLAccessPath.ArrayElem].
     *
     * Note that [idxValuation] must be total for all indices that appear in [ap]; we don't track aliases
     * for array elements with a symbolic index.
     */
    private data class AliasInformation(
        val root: APRoot,
        val ap: List<CVLCompiler.Companion.TraceMeta.CVLAccessPathStep>,
        val idxValuation: TreapMap<TACSymbol.Var, BigInteger>
    )

    /**
     * Abstract state used to infer the aliasing information for variables at each point in the program. This is used to find
     * which values accessed in CVL must alias with reads of calldata arguments within EVM code.
     *
     * [aps] maps a [spec.CVLCompiler.Companion.TraceMeta.ValueIdentity] k to its (singular) [AliasInformation]. This
     * indicates that k must alias with (as in, be the same as) the value reached by traversing the root [AliasInformation.root]
     * with the accesses in [AliasInformation.ap].
     *
     * Note that we do not record a set of possible aliases. Given that [AliasInformation] must have a root of a variable declaration
     * (see [APRoot]) this representation is "principle". But extra aliasing information can be easily
     * inferred from the current reprsentation, e.g., if we have that: `a = b.f` and `c = b.f.g` we can easily infer that
     * `c = a.g`.
     *
     * [relevantTvars] acts an "index" which records the set of variables that appear as indices in some access
     * path in some [AliasInformation] or in the domain of [aps]. This is used to make the [kill] function below
     * run very quickly in the extremely common case that these variables are *not* reassigned.
     *
     * [roots] maps a [spec.CVLCompiler.Companion.TraceMeta.ValueIdentity.CVLVar] to the currently incarnation of that
     * variable, represented by an [APRoot]. This is written defensively to **not** assume that a [spec.CVLCompiler.Companion.TraceMeta.ValueIdentity.CVLVar]
     * can only be declared (via [spec.CVLCompiler.Companion.TraceMeta.VariableDeclaration]) once in the program. We certainly expect
     * this to be the case, but are not willing to perform the heavyweight rewrites in this case assuming this fact.
     *
     * [type] maps an [APRoot] to the type of the object declared for that [APRoot].
     */
    private data class IterationState(
        val aps: TreapMap<CVLCompiler.Companion.TraceMeta.ValueIdentity, AliasInformation>,
        val relevantTvars: TreapSet<TACSymbol.Var>,
        val roots: TreapMap<CVLCompiler.Companion.TraceMeta.ValueIdentity.CVLVar, APRoot>,
        val type: TreapMap<APRoot, CVLType.PureCVLType>,
    ) {
        fun kill(l: TACSymbol.Var) : IterationState {
            if(l !in relevantTvars) {
                return this
            }
            return IterationState(aps.updateValues { k, v ->
                if(k is CVLCompiler.Companion.TraceMeta.ValueIdentity.TACVar && k.t == l) {
                    return@updateValues null
                }
                if(l in v.idxValuation) {
                    return@updateValues null
                }
                v
            }, relevantTvars - l, roots, type)
        }

        fun kill(l: CVLCompiler.Companion.TraceMeta.ValueIdentity) : IterationState {
            return when(l) {
                is CVLCompiler.Companion.TraceMeta.ValueIdentity.CVLVar -> this.copy(
                    aps = this.aps - l
                )
                is CVLCompiler.Companion.TraceMeta.ValueIdentity.TACVar -> this.kill(l.t)
            }
        }

        fun getAliasInformation(l: CVLCompiler.Companion.TraceMeta.ValueIdentity) : AliasInformation? {
            aps[l]?.let { toRet ->
                return toRet
            }
            roots[l]?.let {
                return AliasInformation(
                    root = it,
                    ap = listOf(),
                    idxValuation = treapMapOf()
                )
            }
            return null
        }

        /**
         * Associates [v] with a new [APRoot] (which is just [v] tagged with the current location [where]) and record the
         * type [t]. This does **not** kill existing aliasing information with the current [APRoot] associated with [v] (if
         * there is any), as the use of [APRoot] serves to disambiguate.
         *
         * NB: as stated above, we never **really** expect to see a [spec.CVLCompiler.Companion.TraceMeta.ValueIdentity.CVLVar] redeclared
         * like this, but better safe than sorry.
         */
        fun add(v: CVLCompiler.Companion.TraceMeta.ValueIdentity.CVLVar, where: CmdPointer, t: CVLType.PureCVLType) : IterationState {
            val newRoot = APRoot(where = where, c = v)
            return this.copy(
                type = this.type + (newRoot to t),
                roots = this.roots + (v to newRoot)
            )
        }
    }

    /**
     * Try to transform a [analysis.pta.abi.DecoderAnalysis.BufferAccessPath] with symbolic index information into a path
     * that uses only constant indices. The variable -> constant transformation is attemped via the [ExpressionSimplifier]
     * context parameter. If the buffer access path cannot be thus transformed, this function returns null.
     */
    context(CmdPointer, ExpressionSimplifier)
    private fun DecoderAnalysis.BufferAccessPath.tryStatic() : DecoderAnalysis.BufferAccessPath? {
        return when(this) {
            is DecoderAnalysis.BufferAccessPath.ArrayElemOf -> {
                this.indices.mapNotNull {
                    when(it) {
                        is TACSymbol.Const -> it.value
                        is TACSymbol.Var -> this@ExpressionSimplifier.simplify(it.asSym(), this@CmdPointer, true).evalAsConst()
                    }
                }.uniqueOrNull()?.let {
                    DecoderAnalysis.BufferAccessPath.ArrayElemOf(
                        parent = this.parent.tryStatic() ?: return@let null,
                        indices = setOf(it.asTACSymbol())
                    )
                }
            }
            is DecoderAnalysis.BufferAccessPath.Deref -> {
                DecoderAnalysis.BufferAccessPath.Deref(
                    parent = this.parent.tryStatic() ?: return null
                )
            }
            is DecoderAnalysis.BufferAccessPath.Offset -> {
                DecoderAnalysis.BufferAccessPath.Offset(
                    offset = this.offset,
                    base = this.base.tryStatic() ?: return null
                )
            }
            DecoderAnalysis.BufferAccessPath.Root -> this
            is DecoderAnalysis.BufferAccessPath.StaticStride -> DecoderAnalysis.BufferAccessPath.StaticStride(
                strideBy = this.strideBy,
                parent = this.parent.tryStatic() ?: return null
            )
        }
    }

    /**
     * The actual must aliasing analysis.
     *
     * This is made *signifcantly* easier because there are no destructive heap writes.
     */
    private class CVLMustAliasingAnalysis(
        val g: TACCommandGraph
    ) : WorklistIteration<NBId, Unit, Boolean>() {
        val state = treapMapBuilderOf<NBId, IterationState>()
        init {
            for(root in g.rootBlockIds) {
                state[root] = IterationState(
                    aps = treapMapOf(),
                    type = treapMapOf(),
                    roots = treapMapOf(),
                    relevantTvars = treapSetOf()
                )
            }
        }

        val primitiveReads = treapMapBuilderOf<CmdPointer, IterationState>()
        val externalBinds = treapMapBuilderOf<CmdPointer, IterationState>()

        private val exp = ExpressionSimplifier(g = g, trySimplifyConfluence = true)

        override fun process(it: NBId): StepResult<NBId, Unit, Boolean> {
            var st = state[it]!!
            val blk = g.elab(it)

            for(lc in blk.commands) {
                if(lc.cmd is TACCmd.Simple.AssigningCmd) {
                    st = st.kill(lc.cmd.lhs)
                    continue
                }
                if(lc.cmd !is TACCmd.Simple.AnnotationCmd) {
                    continue
                }
                /**
                 * We're only interested in aliasing propagated via the TraceMetas. Value movement between scalar variables
                 * is not interesting to us, for the purposes of finding prophecy variables (see below).
                 *
                 * In other words, once data passes from complex world (tracked via [spec.CVLCompiler.Companion.TraceMeta.ValueIdentity.CVLVar] and
                 * access paths) to actual [vc.data.TACSymbol.Var], we stop tracking.
                 */
                val (annot, payload) = lc.cmd.annot
                when(annot) {
                    CVLCompiler.Companion.TraceMeta.ValueTraversal.META_KEY -> {
                        check(payload is CVLCompiler.Companion.TraceMeta.ValueTraversal)
                        st = st.kill(payload.lhs)
                        /**
                         * Find the constant value of all indices involved in this access. If we can't get a current index, bail out.
                         */
                        val idxVal = payload.ap.mapNotNull {
                            (it as? CVLCompiler.Companion.TraceMeta.CVLAccessPathStep.ArrayElem)?.i
                        }.monadicMap {
                            it `to?` exp.simplify(it.asSym(), lc.ptr, true).evalAsConst()
                        }?.toTreapMap() ?: continue
                        /**
                         * If we are not traversing from an extant alias, check if we are creating an alias from a known
                         * root
                         */
                        val srcAliasInfo = st.getAliasInformation(payload.base) ?: continue
                        if(idxVal.any { (k, v) ->
                                k in srcAliasInfo.idxValuation && srcAliasInfo.idxValuation[k]!! != v
                            }) {
                            /*
                             conflicting valuations? the kill rule for the AP should prevent this (as this requires reassigning to
                             an index variable, which *should* kill the alias information) but just to be sure...
                             */
                            throw IllegalStateException("Have inconsistent valuations for indices of access path $srcAliasInfo vs $idxVal @ $lc")
                        }
                        st = st.copy(
                            aps = st.aps + (payload.lhs to AliasInformation(
                                root = srcAliasInfo.root,
                                ap = srcAliasInfo.ap + payload.ap,
                                idxValuation = srcAliasInfo.idxValuation + idxVal
                            ))
                        )
                        /**
                         * In addition, if we are reading a primitive value (which happens when the output
                         * of the traversal is a tac variable) record the state at this point,
                         * we'll need to for finding prophecy variables later.
                         */
                        if(payload.lhs is CVLCompiler.Companion.TraceMeta.ValueIdentity.TACVar) {
                            primitiveReads[lc.ptr] = st
                        }
                        /**
                         * Finally, update the index
                         */
                        st = st.copy(relevantTvars = st.relevantTvars + idxVal.keys + (payload.lhs as? CVLCompiler.Companion.TraceMeta.ValueIdentity.TACVar)?.t?.let(::setOf).orEmpty())
                    }

                    CVLCompiler.Companion.TraceMeta.VariableDeclaration.META_KEY -> {
                        check(payload is CVLCompiler.Companion.TraceMeta.VariableDeclaration)
                        if(payload.v !is CVLCompiler.Companion.TraceMeta.ValueIdentity.CVLVar) {
                            continue
                        }
                        st = st.kill(payload.v)
                        /*
                           Add a new root for the variable
                         */
                        st = st.add(payload.v, lc.ptr, payload.t)
                    }
                    CVLCompiler.Companion.TraceMeta.CVLMovement.META_KEY -> {
                        /*
                           NB that these values involved here must be cvlvar, by the
                           invariant that cvlmovement is only generated for complex assignments
                           in the cvl to simple compiler
                         */
                        check(payload is CVLCompiler.Companion.TraceMeta.CVLMovement)
                        st = st.kill(payload.dst)
                        /**
                         * A simplified version of the [spec.CVLCompiler.Companion.TraceMeta.ValueTraversal] above.
                         */
                        val srcAp = st.getAliasInformation(payload.src) ?: continue
                        st = st.copy(aps =st.aps + (payload.dst to srcAp))
                    }
                    CVLCompiler.Companion.TraceMeta.ExternalArg.META_KEY -> {
                        check(payload is CVLCompiler.Companion.TraceMeta.ExternalArg)
                        /*
                         * Record the state at this bind, we'll need it later
                         */
                        externalBinds[lc.ptr] = st
                    }
                }
            }
            val work = g.succ(it).filter { succ ->
                if(succ !in state) {
                    state[succ] = st
                    return@filter true
                }
                val curr = state[succ]!!
                if(curr.aps === st.aps && curr.relevantTvars === st.relevantTvars && curr.roots === st.roots && curr.type === st.type) {
                    return@filter false
                }
                val joined = IterationState(
                    aps = st.aps.strictMerge(curr.aps),
                    roots = st.roots.strictMerge(curr.roots),
                    relevantTvars = st.relevantTvars union curr.relevantTvars,
                    type = st.type.strictMerge(curr.type)
                )
                if(joined != curr) {
                    state[succ] = joined
                    true
                } else {
                    false
                }
            }
            return this.cont(work)
        }

        override fun reduce(results: List<Unit>) : Boolean {
            return true
        }
    }

    fun <K, V: Any> TreapMap<K, V>.strictMerge(other: TreapMap<K, V>) = this.merge(other) { _, a, b ->
        if(a == b) {
            a
        } else {
            null
        }
    }

    /**
     * Returns the type reached by traversing the receiver type according to the steps in [ap], starting from the step
     * with index [i]. The [i] parameter is here for recursion, outside callers should always use 0 as the argument;
     * for these arguments, the function returns the type reachable by traversing the fields of [ap], or null if no such
     * traversal was possible (e.g., attempting to follow a struct field on an array type).
     */
    private tailrec fun CVLType.PureCVLType.reachableType(ap: List<CVLCompiler.Companion.TraceMeta.CVLAccessPathStep>, i: Int) : CVLType.PureCVLType? {
        if(i == ap.size) {
            return this
        }
        return when(val step = ap[i]) {
            is CVLCompiler.Companion.TraceMeta.CVLAccessPathStep.ArrayElem -> {
                if(this is CVLType.PureCVLType.StaticArray) {
                    return this.elementType.reachableType(ap, i + 1)
                } else if(this is CVLType.PureCVLType.DynamicArray.WordAligned) {
                    return this.elementType.reachableType(ap, i + 1)
                } else {
                    return null
                }
            }
            CVLCompiler.Companion.TraceMeta.CVLAccessPathStep.ArrayLength -> CVLType.PureCVLType.CVLArrayType.indexType
            is CVLCompiler.Companion.TraceMeta.CVLAccessPathStep.Field -> {
                if(this !is CVLType.PureCVLType.Struct) {
                    return null
                }
                this.fields.find {
                    it.fieldName == step.f
                }?.cvlType?.reachableType(ap, i + 1)
            }
        }
    }

    /**
     * Information indicating a value reachable from an [APRoot] is used as the input to an external EVM call with [id]
     * at root offsset [offset] in the calldata buffer. The value being passed was converted to type [ty].
     *
     * The actual root is not included in this class, rather, [APRoot]'s are associated with a list of these classes.
     * [paths] indicates that the value used was reached by traversing the indicated fields; [idxValuation] provides the
     * constant value for all indices of [spec.CVLCompiler.Companion.TraceMeta.CVLAccessPath.ArrayElem] used in the traversal.
     */
    private data class CallRoot(
        val id: CallId,
        val paths: List<CVLCompiler.Companion.TraceMeta.CVLAccessPathStep>,
        val idxValuation: TreapMap<TACSymbol.Var, BigInteger>,
        val offset: BigInteger,
        val ty: VMTypeDescriptor
    ) {
        /**
         * Indicates whether this call root is a prefix for [other]. If the steps in [paths] is a prefix of [other]
         * *and* they have equal valuations for the array elements, then the suffix of [other] which is
         * not included in [paths] is returned. Otherwise, null is returned.
         *
         * Q: You seem to have forgotten to check that [APRoot] matches?
         * A: As mentioned above, [APRoot]s are mapped to a list of [CallRoot], and this [CallRoot] object is
         * *assumed* have been retried by looking up the list of [CallRoot]s associated with [other]'s [AliasInformation.root].
         */
        fun isPrefixFor(other: AliasInformation) : List<CVLCompiler.Companion.TraceMeta.CVLAccessPathStep>? {
            var i = 0
            while(i < paths.size) {
                if(i >= other.ap.size) {
                    return null
                }
                val thisStep = paths[i]
                val otherStep = other.ap[i]
                when(thisStep) {
                    is CVLCompiler.Companion.TraceMeta.CVLAccessPathStep.ArrayElem -> {
                        // this really should never be null, but let's not throw
                        val currIdx = idxValuation[thisStep.i] ?: return null
                        val otherIdx = (otherStep as? CVLCompiler.Companion.TraceMeta.CVLAccessPathStep.ArrayElem)?.i?.let(other.idxValuation::get) ?: return null
                        if(otherIdx != currIdx) {
                            return null
                        }
                    }
                    CVLCompiler.Companion.TraceMeta.CVLAccessPathStep.ArrayLength -> {
                        if(otherStep !is CVLCompiler.Companion.TraceMeta.CVLAccessPathStep.ArrayLength) {
                            return null
                        }
                    }
                    is CVLCompiler.Companion.TraceMeta.CVLAccessPathStep.Field -> {
                        if((otherStep as? CVLCompiler.Companion.TraceMeta.CVLAccessPathStep.Field)?.f != thisStep.f) {
                            return null
                        }
                    }
                }
                i++
            }
            return other.ap.subList(i, other.ap.size)
        }
    }

    /**
     * Describes an "executable" step through a value. The subtypes of this interface closely mirror the constructors of
     * [spec.CVLCompiler.Companion.TraceMeta.CVLAccessPath] but are elaborated with extra information to enable the compilation
     * of the access into TAC.
     */
    private sealed interface ExecutableAccessStep

    /**
     * Descriptions of how to step through a CVL value at a lower level of detail than provided by [spec.CVLCompiler.Companion.TraceMeta.CVLAccessPath].
     * For example, if the value lies in a bytemap, the bytemap variable holding the value is included, along with offset information.
     *
     * All except for [ArrayElement] are also executable, i.e., they contain sufficient information to translate into TAC. To translate
     * an array element access, we need a logical index, which is provided by the [ArrayElemWithIndex] class.
     */
    private sealed interface CVLAccessStep {
        /**
         * Represents a value (scalar or reference) that is held in the bytemap [baseMap]. The name of the field is [fieldName]
         * (although this is only used for traceability and debugging). [pointerOffset] indicates that before accessing
         * this field the pointer value must be incremented by [pointerOffset] (we borrow Solidity's layout strategy).
         */
        data class PointerField(val pointerOffset: BigInteger, val baseMap: TACSymbol.Var, val fieldName: String) : CVLAccessStep, ExecutableAccessStep

        /**
         * Indicates that the scalar value lies in [fieldNameVar], which is expected to be a [Tag.Int].
         */
        data class ScalarField(val fieldNameVar: TACSymbol.Var, val accessName: String) : CVLAccessStep, ExecutableAccessStep

        /**
         * Represents an array element access without a known index. [elementDataVar] is the bytemap that contains the element
         * information; [packed] indicates whether this array is a packed bytes array (true) or a word-aligned array (false).
         *
         * [lengthOffset] indicates whether the physical location of the element needs to be bumped by 32 bytes to skip the
         * "length" field (as mentioned above, we borrow EVM's value layout in the hopes of interoperability
         * between the two).
         *
         * [fieldName] is a representation of the field(s) traversed to reach this array element. There may be multiple
         * such logical fields if this array is reached via top-level struct fields.
         */
        data class ArrayElement(val elementDataVar: TACSymbol.Var, val lengthOffset: Boolean, val fieldName: String?, val packed: Boolean) : CVLAccessStep
    }

    /**
     * Variant of [CVLAccessStep.ArrayElement] which includes the logical index of the array element being accessed: [idx]
     */
    private data class ArrayElemWithIndex(val elementDataVar: TACSymbol.Var, val lengthOffset: Boolean, val elemSize: BigInteger, val idx: TACSymbol, val fieldName: String?) : ExecutableAccessStep

    private interface AccessSink {
        fun onScalarAccess(
            lhs: TACSymbol.Var,
            cvlValue: TACSymbol.Var
        ) : CommandWithRequiredDecls<TACCmd.Simple>?

        fun onBufferAccess(
            lhs: TACSymbol.Var,
            cvlValue: TACSymbol.Var
        ) : CommandWithRequiredDecls<TACCmd.Simple>?
    }

    private sealed interface ABIAccessRewriter : AccessSink {
        val accessTranslation: ABIAccessTranslation
    }

    private data class RawBytesAccess(override val accessTranslation: ABIAccessTranslation) : ABIAccessRewriter {
        override fun onScalarAccess(lhs: TACSymbol.Var, cvlValue: TACSymbol.Var): CommandWithRequiredDecls<TACCmd.Simple>? {
            return null
        }

        override fun onBufferAccess(
            lhs: TACSymbol.Var,
            cvlValue: TACSymbol.Var
        ): CommandWithRequiredDecls<TACCmd.Simple> {
            return CommandWithRequiredDecls(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = lhs,
                    rhs = cvlValue.asSym()
                ), cvlValue, lhs
            )
        }

    }

    /**
     * A package of an [ABIAccessTranslation] (pattern + rewrite instruction) plus the converters necessary to move
     * from the CVL representation to the VM representation.
     */
    private data class ConverterBasedABIAccessRewrite(
        override val accessTranslation: ABIAccessTranslation,
        val converter: ITypeDescriptorConverter<ISimpleOutput, ITACSymbolVar, ITACSymbolVar>,
        val sourceType: CVLType.PureCVLType
    ) : ABIAccessRewriter {
        private fun moveToEVM(
            cvlValue: TACSymbol.Var,
            lhs: TACSymbol.Var
        ): CommandWithRequiredDecls<TACCmd.Simple> {
            return converter.convertTo(
                fromVar = cvlValue,
                toVar = lhs,
                cb = { it }
            ).uncheckedAs()
        }

        override fun onScalarAccess(lhs: TACSymbol.Var, cvlValue: TACSymbol.Var): CommandWithRequiredDecls<TACCmd.Simple>? {
            return moveToEVM(lhs, cvlValue)
        }

        @OptIn(InternalCVLCompilationAPI::class)
        override fun onBufferAccess(
            lhs: TACSymbol.Var,
            cvlValue: TACSymbol.Var
        ): CommandWithRequiredDecls<TACCmd.Simple>? {
            val outputVar = TACKeyword.TMP(sourceType.toTag(), "bufferValueTmp")
            return CommandWithRequiredDecls(CVLToSimpleCompiler.decodePrimitiveBufferRepresentation(
                bufferValue = cvlValue,
                lhs = outputVar,
                enc = (sourceType as? CVLType.PureCVLType.BufferEncodeableType)?.getEncoding() ?: return null
            )) andThen this.moveToEVM(
                outputVar,
                lhs
            )
        }
    }


    /**
     * Common interface describing "patterns" over [analysis.pta.abi.DecoderAnalysis.BufferAccessPath]. Portions of these patterns
     * describe how to translate portions of the  [analysis.pta.abi.DecoderAnalysis.BufferAccessPath] into an access over CVL.
     * Thus, the result of a successful pattern match is a sequence of [ExecutableAccessStep] which describe how to compile
     * an access to the matched [analysis.pta.abi.DecoderAnalysis.BufferAccessPath] into CVL.
     *
     * For those familiar (hi Alex B) this serves a similar role to the [analysis.icfg.ABICallConvention.ObjectTraversalConstructor].
     *
     * By convention, all of the subtypes of this interface have the name "ExpectX", indicating that the type
     * expects to match a [analysis.pta.abi.DecoderAnalysis.BufferAccessPath] constructor with the name X (e.g., [ExpectDeref]
     * matches [analysis.pta.abi.DecoderAnalysis.BufferAccessPath.Deref])
     */
    private sealed interface ABIAccessTranslation

    /**
     * Marker interface for [ABIAccessTranslation] instances that are not [ExpectRoot].
     */
    private sealed interface IntermediateAccessTranslation : ABIAccessTranslation

    /**
     * Matches a [analysis.pta.abi.DecoderAnalysis.BufferAccessPath.Offset] with
     * [analysis.pta.abi.DecoderAnalysis.BufferAccessPath.Offset.offset] that equals [o], and whose
     * [analysis.pta.abi.DecoderAnalysis.BufferAccessPath.Offset.base] matches [prev].
     *
     * The [analysis.pta.abi.DecoderAnalysis.BufferAccessPath.Offset] corresponds to executable [steps]. Note that
     * one [ExpectOffset] can correspond to multiple steps, as structs are "flattened" when ABI encoded.
     *
     * Note that [steps] only contain the access steps included in this offset, these steps logically come after all of the steps
     * generated by a match in prev.
     */
    private data class ExpectOffset(val o: BigInteger, val prev: ABIAccessTranslation, val steps: List<ExecutableAccessStep>) : IntermediateAccessTranslation

    /**
     * Matches a [analysis.pta.abi.DecoderAnalysis.BufferAccessPath.ArrayElemOf]
     * whose [analysis.pta.abi.DecoderAnalysis.BufferAccessPath.ArrayElemOf.parent] matches [prev].
     * The matched [analysis.pta.abi.DecoderAnalysis.BufferAccessPath.ArrayElemOf.indices] are combined with [elem] to produce
     * the executable [ArrayElemWithIndex] step, which corresponds to the array element indexing.
     */
    private data class ExpectArrayElement(val elem: CVLAccessStep.ArrayElement, val prev: ABIAccessTranslation) : IntermediateAccessTranslation

    /**
     * Matches a [analysis.pta.abi.DecoderAnalysis.BufferAccessPath.Deref] whose [analysis.pta.abi.DecoderAnalysis.BufferAccessPath.Deref.parent]
     * matches [prev]. This step does not have a corresponding step in CVL.
     */
    private data class ExpectDeref(val prev: ABIAccessTranslation) : IntermediateAccessTranslation

    /**
     * Matches a [analysis.pta.abi.DecoderAnalysis.BufferAccessPath.Root]
     */
    private object ExpectRoot : ABIAccessTranslation

    /**
     * A common interface used to build up [ABIAccessTranslation] objects. The steps needed to be taken
     * in CVL *greatly* depends on whether the access is happening via an array element. Traversing struct
     * fields without an array access "just happens" via the flattening of structs into identifiers, however
     * *within* an array there are field pointers and bytemap reads involved. Similarly, an array element accesses need to be
     * offset by 32 bytes depending on whether if it is a top level array (not needed) or an array nested within another
     * one (needed). All of this context is handled by the [AccessBuilder] object, and the decisions about what
     * type of [CVLAccessStep] to use is determined by the concrete subclass of [AccessBuilder]. The [DynamicBuilder] is
     * used for accesses that have traversed an array, and use the pointer model of data, whereas the [RootBuilder]
     * is used for accesses that have not yet traversed an array element. [RootBuilder.pushArrayElem] seamlessly switches
     * to [DynamicBuilder], passing off the state along to the new [DynamicBuilder].
     *
     * However, the user of this interface can just push elements without worrying about this, hence this design.
     *
     * Each [AccessBuilder] object is immutable and represents an in progress construction of an [ABIAccessTranslation].
     * The push* functions generate a new [AccessBuilder] object (if able) that represents the same in progress
     * [ABIAccessTranslation] but with the new type of match included.
     *
     * [build] is called to retrieve the [ABIAccessTranslation] corresponding to the [AccessBuilder], or null
     * if the builder is in a bad state.
     */
    private interface AccessBuilder {
        /**
         * Indicates we want to match a field with name [field] at offset within its type [offs]. The ordinal
         * number of the field is [ord].
         */
        fun pushStructField(ord: Int, offs: BigInteger, field: String) : AccessBuilder?

        /**
         * Indicates we want to match an array length field. It is expected (but not checked) that after calling this function
         * the resulting object will simply have [build] called upon it.
         */
        fun pushArrayLength(): AccessBuilder?

        /**
         * Indicates we want to extend the in progress match construction by matching an array element. Whether the
         * array is packed or not is determined by the [packed] argument.
         */
        fun pushArrayElem(packed: Boolean): AccessBuilder?

        /**
         * Indicates that the in progress match should be extended to match a
         * [analysis.pta.abi.DecoderAnalysis.BufferAccessPath.Deref] (an artifact of the [analysis.pta.abi.DecoderAnalysis.BufferAccessPath])
         */
        fun pushDynamic(): AccessBuilder

        /**
         * Return the "finalized" [ABIAccessTranslation] represented by this object.
         */
        fun build(): ABIAccessTranslation?
    }

    /**
     * The builder instance used once at least one array element has been traversed. After this
     * point, accesses within CVL are effected with pointer semantics, and the array indexing logic changes.
     *
     * Note that the actual logic used for choosing which [ABIAccessTranslation] type constructor to use
     * is the same, as is the logic for offset tracking.
     *
     * It is an invariant of this class that [ABIAccessTranslation] will never be an [ExpectOffset],
     * these constructors are always added "on demand" during [pushDynamic], [pushArrayElem], or [build].
     *
     * The current offset from the access path pattern represented by [currTraversal] is recordded in [currOffset].
     */
    private class DynamicBuilder(
        val fieldMap: Map<List<DataField>, TACSymbol.Var>,
        val currOffset: BigInteger,
        val currSteps: List<ExecutableAccessStep>,
        val currFields: List<DataField>,
        val currTraversal: ABIAccessTranslation
    ) : AccessBuilder {
        init {
            check(currTraversal !is ExpectOffset) {
                "Representation invariant broken, have expect offset at root: $currTraversal"
            }
        }
        override fun pushStructField(ord: Int, offs: BigInteger, field: String): AccessBuilder? {
            return commonField(offs, (ord * EVM_WORD_SIZE_INT).toBigInteger(), DataField.StructField(field), field)
        }

        private fun commonField(evmOffset: BigInteger, cvlOffset: BigInteger, field: DataField, fieldString: String) : AccessBuilder? {
            val subField = currFields + field
            val fieldContainer = fieldMap[subField]?.takeIf {
                it.tag is Tag.ByteMap
            } ?: return null
            return DynamicBuilder(
                currOffset = currOffset + evmOffset,
                currTraversal = currTraversal,
                currSteps = currSteps + CVLAccessStep.PointerField(
                    cvlOffset,
                    fieldContainer,
                    fieldString
                ),
                currFields = subField,
                fieldMap = fieldMap
            )
        }

        override fun pushArrayLength(): AccessBuilder? {
            return commonField(BigInteger.ZERO, BigInteger.ZERO, DataField.ArrayLength, "length")
        }

        override fun pushArrayElem(packed: Boolean): AccessBuilder? {
            if(currOffset != BigInteger.ZERO) {
                return null
            }
            val subField = currFields + DataField.ArrayData
            val dataContainer = fieldMap[subField]?.takeIf {
                it.tag is Tag.ByteMap
            } ?: return null
            return DynamicBuilder(
                fieldMap = fieldMap,
                currFields = subField,
                currSteps = listOf(),
                currTraversal = ExpectArrayElement(prev = currTraversal, elem = CVLAccessStep.ArrayElement(dataContainer, lengthOffset = true, fieldName = null, packed = packed)),
                currOffset = BigInteger.ZERO
            )
        }

        override fun pushDynamic(): AccessBuilder {
            return DynamicBuilder(
                fieldMap = fieldMap,
                currOffset = BigInteger.ZERO,
                currFields = currFields,
                currTraversal = ExpectDeref(
                    ExpectOffset(
                        o = currOffset,
                        steps = currSteps,
                        prev = currTraversal
                    )
                ),
                currSteps = listOf()
            )
        }

        override fun build(): ABIAccessTranslation {
            return ExpectOffset(
                prev = currTraversal,
                steps = currSteps,
                o = currOffset
            )
        }

    }

    /**
     * The [AccessBuilder] instance used up until an array element is traversed.
     *
     * In practice this is used only for "top-level" struct fields, which are always variables.
     */
    private class RootBuilder(
        /**
         * Used for traceability and debugging purposes
         */
        val rootName: String,
        /**
         * Mapping extracted from the [ExternalArg]
         */
        val fieldMap: Map<List<DataField>, TACSymbol.Var>,
        /**
         * The sequence of traversals built up so far in this object. It is an invariant that
         * this is *never* [ExpectOffset], it must be [ExpectRoot] or [ExpectDeref], like the
         * [DynamicBuilder], [ExpectOffset] are added on demand at [pushArrayElem] and [pushDynamic].
         */
        val currTraversal: ABIAccessTranslation,
        /**
         * The word offset within the buffer access path being built by this object. When an [ExpectOffset]
         * is pushed, this running total is used as the offset.
         */
        val currOffset: BigInteger,
        /**
         * Sequence of [DataField]s traversed so far in the access represented by the object
         */
        val currFields: List<DataField>
    ) : AccessBuilder {
        override fun pushStructField(ord: Int, offs: BigInteger, field: String): AccessBuilder {
            return commonField(offs, DataField.StructField(field))
        }

        private fun commonField(offs: BigInteger, field: DataField): AccessBuilder {
            return RootBuilder(
                rootName = rootName,
                currTraversal = currTraversal,
                currFields = currFields + field,
                currOffset = currOffset + offs,
                fieldMap = fieldMap
            )
        }

        override fun pushArrayElem(packed: Boolean): AccessBuilder? {
            if(currOffset != BigInteger.ZERO) {
                return null
            }
            val fieldName = getFieldName()
            val dataFields = currFields + DataField.ArrayData
            val baseMap = fieldMap[dataFields]?.takeIf {
                it.tag is Tag.ByteMap
            } ?: return null
            val arrayAccess = CVLAccessStep.ArrayElement(baseMap, lengthOffset = false, fieldName = fieldName, packed = packed)
            return DynamicBuilder(
                fieldMap = fieldMap,
                currOffset = BigInteger.ZERO,
                currFields = dataFields,
                currSteps = listOf(),
                currTraversal = ExpectArrayElement(arrayAccess, currTraversal)
            )
        }

        override fun pushArrayLength(): AccessBuilder {
            return commonField(BigInteger.ZERO, DataField.ArrayLength)
        }

        override fun pushDynamic(): AccessBuilder {
            val newTraversal = ExpectDeref(ExpectOffset(
                o = currOffset, prev = currTraversal, steps = listOf()
            ))
            return RootBuilder(rootName, fieldMap, newTraversal, BigInteger.ZERO, currFields)
        }

        private fun getFieldName() : String {
            return rootName + currFields.joinToString(".") {
                when(it) {
                    DataField.ArrayData -> throw IllegalStateException("should not have pushed array data")
                    DataField.ArrayLength -> "length"
                    is DataField.StructField -> it.field
                }
            }.let {
                if(it.isNotEmpty()) {
                    ".$it"
                } else {
                    it
                }
            }

        }

        override fun build(): ABIAccessTranslation? {
            val f = fieldMap[currFields] ?: return null
            return ExpectOffset(
                prev = currTraversal,
                steps = listOf(CVLAccessStep.ScalarField(fieldNameVar = f, accessName = getFieldName())),
                o = currOffset
            )
        }
    }

    private fun AccessBuilder.buildWithConverter(src: CVLType.PureCVLType, dst: EVMTypeDescriptor) : ABIAccessRewriter? {
        val tr = this.build() ?: return null
        val conv = dst.converterFrom(src, ToVMContext.DirectPassing.getVisitor()).resultOrNull() ?: return null
        return ConverterBasedABIAccessRewrite(
            accessTranslation = tr,
            sourceType = src,
            converter = conv
        )
    }

    /**
     * Recursively traverse the EVM type [ty], using [tr] to build up a list [ABIAccessRewriter] for primitive
     * types reachable in [ty]. Recall that [tr] represents an [ABIAccessTranslation] which itself represents a
     * pattern match over [analysis.pta.abi.DecoderAnalysis.BufferAccessPath] objects that produces instructions for
     * how to traverse an "equivalent" value in CVL. At the "leaves" of the type we take the [ABIAccessTranslation] represented by
     * [tr], and elaborate it with instructions on how to move the accessed value to the EVM producing the output [ABIAccessRewriter].
     */
    private fun traverseType(tr: AccessBuilder, ty: EVMTypeDescriptor, sourceTy: CVLType.PureCVLType) : List<ABIAccessRewriter> {
        val workingBuilder = tr.letIf(ty.isDynamicType()) {
            tr.pushDynamic()
        }
        if(ty is EVMTypeDescriptor.EVMValueType) {
            return listOfNotNull(workingBuilder.buildWithConverter(sourceTy, ty))
        }
        @Suppress("KotlinConstantConditions")
        // XXX(jtoman): this feels like the 100th time I've written a "traverse a CVL and EVM type in parallel" function
        return when(ty) {
            is EVMTypeDescriptor.DynamicArrayDescriptor -> {
                if(sourceTy !is CVLType.PureCVLType.DynamicArray.WordAligned) {
                    return listOf()
                }
                val toRet = mutableListOf<ABIAccessRewriter>()
                workingBuilder.pushArrayLength()?.buildWithConverter(CVLType.PureCVLType.CVLArrayType.lengthType, ty.lengthType)?.let(toRet::add)
                workingBuilder.pushArrayElem(false)?.let {
                    traverseType(it, ty.elementType, sourceTy.elementType)
                }?.let(toRet::addAll)
                toRet
            }
            is EVMTypeDescriptor.EVMStructDescriptor -> {
                if(sourceTy !is CVLType.PureCVLType.Struct) {
                    return listOf()
                }
                val toRet = mutableListOf<ABIAccessRewriter>()
                var offs = BigInteger.ZERO
                var card = 0
                for(t in ty.fields) {
                    val sourceField = sourceTy.fields.find {
                        it.fieldName == t.fieldName
                    }?.cvlType ?: continue
                    toRet.addAll(traverseType(
                        tr = workingBuilder.pushStructField(card, offs, t.fieldName) ?: continue,
                        ty = t.fieldType,
                        sourceTy = sourceField
                    ))
                    offs += t.fieldType.sizeAsEncodedMember()
                    card++
                }
                toRet
            }

            is EVMTypeDescriptor.EVMMappingDescriptor,
            is EVMTypeDescriptor.FunctionDescriptor,
            is EVMTypeDescriptor.PackedBytes1Array -> {
                listOfNotNull(
                    // XXX(jtoman): for odd reasons, the PackedBytes1Array type does not implement VMDynamicArrayTypeDescriptor
                    workingBuilder.pushArrayLength()?.buildWithConverter(CVLType.PureCVLType.CVLArrayType.lengthType, EVMTypeDescriptor.UIntK(EVM_WORD_SIZE_INT * EVM_BYTE_SIZE_INT)),
                    /*
                     * This lets us directly access entire words of `bytes` arrays in CVL, which
                     * isn't actually possible anywhere else in CVL (indexing into bytes arrays in CVL is
                     * busted anyway).
                     */
                    workingBuilder.pushArrayElem(true)?.build()?.let(::RawBytesAccess)
                )
            }
            is EVMTypeDescriptor.StaticArrayDescriptor -> listOf()

            // kotlin warns about incomplete `when` without this,
            // warns if you have it :-\
            is EVMTypeDescriptor.EVMValueType -> `impossible!`
        }
    }

    private fun traverseType(
        rootName: String,
        rootOffset: BigInteger,
        targetTy: EVMTypeDescriptor,
        sourceTy: CVLType.PureCVLType,
        fieldMap: Map<List<DataField>, TACSymbol.Var>
    ) : List<ABIAccessRewriter> {
        return traverseType(RootBuilder(
            fieldMap = fieldMap,
            currTraversal = ExpectRoot,
            currFields = listOf(),
            currOffset = rootOffset,
            rootName = rootName
        ), targetTy, sourceTy)
    }

    /**
     * Try to match [sourceAccessPath] with [toMatch]. As belabored elsewhere, the reuslt of this match is a list of [ExecutableAccessStep].
     * These steps are passed to [cb] which is expected to return a pair of commands which "compiles" these [ExecutableAccessStep],
     * and a [TACSymbol] which holds the result of executing these accesses. The result of this [cb] is returned as the overall
     * result of this function; or null if [cb] itself returns null or the match fails.
     *
     * In what is a familiar pattern by now, [cb] is a continuation, on recursive calls, a new [cb] instance is created;
     * this new callback adds the list of [ExecutableAccessStep] generated by the current matching step to the steps
     * received as a parameter, and passes this elaborated list onto the original [cb] instance. Thus, the [cb] instance
     * passed into the "top-level" call to [tryMatch] is ultimately invoked with the full list of [ExecutableAccessStep]
     * generated by a complete match.
     *
     * NB [cb] is not invoked if the match fails.
     *
     * The context parameters are used to attempt simplifying the index symbols to constant values; if this simplification
     * fails, we use a symbolic index.
     */
    context(CmdPointer, ExpressionSimplifier)
    tailrec private fun <T> tryMatch(
        sourceAccessPath: DecoderAnalysis.BufferAccessPath,
        toMatch: ABIAccessTranslation,
        cb: (List<ExecutableAccessStep>) -> T?
    ) : T? {
        return when(sourceAccessPath) {
            is DecoderAnalysis.BufferAccessPath.ArrayElemOf -> {
                if(toMatch !is ExpectArrayElement) {
                    return null
                }
                if(sourceAccessPath.indices.isEmpty()) {
                    return null
                }
                tryMatch(
                    sourceAccessPath = sourceAccessPath.parent,
                    toMatch = toMatch.prev
                ) { acc ->
                    val idx = sourceAccessPath.indices.mapNotNull {
                        simplify(it.asSym(), this@CmdPointer, inPrestate = true, stopAt = null).evalAsConst()?.asTACSymbol()
                    }.uniqueOrNull() ?: sourceAccessPath.indices.first() // guaranteed not to throw due to isEmpty check above
                    cb(acc + ArrayElemWithIndex(
                        elementDataVar = toMatch.elem.elementDataVar,
                        idx = idx,
                        elemSize = if(!toMatch.elem.packed) { EVM_WORD_SIZE } else { BigInteger.ONE },
                        lengthOffset = toMatch.elem.lengthOffset,
                        fieldName = toMatch.elem.fieldName
                    ))
                }
            }
            is DecoderAnalysis.BufferAccessPath.Deref -> {
                if(toMatch !is ExpectDeref) {
                    return null
                }
                tryMatch(sourceAccessPath.parent, toMatch.prev, cb)
            }
            is DecoderAnalysis.BufferAccessPath.Offset -> {
                if(toMatch !is ExpectOffset || toMatch.o != sourceAccessPath.offset) {
                    return null
                }
                tryMatch(sourceAccessPath = sourceAccessPath.base, toMatch.prev) { accStep ->
                    cb(accStep + toMatch.steps)
                }
            }
            DecoderAnalysis.BufferAccessPath.Root -> {
                if(toMatch !is ExpectRoot) {
                    return null
                }
                return cb(listOf())
            }
            is DecoderAnalysis.BufferAccessPath.StaticStride -> {
                return null
            }
        }
    }

    /**
     * Carrier class for instrumentation instructions computed in parallel by the analysis,
     * and then applied later sequentially.
     */
    @SuppressRemapWarning
    private data class Instrumentation(
        val output: TACSymbol.Var,
        val insertRead: CommandWithRequiredDecls<TACCmd.Simple>?,
        val prophecyKey: Pair<CallId, DecoderAnalysis.BufferAccessPath>?,
        val read: ABIDirectRead
    )

    /**
     * Class for tracking reads of primitive CVL values that may alias with direct calldata reads
     * in EVM code. [prophecyVar] is the prophecy variable to use for linking these two families of values.
     * [sources] is a map of program locations that read a potentially aliased value, and the [TACSymbol.Var]
     * which holds the result of that read. [hasConsumer] indicates that we found at least one read in
     * the contract code which observes this aliased value.
     *
     * Like [CallRoot], the identity of the potentially aliased value is not included in this class state.
     */
    private class ProphecyVars(val prophecyVar: TACSymbol.Var) {
        val sources = treapMapBuilderOf<CmdPointer, TACSymbol.Var>()
        var hasConsumer = false
    }

    /**
     * Translate a sequence of [ExecutableAccessStep] to straightline code that effects these accesses,
     * and the symbol which holds the result of the access. This is used as the initial callback to [tryMatch].
     *
     * It returns null if the compilation fails (e.g., there is a nonsensical sequence of commands)
     */
    private fun rewriteAccess(
        lhs: TACSymbol.Var,
        l: List<ExecutableAccessStep>,
        sinkHandler: AccessSink
    ) : CommandWithRequiredDecls<TACCmd.Simple>? {
        var pointerAcc : TACSymbol? = null

        val accessString = l.joinToString(".") { it ->
            when (it) {
                is ArrayElemWithIndex -> {
                    (it.fieldName.orEmpty()) + "[${it.idx}]"
                }

                is CVLAccessStep.PointerField -> {
                    it.fieldName
                }

                is CVLAccessStep.ScalarField -> it.accessName
            }
        }

        val cmdAcc = MutableCommandWithRequiredDecls<TACCmd.Simple>()
        cmdAcc.extend(TACCmd.Simple.LabelCmd("Direct access instrumentation: $accessString"))
        for((i, acc) in l.withIndex()) {
            when(acc) {
                is ArrayElemWithIndex -> {
                    if(pointerAcc == null) {
                        check(i == 0 && !acc.lengthOffset) {
                            "Have null pointer accumulator within chain"
                        }
                        pointerAcc = TACSymbol.Zero
                    }
                    val nextPointer = TACKeyword.TMP(Tag.Bit256, "next")
                    cmdAcc.extend(ExprUnfolder.unfoldPlusOneCmd("arrayIdx", with(TACExprFactUntyped) {
                        Add(pointerAcc!!.asSym(), Mul(acc.idx.asSym(), acc.elemSize.asTACExpr).letIf(acc.lengthOffset) {
                                Add(EVM_WORD_SIZE.asTACExpr, it)
                            }
                        )
                    }) {
                        TACCmd.Simple.AssigningCmd.ByteLoad(
                            lhs = nextPointer,
                            loc = it.s,
                            base = acc.elementDataVar
                        )
                    })
                    cmdAcc.extend(nextPointer)
                    pointerAcc = nextPointer
                }
                is CVLAccessStep.PointerField -> {
                    if(pointerAcc == null) {
                        return null
                    }
                    val nextPointer = TACKeyword.TMP(Tag.Bit256, "next")
                    cmdAcc.extend(ExprUnfolder.unfoldPlusOneCmd("fieldAccess", with(TACExprFactUntyped) {
                        Add(acc.pointerOffset.asTACExpr, pointerAcc!!.asSym())
                    }) {
                        TACCmd.Simple.AssigningCmd.ByteLoad(
                            lhs = nextPointer,
                            loc = it.s,
                            base = acc.baseMap
                        )
                    })
                    cmdAcc.extend(nextPointer)
                    pointerAcc = nextPointer
                }
                is CVLAccessStep.ScalarField -> {
                    check(l.size == 1) {
                        "Invariant broken: have direct scalar accessed in a complex chain: $l $acc"
                    }
                    return sinkHandler.onScalarAccess(
                        lhs = lhs,
                        cvlValue = acc.fieldNameVar
                    )?.let {
                        cmdAcc.toCommandWithRequiredDecls() andThen it
                    }
                }
            }
        }
        if(pointerAcc !is TACSymbol.Var) {
            return null
        }
        return sinkHandler.onBufferAccess(
            lhs = lhs,
            cvlValue = pointerAcc
        )?.let {
            cmdAcc.toCommandWithRequiredDecls() andThen it
        }
    }

    /**
     * A class for generating mappers for calldata reference rewriting. After running the mapper returned by [getMapper],
     * [scalarConversionCode] will hold a set of (non-empty) commands that need to be added to the start of the given call id
     * to create a rebinding of the calldata.
     */
    private class ScalarRewriteManager(val scalarArgGen: TreapMap<CallId, TreapMap<BigInteger, (TACSymbol.Var) -> CommandWithRequiredDecls<TACCmd.Simple>>>) {
        val replacement = ConcurrentHashMap<CallId, MutableMap<BigInteger, TACSymbol.Var>>()
        val scalarConversionCode = mutableMapOf<CallId, CommandWithRequiredDecls<TACCmd.Simple>>()

        fun getMapper(id: CallId) : ScalarRewriteMapper? {
            val gen = scalarArgGen[id] ?: return null
            val m = replacement.computeIfAbsent(id) { mutableMapOf() }
            return ScalarRewriteMapper(gen, m, id)
        }

        /**
         * A command mapper which rewrites reads of scalar variables using [scalarArgGen]. The key and values in this
         * map have the interpretation for the scalarToArg codomain. It is intended that each instance of this class
         * is used to rewrite one command. The [mutated] field is set to true if the command was rewritten, otherwise
         * it is left false.
         */
        inner class ScalarRewriteMapper(
            private val gen: TreapMap<BigInteger, (TACSymbol.Var) -> CommandWithRequiredDecls<TACCmd.Simple>>,
            private val m: MutableMap<BigInteger, TACSymbol.Var>,
            private val id: CallId
        ) : DefaultTACCmdMapper() {
            var mutated = false

            override fun mapLhs(t: TACSymbol.Var): TACSymbol.Var {
                return t
            }

            override fun mapVar(t: TACSymbol.Var): TACSymbol.Var {
                val ind = t.getScalarCallindex() ?: return t
                val otfConverter = gen[ind] ?: return t
                mutated = true
                val replacement = if(ind !in m) {
                    synchronized(m) {
                        if(ind !in m) {
                            val replacement = TACKeyword.TMP(Tag.Bit256, "scalarReplacement")
                            m[ind] = replacement
                            val conv = otfConverter(replacement)
                            synchronized(scalarConversionCode) {
                                scalarConversionCode[id] = scalarConversionCode.getOrDefault(id, CommandWithRequiredDecls()).merge(conv)
                            }
                        }
                        m[ind]!!
                    }
                } else {
                    m[ind]!!
                }
                return replacement
            }
        }
    }
    private class Mapper(val offsetToGen: TreapMap<BigInteger, (TACSymbol.Var) -> CommandWithRequiredDecls<TACCmd.Simple>>) : DefaultTACCmdMapper() {
        val toReplace = mutableMapOf<BigInteger, TACSymbol.Var>()
        val toPrefix = mutableListOf<CommandWithRequiredDecls<TACCmd.Simple>>()

        override fun mapLhs(t: TACSymbol.Var): TACSymbol.Var {
            return t
        }

        override fun mapVar(t: TACSymbol.Var): TACSymbol.Var {
            val ind = t.getScalarCallindex() ?: return t
            val otfConverter = offsetToGen[ind] ?: return t
            return toReplace.getOrPut(ind) {
                val tmp = TACKeyword.TMP(Tag.Bit256, "scalarReplacement")
                val code = otfConverter(tmp).merge(tmp)
                toPrefix.add(code)
                tmp
            }

        }
    }

    private fun TACSymbol.Var.getScalarCallindex(): BigInteger? {
        if(TACMeta.IS_CALLDATA !in this.meta) {
            return null
        }
        return this.meta.find(TACMeta.SCALARIZATION_SORT)?.let {
            it as? ScalarizationSort.Split
        }?.idx
    }


    fun analysis(c: CoreTACProgram) : CoreTACProgram {
        if(!Config.EnableAggressiveABIOptimization.get()) {
            return c
        }
        val g = c.analysisCache.graph

        val exp = ExpressionSimplifier(g = g, trySimplifyConfluence = true)

        /**
         * First compute must aliasing between CVL values. We are most interested in the states at reads of primitive values
         * out complex types ([CVLMustAliasingAnalysis.primitiveReads]) and the state at external argument binding
         * [CVLMustAliasingAnalysis.externalBinds].
         */
        val mustAlias = CVLMustAliasingAnalysis(g)
        val ok = mustAlias.submit(listOf(c.getStartingBlock()))
        if(!ok) {
            return c
        }

        /**
         * Map from a [CallId] to the [ABIAccessRewriter] objects (i.e., patterns and rewrites) constructed for the
         * arguments into the function with that call id.
         */
        val buffersAsPath = treapMapBuilderOf<CallId, MutableList<ABIAccessRewriter>>()

        /**
         * This is something of a kludge to rewrite references to scalarized calldata. Within an external call with the
         * [CallId] for a given key, maps scalarized calldata offsets to a generator function. This argument generator
         * accepts a variable v, and returns code that moves the primitive argument at the calldata offset into v.
         *
         * For example, if we pass some CVL address `a` as the first argument to an external EVM function with call
         * id k, and this address is accessed via the scalarized calldata variable `tacCalldata!4@k`, then we will have:
         *
         * `scalarToArg[k][4] = { v -> move `a` into the variable v }`
         */
        val scalarToArg = treapMapBuilderOf<CallId, TreapMap<BigInteger, (TACSymbol.Var) -> CommandWithRequiredDecls<TACCmd.Simple>>>()

        /**
         * Maps [APRoot]s to uses of that [APRoot] (or value reachable from [APRoot]) as an argument to an external function.
         * As promised, this is where [CallRoot]s are associated with [APRoot]s.
         */
        val callSiteUses = treapMapBuilderOf<APRoot, List<CallRoot>>()
        extractExternalArgData(mustAlias, g, scalarToArg, buffersAsPath, callSiteUses)
        /**
         * maps pairs of [CallId] and a (static) [analysis.pta.abi.DecoderAnalysis.BufferAccessPath] to the
         * prophecy variable associated with that path. for a (k, bap) key, a direct read of bap in the external call with
         * id k should be constrained to match the mapped prophecy variable. The [ProphecyVars.sources] (which, recall,
         * are accesses of the same value but in CVL) will also be constrained to equal that prophecy variable.
         */
        val prophecyMatch = treapMapBuilderOf<Pair<CallId, DecoderAnalysis.BufferAccessPath>, ProphecyVars>()

        extractPrimitiveAliasingData(mustAlias, g, callSiteUses.build(), prophecyMatch)

        /**
         * now that we're set up, record where we'll be rewriting [ABIDirectRead] annotations, as described by the
         * [Instrumentation] object.
         */
        val directRewrites = treapMapBuilderOf<CmdPointer, Instrumentation>()

        val scalarRewrites = mutableMapOf<CmdPointer, TACCmd.Simple>()

        val scalarRewriter = ScalarRewriteManager(scalarArgGen = scalarToArg.build())

        /**
         * In parallel, compute the rewrites of scalars, and then sequentially record these in scalarRewrites,
         * using my much loved thunk trick.
         */
        c.parallelLtacStream().filter {
            it.ptr.block.calleeIdx in scalarToArg
        }.mapNotNull { lc ->
            val mapper = scalarRewriter.getMapper(lc.ptr.block.calleeIdx) ?: return@mapNotNull null
            val ret = mapper.map(lc.cmd)
            if(!mapper.mutated) {
                return@mapNotNull null
            }
            {
                scalarRewrites[lc.ptr] = ret
            }
        }.sequential().forEach {
            it()
        }

        /**
         * Now with all the setup done, the actual rewriting is rather straight forward: find all direct reads for which
         * we have rewrite opportunities, i.e., [ABIDirectRead] annotations at call indices with a mapping in buffersAsPath.
         */
        c.parallelLtacStream().filter {
            it.ptr.block.calleeIdx in buffersAsPath
        }.mapNotNull {
            it `to?` it.maybeAnnotation(ABIDirectRead.META_KEY)
        }.mapNotNull { (where, i) ->
            /**
             * We are attempting two rewrites here:
             * the first is to insert the prophecy variable assumption if possible. To do this, we see if the buffer access
             * path being accessed is static, and then consult prophecyMath. If we find a mapped value, then we know there
             * is at least one read in CVL code which aliases with this direct read; i.e., we should generate a prophecy variable constraint.
             *
             * The second is to completely rewrite the direct access. Note that this can coexist with the first optimization: for the
             * first optimization we are performing a constraint on the result of the direct read; if this direct read is rewritten
             * to directly access the CVL arguments, that's fine.
             */
            val (prophecyKey, directAccess) = with(where.ptr) {
                with(exp) {
                    i.path.bufferAccessPath.tryStatic()?.let { staticPath ->
                        (where.ptr.block.calleeIdx to staticPath).takeIf {
                            it in prophecyMatch
                        }
                    } to buffersAsPath[where.ptr.block.calleeIdx]?.let { trans ->
                        /**
                         * Search through all of the [ABIAccessTranslation] generated for this call, and find the (unique)
                         * match for this [analysis.pta.abi.DecoderAnalysis.BufferAccessPath]; if there is a match, compile
                         * the access using [rewriteAccess].
                         */
                        trans.mapNotNull { toMatch ->
                            tryMatch(
                                sourceAccessPath = i.path.bufferAccessPath,
                                toMatch = toMatch.accessTranslation
                            ) {
                                rewriteAccess(
                                    lhs = i.output,
                                    sinkHandler = toMatch,
                                    l = it
                                )
                            }
                        }
                    }?.singleOrNull()
                }
            }
            /**
             * If neither optimization applies, skip!
             */
            if(prophecyKey == null && directAccess == null) {
                return@mapNotNull null
            }
            /**
             * Otherwise generate a thunk which mutably records the instrumentation to perform,
             * and record that the reads in CVL are matched by a read in the contract code (via the [ProphecyVars.hasConsumer]
             * flag).
             */
            {
                directRewrites[where.ptr] = Instrumentation(
                    output = i.output,
                    insertRead = directAccess,
                    prophecyKey = prophecyKey,
                    read = i
                )
                if(prophecyKey != null) {
                    prophecyMatch[prophecyKey]!!.hasConsumer = true
                }
            }
        }.sequential().forEach { thunk ->
            thunk()
        }

        /**
         * Now perform the rewrites
         */
        val p = c.toPatchingProgram()

        /**
         * For all reads in CVL, if there is a matched read in EVM, instrument an assume to the prophecy variable.
         */
        for((_, pv) in prophecyMatch) {
            if(!pv.hasConsumer) {
                continue
            }
            for((where, v) in pv.sources) {
                val ex = ExprUnfolder.unfoldPlusOneCmd("prophecyAssume", TACExpr.BinRel.Eq(v.asSym(), pv.prophecyVar.asSym())) {
                    TACCmd.Simple.AssumeCmd(it.s)
                }
                p.addAfter(where, ex)
            }
            p.addVarDecl(pv.prophecyVar)
        }
        /**
         * Now, rewrite the direct reads. Add the prophecy assumption and/or the direct read rewrite. If we do
         * the direct read rewrite, mark the Direct read as a source to garbage collect later.
         */
        val directReadsToGC = mutableSetOf<ABICodeFinder.Source>()
        for((k, inst) in directRewrites) {
            var toInsert = CommandWithRequiredDecls<TACCmd.Simple>()
            val readSource = ABICodeFinder.Source.Direct(inst.read.id)

            /**
             * We don't want to insert the rewrite within one of the ABI direct read abi ranges, as those
             * might be removed later. so find the end of the range containing this direct read (this
             * has to exist based on how we do abi range finding).
             */
            val insertionLocation = g.iterateBlock(k, excludeStart = true).firstOrNull {
                it.maybeAnnotation(ABIAnnotator.REGION_END)?.sources == setOf(readSource)
            } ?: continue
            if(inst.insertRead != null) {
                toInsert = toInsert.merge(inst.insertRead)
                toInsert = toInsert.merge(TACCmd.Simple.LabelCmd("Direct read instrumentation"))
                directReadsToGC.add(readSource)
            }
            if(inst.prophecyKey != null) {
                val prophecyVar = prophecyMatch[inst.prophecyKey]!!.prophecyVar
                toInsert = toInsert.merge(ExprUnfolder.unfoldPlusOneCmd("prophecyAssume", TACExpr.BinRel.Eq(prophecyVar.asSym(), inst.output.asSym())) {
                    TACCmd.Simple.AssumeCmd(it.s)
                })
            }
            p.insertAfter(insertionLocation.ptr, toInsert.cmds)
            p.addVarDecls(toInsert.varDecls)
        }
        /**
         * Now, apply the scalar rewrites generated previously
         */
        for((where, replacement) in scalarRewrites) {
            p.replaceCommand(where, listOf(replacement))
        }

        c.parallelLtacStream().mapNotNull {
            it.takeIf {
                it.maybeAnnotation(Inliner.CallStack.STACK_PUSH)?.calleeId in scalarRewriter.scalarConversionCode
            }
        }.sequential().forEach {
            check(it.ptr.block.calleeIdx == it.maybeAnnotation(Inliner.CallStack.STACK_PUSH)?.calleeId) {
                "Nonsense stack push at $it, disagreement about what call index this is"
            }
            p.addBefore(it.ptr, scalarRewriter.scalarConversionCode[it.ptr.block.calleeIdx]!!)
        }

        /**
         * Apply the patches, and then initialize the used prophecy variables with havoc
         */
        return p.toCode(c).prependToBlock0(prophecyMatch.mapNotNull { (_, pv) ->
            if(!pv.hasConsumer) {
                return@mapNotNull null
            }
            TACCmd.Simple.AssigningCmd.AssignHavocCmd(pv.prophecyVar)
        }).letIf(directReadsToGC.isNotEmpty()) {
            ABIOptimizations.gcABI(it, directReadsToGC)
        }
    }

    /**
     * Based on the [CVLMustAliasingAnalysis.primitiveReads] discovered in by the [mustAlias]
     * analysis over [g], record primitive reads in CVL might alias with direct values reads within a call to EVM,
     * as determined by [callSiteUses]. We record the [analysis.pta.abi.DecoderAnalysis.BufferAccessPath]
     * which represents the primitive value which aliases with the primitive read in CVL, and associate it with
     * a [ProphecyVars] for connecting up later.
     */
    private fun extractPrimitiveAliasingData(
        mustAlias: CVLMustAliasingAnalysis,
        g: TACCommandGraph,
        callSiteUses: TreapMap<APRoot, List<CallRoot>>,
        prophecyMatch: TreapMap.Builder<Pair<CallId, DecoderAnalysis.BufferAccessPath>, ProphecyVars>
    ) {
        for ((where, postStep) in mustAlias.primitiveReads) {
            val lhs = g.elab(where).maybeAnnotation(CVLCompiler.Companion.TraceMeta.ValueTraversal.META_KEY)!!.lhs

            /**
             * res, if non-null, indicates this (primitive) variable aliases with some value reachable from an [APRoot].
             */
            val res = postStep.getAliasInformation(lhs) ?: continue
            check(lhs is CVLCompiler.Companion.TraceMeta.ValueIdentity.TACVar)
            /**
             * If this [APRoot] is used in an external call, see if the value being observed here is used
             * in the external call.
             *
             * Note that this will *not* be the case if we have, e.g.
             * ```
             * SomeStruct a;
             * require(a.someField == 4);
             * f(a.someSubStruct);
             * ```
             *
             * search is a list of [CallRoot], uses of the same [APRoot] at a call-site
             */
            val search = callSiteUses[res.root] ?: continue
            outer@ for (s in search) {
                /**
                 * If this returns non-null, then the value being read here is reachable
                 * from the value being passed to the external call via the steps in rem.
                 *
                 * For example, if we have:
                 * ```
                 * SomeStruct a;
                 * require(a.someSubStruct.prim == 6);
                 * f(a.someSubStruct);
                 * ```
                 *
                 * Then we expect `rem` here to be `prim`, indicating that the primitive value being
                 * read here is reachable by traversing the field `prim` of the argument being passed to the external call
                 * to f.
                 */
                val rem = s.isPrefixFor(res) ?: continue

                /**
                 * Construct the [analysis.pta.abi.DecoderAnalysis.BufferAccessPath] which corresponds to traversing
                 * the steps given by [rem]. After traversing the steps in [rem] the resulting [analysis.pta.abi.DecoderAnalysis.BufferAccessPath]
                 * represents the path in the calldata buffer that is the location of the primitive value being read here.
                 * Continuing our example above, let's assume that `SomeSubStruct` is a dynamic type, and `prim` is at offset
                 * 64 within the struct, then it will contain:
                 * `Offset(64, Deref(Offset(0, Root)))`
                 *
                 * which gives the location of the prim field of the first argument to the external function.
                 * Remember, this prim field is also being read here, at the value traversal annotation, and thus we have
                 * a candidate for a prophecy variable.
                 */
                var it: DecoderAnalysis.BufferAccessPath = DecoderAnalysis.BufferAccessPath.Offset(
                    base = DecoderAnalysis.BufferAccessPath.Root,
                    offset = s.offset
                )

                /**
                 * The traversal of [rem] requires tracking the EVM type being traversed as well, as we need this information
                 * in the struct case to compute the field offsets.
                 */
                var ty = s.ty as EVMTypeDescriptor
                var i = 0
                while (i < rem.size) {
                    if (ty.isDynamicType()) {
                        it = DecoderAnalysis.BufferAccessPath.Deref(parent = it)
                    }
                    when (val st = rem[i]) {
                        is CVLCompiler.Companion.TraceMeta.CVLAccessPathStep.ArrayElem -> {
                            it = DecoderAnalysis.BufferAccessPath.Offset(
                                base = DecoderAnalysis.BufferAccessPath.ArrayElemOf(
                                    parent = it,
                                    indices = setOf(res.idxValuation[st.i]!!.asTACSymbol())
                                ),
                                offset = BigInteger.ZERO
                            )
                            if (ty is EVMTypeDescriptor.DynamicArrayDescriptor) {
                                ty = ty.elementType
                                // XXX(jtoman): try to support static arrays...
                            } else {
                                continue@outer
                            }
                        }

                        CVLCompiler.Companion.TraceMeta.CVLAccessPathStep.ArrayLength -> {
                            it = DecoderAnalysis.BufferAccessPath.Offset(
                                offset = BigInteger.ZERO,
                                base = it
                            )
                            if (ty !is EVMTypeDescriptor.DynamicArrayDescriptor) {
                                continue@outer
                            }
                            ty = ty.lengthType
                        }

                        is CVLCompiler.Companion.TraceMeta.CVLAccessPathStep.Field -> {
                            var offs = BigInteger.ZERO
                            if (ty !is EVMTypeDescriptor.EVMStructDescriptor) {
                                continue@outer
                            }
                            var found = false
                            lateinit var fieldTy: EVMTypeDescriptor
                            for (f in ty.fields) {
                                if (f.fieldName == st.f) {
                                    found = true
                                    fieldTy = f.fieldType
                                    break
                                } else {
                                    offs += f.fieldType.sizeAsEncodedMember()
                                }
                            }
                            if (!found) {
                                continue@outer
                            }
                            if (it is DecoderAnalysis.BufferAccessPath.Offset) {
                                it = it.copy(offset = it.offset + offs)
                            } else {
                                it = DecoderAnalysis.BufferAccessPath.Offset(
                                    offset = offs, base = it
                                )
                            }
                            ty = fieldTy
                        }
                    }
                    i++
                }
                /**
                 * Now that we're here, we have the [analysis.pta.abi.DecoderAnalysis.BufferAccessPath]
                 * which, if directly read, must alias with
                 */
                prophecyMatch.getOrPut(s.id to it) {
                    ProphecyVars(TACKeyword.TMP(Tag.Bit256, "Prophecy"))
                }.sources.put(where, lhs.t)
            }
        }
    }

    /**
     * Based on the external binds discovered by [mustAlias], process that information into [scalarToArg] (which
     * describes how to transform a read of scalarized callindex k in call id n), [buffersAsPath] (which
     * describes how to transform a direct calldata reads in the given call id to direct accesses over CVL values),
     * and [callSiteUses] (which maps [APRoot] to their sub-objects use at callsites)
     */
    private fun extractExternalArgData(
        mustAlias: CVLMustAliasingAnalysis,
        g: TACCommandGraph,
        scalarToArg: TreapMap.Builder<CallId, TreapMap<BigInteger, (TACSymbol.Var) -> CommandWithRequiredDecls<TACCmd.Simple>>>,
        buffersAsPath: TreapMap.Builder<CallId, MutableList<ABIAccessRewriter>>,
        callSiteUses: TreapMap.Builder<APRoot, List<CallRoot>>
    ) {
        for ((where, st) in mustAlias.externalBinds) {
            val eb = g.elab(where).maybeAnnotation(CVLCompiler.Companion.TraceMeta.ExternalArg.META_KEY)!!
            if (eb.s is CVLCompiler.Companion.TraceMeta.ValueIdentity.TACVar) {
                eb.targetType.converterFrom(eb.sourceType, ToVMContext.DirectPassing.getVisitor()).resultOrNull()?.let {
                    /**
                     * Generate a binding for the scalar argument being passed here, the callback here moves the argument, which is the external bind's tac variable field,
                     * to the generator's argument via the [spec.converters.EVMMoveSemantics].
                     */
                    scalarToArg[eb.callId] = scalarToArg.getOrDefault(
                        eb.callId,
                        treapMapOf()
                    ) + ((eb.rootOffset + DEFAULT_SIGHASH_SIZE) to { v: TACSymbol.Var ->
                        it.convertTo(
                            fromVar = eb.s.t,
                            toVar = v,
                            cb = { it }
                        ).uncheckedAs()
                    })
                }
            }
            /**
             * Find which [APRoot] this argument aliases.
             */
            val ap = st.getAliasInformation(eb.s) ?: continue
            val typeAtCall = st.type[ap.root]?.reachableType(ap.ap, 0) ?: continue
            // sanity checking
            if (!typeAtCall.convertibleToVMType(eb.targetType, ToVMContext.ArgumentPassing).isResult()) {
                continue
            }
            /**
             * If there are data fields, then this is a reference type. register all [ABIAccessRewriter]s generated
             * via [traverseType]
             */
            eb.fields?.let {
                buffersAsPath.getOrPut(eb.callId) {
                    mutableListOf()
                }.addAll(
                    traverseType(
                        rootName = eb.s.toString(),
                        rootOffset = eb.rootOffset,
                        fieldMap = it,
                        targetTy = eb.targetType as EVMTypeDescriptor,
                        sourceTy = eb.sourceType
                    )
                )
            }

            /**
             * record this binding as a use of the root at a callsite
             */
            callSiteUses[ap.root] = callSiteUses.getOrDefault(ap.root, listOf()) + CallRoot(
                idxValuation = ap.idxValuation,
                offset = eb.rootOffset,
                id = eb.callId,
                paths = ap.ap,
                ty = eb.targetType
            )
        }
    }
}
