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

package instrumentation

import algorithms.dominates
import analysis.*
import analysis.icfg.ExpressionSimplifier
import analysis.numeric.linear.*
import analysis.worklist.SimpleWorklist
import bridge.ContractInstanceInSDC
import com.certora.collect.*
import log.*
import normalizer.ConstructorBytecodeNormalizer
import scene.*
import vc.data.*
import java.math.BigInteger
import java.util.stream.Collectors
import datastructures.stdcollections.*
import spec.CVLCompiler
import spec.cvlast.CVLType
import spec.cvlast.typedescriptors.FromVMContext
import utils.*
import vc.data.tacexprutil.ExprUnfolder

private val logger = Logger(LoggerTypes.INSTRUMENTATION)

/**
 * Instruments constructor code which potentially writes immutables via its *own* bytecode
 * instrumentation (whoa). As an over-approximation, we put havocs of all immutables known to exist in the contract at the
 * root of the constructor, and instrument actual immutable initialization on a best effort basis.
 */
object ImmutableInstrumenter : ConstructorBytecodeNormalizer {
    fun instrument(prog: CoreTACProgram, src: ContractInstanceInSDC) : CoreTACProgram {
        // no immutables? nothing to do
        if(src.immutables.isEmpty()) {
            return prog
        }
        val root = prog.analysisCache.graph.roots.singleOrNull() ?: return prog
        val simplifier = ExpressionSimplifier(prog.analysisCache.graph, preservedNames = emptySet())
        fun TACSymbol.toInt(p: CmdPointer) = simplifier.simplify(this, p, true)
            .let { (it as? TACExpr.Sym.Const)?.s?.value }
            ?.takeIf {
                it.bitLength() < 32
            }?.let(BigInteger::intValueExact)
        /**
         * Find the (unique) instance of a copy of the contracts deployed bytecode from codedata of the
         * constructor.
         */
        val (where, writeOffs) = prog.analysisCache.graph.commands.mapNotNull {
            /*
             find all bytelongcopies...
             */
            it.maybeNarrow<TACCmd.Simple.ByteLongCopy>()
        }.filter {
            /*
            from codedata into memory...
             */
            it.cmd.srcBase.meta.contains(TACMeta.CODEDATA_KEY) && it.cmd.dstBase == TACKeyword.MEMORY.toVar()
        }.mapNotNull {
            /*
             * Where the source, destination, and length are all constant integers
             */
            val srcOffs = it.cmd.srcOffset.toInt(it.ptr) ?: return@mapNotNull null
            val dstOffs = it.cmd.dstOffset.toInt(it.ptr)?.toLeft() ?: it.cmd.dstOffset.toRight()
            val len = it.cmd.length.toInt(it.ptr) ?: return@mapNotNull null
            // two characters per byte
            val startStringOffset = srcOffs * 2
            val stringLen = len * 2
            /*
               If this doesn't seem to be a valid string in the constructor's bytecode, bail
             */
            if(stringLen + startStringOffset > src.constructorBytecode.length) {
                return@mapNotNull null
            }
            /*
              Get the bytecode that we are copying, normalizing for cbor and finders
             */
            val toDeploy = src.constructorBytecode.substring(startStringOffset, stringLen + startStringOffset).stripCbor().sanitizeFinders()
            /*
              The bytecode solidity says we deploy (again, normalizing)
             */
            val srcCode = src.bytecode.stripCbor().sanitizeFinders()
            if(srcCode != toDeploy) {
                return@mapNotNull null
            }
            /*
              If they are equal, then we have found our deployed bytecode copy, which is known to copy to a constant
              offset dstOffs in memory
             */
            it to dstOffs
        }.toList().singleOrNull() ?: return prog
        fun CmdPointer.dominates(other: CmdPointer) = prog.analysisCache.domination.dominates(this, other)
        /*
          Compute the linear invariants for bytestores in the the blocks dominated by the long copy.
          We use this to extract a symbolic description of the write location, and try to relativize this write
          to the (symbolic) longcopy destination. NB: this is run lazily, so if the constructor always uses constant offset
          we don't pay for the overhead of running this analysis. That said, the bytelongcopy of the constructor code
          usually comes near the very very end of the constructor, so running this will be cheap in practice.

          XXX(jtoman) this *very* much assumes that we aren't doing something *truly* bizarre and overwriting the code
          in memory, and thus a constant offset write that happens to correspond to a immutable offset is actually doing something
          else. In lieu of *actually* checking this property (annoying!) we see if we can find a write for *every* immutable
          offset we expect to see, which gives some confidence that the constructor is doing what we expect.
         */
        val toSearch = prog.analysisCache.domination.dominatedOf(where.ptr.block)
        val linInvAtWrites by lazy {
            val toRet = treapMapBuilderOf<CmdPointer, LinearInvariants>()
            val graph = prog.analysisCache.graph
            val sem = GlobalInvariantAnalysisSemantics(maxTerms = 2)
            var linearInv = treapSetOf<LinearEquality>()
            graph.iterateBlock(where.ptr, excludeStart = true).forEach {
                if(it.cmd is TACCmd.Simple.AssigningCmd.ByteStore) {
                    toRet[it.ptr] = linearInv
                }
                linearInv = sem.step(it, linearInv)
            }
            val blockPreState = graph.succ(where.ptr.block).retainAll {
                it in toSearch
            }.associateWith {
                linearInv
            }.toTreapMap().builder()
            SimpleWorklist.iterateWorklist(blockPreState.keys) { curr, nxt ->
                var st = blockPreState[curr]!!
                graph.elab(curr).commands.forEach { lc ->
                    if(lc.cmd is TACCmd.Simple.AssigningCmd.ByteStore) {
                        toRet[lc.ptr] = st
                    }
                    st = sem.step(lc, st)
                }
                graph.succ(curr).retainAll { succ ->
                    succ in toSearch
                }.forEach { succ ->
                    val newState = blockPreState[succ]?.fastJoin(st) ?: st
                    if(newState != blockPreState[succ]) {
                        blockPreState[succ] = newState
                        nxt.add(succ)
                    }
                }
            }
            toRet.build()
        }

        /*
         For every immutable...
         */
        val toInstr: Map<TACSymbol.Var, Set<LTACCmdView<TACCmd.Simple.AssigningCmd.ByteStore>>> = src.immutables.mapNotNull { ref ->
            if(ref.value != null) {
                return@mapNotNull null
            }
            /*
              Compute the symbol we are initializing, and the offset in memory (computed as bytecode offset + dest offset)
              that corresponds to that initialization
             */
            writeOffs.mapBoth({ it + ref.offset }, { outputS ->
                LinearTerm.lift(TACExpr.Vec.Add(ref.offset.asTACExpr, outputS.asSym()))
            }) to TACSymbol.immutable(ref.varname, src.name)
        }.stream().map { (offs, expect: TACSymbol.Var) ->
            /*
              Find the (unique) write to the offset location [offs] computed to initialize [expect]. This must
              be dominated by the copy of code data, and must be a write to a constant location equal to offs.
             */
            toSearch.flatMap {
                prog.analysisCache.graph.elab(it).commands.mapNotNull { cand ->
                    cand.maybeNarrow<TACCmd.Simple.AssigningCmd.ByteStore>()?.takeIf { write ->
                        write.cmd.base == TACKeyword.MEMORY.toVar() && offs.toValue({ expectedOffs ->
                            write.cmd.loc.toInt(write.ptr) == expectedOffs
                        }, r@{ term ->
                            if(term == null) {
                                return@r false
                            }
                            val baseSym = (term.terms.singleOrNull()?.first as? LVar.PVar)?.v ?: return@r false
                            if(baseSym !in prog.analysisCache.gvn.findCopiesAt(write.ptr, where.ptr to baseSym)) {
                                return@r false
                            }
                            val inv = linInvAtWrites[write.ptr] ?: return@r false
                            inv implies {
                                term `=` !write.cmd.loc
                            }
                        })
                    }
                }
            }.singleOrNull()?.let {
                (it to expect)
            }
        /* monadic collector ensures that if *any* immutable write isn't resolved correctly, none are */
        }.collect(MonadicCollector(
            Collectors.groupingBy({
                it.second
            }, Collectors.mapping({it.first}, Collectors.toSet()))
        )) ?: return prog
        fun SimplePatchingProgram.addImmutableHavoc() {
            src.immutables.mapTo(mutableSetOf()) {
                TACSymbol.immutable(it.varname, owningContract = src.name)
            }.also {
                this.addVarDecls(it)
            }.map {
                TACCmd.Simple.AssigningCmd.AssignHavocCmd(lhs = it)
            }.let {
                addBefore(root.ptr, it)
            }
        }
        if(toInstr.isEmpty()) {
            return prog.patching {
                it.addImmutableHavoc()
            }
        }
        return prog.patching {p ->
            p.addImmutableHavoc()
            /*
             For each "group" of writes for the same immutable
             */
            toInstr.forEach { (which, writes) ->
                writes.first().let { tgt ->
                    /*
                     Instrument the "first" such write (chosen arbitrarily) to initialize the symbol

                     Again, we are begin *very* optimistic here: we assume all writes to the immutable locations
                     are actually the same value, that there is no ordering or dependency etc.
                     */
                    p.replaceCommand(tgt.ptr,
                        listOf(tgt.cmd, TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            lhs = which,
                            rhs = tgt.cmd.value
                        ))
                    )
                    p.addVarDecl(which)
                }
            }
        }
    }

    /**
     * For [m] (which is assumed to be a constructor), add initialization of the constant values as specified in
     * immutable linking information. Most of this behavior is given in [getImmutableInitializer], this just applies
     * this after contract cloning
     */
    fun instrumentConstants(scene : IScene, m: ITACMethod)  {
        val code = m.code as CoreTACProgram
        if(m.getContainingContract() is IClonedContract) {
            return
        }
        val parent = (m.getContainingContract() as? IContractWithSource) ?: return
        val init = getImmutableInitializer(parent, scene)
        if(init.cmds.isEmpty()) {
            return
        }
        code.toPatchingProgram().let { p ->
            p.addVarDecls(init.varDecls)
            code.parallelLtacStream().mapNotNull {
                it.maybeNarrow<TACCmd.Simple.ReturnCmd>()
            }.sequential().forEach {
                p.addBefore(
                    it.ptr, init.cmds
                )
            }
            m.updateCode(p)
        }
    }

    fun getImmutableInitializer(c: IContractWithSource, s: IScene): CommandWithRequiredDecls<TACCmd.Simple> {
        return c.src.immutables.filter {
            it.value != null
        }.groupBy({
            TACSymbol.immutable(it.varname, (c as IContractClass).name)
        }, {
            it.value!!
        }).entries.mapNotNull {
            it.key `to?` it.value.uniqueOrNull()
        }.associateTo(mutableMapOf()) { it }.let {
            val (assignExpCmds, contractAddrs) = it.map { (lhs, immutableConstant) ->
                // if the immutable constant is a link, its values will match a contract instanceId. In this case
                // we'll have to use that contract's symbolic address. If the immutable is just a plain contant, the
                // contractAddr will be null
                val contractAddr = s.getContractOrNull(immutableConstant)?.addressSym as? TACSymbol.Var
                val rhs = contractAddr ?: immutableConstant.asTACSymbol()

                val cmd = TACCmd.Simple.AssigningCmd.AssignExpCmd(lhs = lhs, rhs = rhs.asSym())

                Pair(cmd, contractAddr)
            }.unzip()
            CommandWithRequiredDecls(assignExpCmds.toList(), it.keys + contractAddrs.filterNotNull())
        }
    }

    fun constrainNonconstImmutables(
        c: IContractWithSource,
        cvlCompiler: CVLCompiler
    ): CommandWithRequiredDecls<TACCmd.Spec> {
        return c.src.immutables.filter {
            it.value == null
        }.distinctBy {
            it.varname
        }.map {
            TACSymbol.immutable(it.varname, (c as IContractClass).name) to it
        }.map { (immutableVar, immutReference) ->
            val type = immutReference.type
            // currently solidity immutables are up to a size of 1 word or 256 bits.
            // we do best effort of detecting the correct bitwidth
            val pureType = type.toVMTypeDescriptor().getPureTypeToConvertTo(FromVMContext.ReturnValue).resultOrNull()
            if (pureType == null) {
                logger.warn { "Could not infer value type of immutable reference ${immutReference.varname}" }
                CommandWithRequiredDecls<TACCmd.Spec>()
            } else if (pureType is CVLType.PureCVLType.Primitive.Bool) {
                // I'm scared of changing ensureBitWidth to limit booleans to 0-1 range, there's even a message there
                ExprUnfolder.unfoldToSingleVar("inBounds", TACExprFactUntyped {
                    LAnd(
                        Le(BigInteger.ZERO.asTACExpr, immutableVar.asSym()),
                            Le(immutableVar.asSym(), BigInteger.ONE.asTACExpr)
                    )
                }).let {
                    CommandWithRequiredDecls(
                        it.cmds + TACCmd.Simple.AssumeCmd(it.e.s),
                        it.newVars + immutableVar
                    )
                }
            } else {
                cvlCompiler.ensureBitWidth(pureType, immutableVar)
            }
        }.let(CommandWithRequiredDecls.Companion::mergeMany)
    }

    fun establishEquivalenceOfExtensionContractImmutables(
        c: IContractWithSource,
        cvlCompiler: CVLCompiler
    ): CommandWithRequiredDecls<TACCmd.Spec> {
        val srcImmutables = c.src.immutables.filter { it.value == null }
        val extensionImmutables = c.src.extensionContracts
            .map { cvlCompiler.scene.getContract(it.extension.getAddressAsInteger()) }
            .flatMap { extension ->
                check(extension is IContractWithSource) { "extension contracts should have a src" }
                extension.src.immutables.map { extension to it }
            }

        val srcToExtensions = extensionImmutables
            .filter { it.second.varname in srcImmutables.map { it.varname } }
            .groupBy { it.second.varname }
            .mapKeys { (name, _) -> srcImmutables.find { it.varname == name }!! }

        val (commands, decls) = srcToExtensions.map { (srcImmut, extensions) ->
            if (extensions.size > 1) {
                if (extensions.unzip().second.mapToSet { it.value }.size != 1) {
                    throw CertoraException(
                        CertoraErrorType.CONTRACT_EXTENSION,
                        "several extensions have the same immutable ${srcImmut.varname} with different values ${extensions.unzip().second.mapToSet { it.value }}"
                    )
                }
            }
            val (extensionC, extensionImmut) = extensions.first() // doesn't matter which, since we verified that the all have the same value
            if (srcImmut.type != extensionImmut.type || srcImmut.length != extensionImmut.length) {
                throw CertoraException(
                    CertoraErrorType.CONTRACT_EXTENSION,
                    "extension contract ${extensionC.name} has an immutable ${extensionImmut.varname} that is does not " +
                        "match the immutable with the same name in base contract ${c.src.name}"
                )
            }
            val cond = TACKeyword.COND.toVar().toUnique("!")
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = cond,
                    rhs = cvlCompiler.exprFact {
                        TACSymbol.immutable(srcImmut.varname, (c as IContractClass).name).asSym() eq
                            TACSymbol.immutable(extensionImmut.varname, extensionC.name).asSym()
                    }
                ),
                TACCmd.Simple.AssumeCmd(cond)
            ) to cond
        }.unzip()
        return CommandWithRequiredDecls(
            commands.flatten(),
            decls
        )
    }
}
