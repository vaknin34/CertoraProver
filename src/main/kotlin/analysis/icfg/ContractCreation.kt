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

import analysis.*
import config.Config
import config.ReportTypes
import datastructures.stdcollections.*
import scene.IClonedContract
import scene.IDynamicScene
import tac.NBId
import tac.Tag
import utils.*
import vc.data.*
import vc.data.tacexprutil.ExprUnfolder
import verifier.ChainedMethodTransformers
import verifier.ContractUtils
import verifier.MethodToCoreTACTransformer
import java.math.BigInteger

/**
 * Actually performs the dynamic contract creation instrumentation. Based on the create
 * summaries inserted by the [CallGraphBuilder], this code clones the resolved contracts
 * up to the bound specified in [Config.DynamicCreationBound], instruments the create
 * calls to select from one of these pre-generated contracts, and then inlines the constructor
 * code (if necessary).
 */
object ContractCreation {
    private val creationBound = Config.DynamicCreationBound.get()

    fun extendScene(scene: IDynamicScene, contractOracle: IConstructorOracle) {
        /**
         * The set of contracts we want to clone
         */
        val toClone = mutableSetOf<BigInteger>()

        /**
         * For each contract in the above, give the list of cloned contracts (populated after the loop below)
         */
        val cloned = mutableMapOf<BigInteger, List<IClonedContract>>()

        /**
         * For each method, within that method get the locations within that method that instantiate a contract.
         * The first element of the codomain of the inner map indicates whether the instantiation is via an explicit "prototype"
         * configuration, or a "proper" constructor call. The second element is the address of the (base) contract.
         *
         * We explicitly group these creation by method, because each instantiation requires instrumenting the code
         * of the containing method, and so all those changes need to be applied in one go (for caching and perf reasons)
         */
        val resolved = mutableMapOf<MethodRef, MutableMap<LTACCmd, Pair<Boolean, BigInteger>>>()
        val hasResolvedCallViaImmutable = mutableSetOf<BigInteger>()
        scene.getContracts().forEach { contract ->
            contract.getDeclaredMethods().forEach { meth ->
                if((meth.code as CoreTACProgram).parallelLtacStream().mapNotNull {
                    it.maybeAnnotation(Inliner.CallStack.STACK_PUSH)
                }.anyMatch {
                    it.summary?.callTarget?.any { it is CallGraphBuilder.CalledContract.FullyResolved.ImmutableReference} == true
                }) {
                    hasResolvedCallViaImmutable.add(contract.instanceId)
                }
                meth.commands.mapNotNull {
                    it.maybeNarrow<TACCmd.Simple.SummaryCmd>()
                }.filter {
                    it.cmd.summ is CreateSummary
                }.mapNotNull {
                    val summ = it.cmd.summ as CreateSummary
                    val resolveTo = contractOracle.resolve(summ.constructorSig) ?: return@mapNotNull null
                    it.wrapped.lift(meth) to resolveTo
                }.forEach { (where, res) ->
                    resolved.computeIfAbsent(where.method) {
                        mutableMapOf()
                    }[where.toLTAC()] = res.isProxy to res.prototypeAddress
                    toClone.add(res.prototypeAddress)
                }
            }
        }
        for(srcAddr in toClone) {
            if(srcAddr in hasResolvedCallViaImmutable) {
                throw IllegalArgumentException("Cannot link delegate calls via immutables on contracts that are also cloned, the" +
                        "resolution behavior is ambiguous")
            }
            val newContracts = (0 until creationBound).map { ind ->
                scene.cloneContract(srcAddr).also {
                    /**
                     * The "nonce" here has no bearing on the actual nonce defined by EVM, but rather
                     * provides an idea of "which number clone am I"
                     */
                    it.createdContractInstance = ind
                }
            }
            cloned[srcAddr] = newContracts
        }
        val transformer = ChainedMethodTransformers(listOf(MethodToCoreTACTransformer(ReportTypes.DYNAMIC_CREATION) tr@{ meth ->
            val code = meth.code as CoreTACProgram
            val toInst = resolved[meth.toRef()] ?: return@tr code
            val patch = code.toPatchingProgram()
            for((where, addr) in toInst) {
                val proxy = addr.first
                instantiateCreate(
                    scene, code, patch, where.narrow(), cloned[addr.second]!!, proxy
                )
            }
            patch.toCode(code)
        }))
        scene.mapContractMethodsInPlace("static_alloc") tr@{ _, meth ->
            ContractUtils.transformMethodInPlace(meth, transformer)
        }
    }

    private fun instantiateCreate(
        scene: IDynamicScene,
        src: CoreTACProgram,
        p: SimplePatchingProgram,
        create: LTACCmdView<TACCmd.Simple.SummaryCmd>,
        targetContracts: List<IClonedContract>,
        isPrototype: Boolean
    ) {
        val createSumm = create.cmd.summ as CreateSummary

        /**
         * Each create summary corresponds to some command that generates the address of the created contract, find that command
         */
        val createCmd = src
            .parallelLtacStream()
            .filter {
                it.cmd.meta.find(TACMeta.CONTRACT_CREATION) == createSumm.createId &&
                    ((it.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd &&
                         it.cmd.rhs is TACExpr.SimpleHash &&
                         it.cmd.rhs.hashFamily.isContractCreation) ||
                        (it.cmd is TACCmd.Simple.AssigningCmd.AssignSimpleSha3Cmd && TACMeta.CREATE2_COMPUTATION in it.cmd.meta))
            }.findAny()
            .toNullable()
            ?.narrow<TACCmd.Simple.AssigningCmd>()
            ?: return

        // symbol holding computed address, if CREATE2 was used. Otherwise - null
        val computedAddress = if(TACMeta.CREATE2_COMPUTATION in createCmd.cmd.meta || Config.UseComputedAddressForCreate.get()) {
            createCmd.cmd.lhs
        } else {
            null
        }

        /**
         * The address of the contract (we expect all clones here to share the same source address)
         */
        val srcContract = targetContracts.map { it.sourceContractId }.uniqueOrNull() ?: error("Inconsistent clones")

        /**
         * The following generates the contract address resolution instrumentation.
         * It does so both for instances created using CREATE and CREATE2. If we are creating an "instance"
         * of an address A, and putting the resulting address in newAddressLhs, then we generate:
         *
         * ```
         *  createdAddress = <compute if CREATE2 or UseComputedAddressForCreate, otherwise set to null>
         *   if(tacContractsCreated[A] == 0) {
         *       A$Clone0.addressSym = ite(createdAddress != null, create2Address, A$Clone0.addressSym)
         *       newAddressLhs = A$Clone0.addressSym;
         *       tacContractsCreated[A] = 1
         *       createdAddresses[create2Address] = 1
         *   } else if(tacContractsCreated[A] == 1) {
         *       A$Clone1.addressSym = ite(createdAddress != null, create2Address, A$Clone1.addressSym)
         *       newAddressLhs = A$Clone1.addressSym;
         *       tacContractsCreated[A] = 1
         *       createdAddresses[create2Address] = 2
         *   } ... else if(tacContractsCreated[A] == n-1) {
         *       A$Clonek.addressSym = ite(createdAddress != null, create2Address, A$Clonek.addressSym)
         *       newAddressLhs = A$Clonek.addressSym;
         *       tacContractsCreated[A] = n
         *       createdAddresses[create2Address] = 1
         *   } else {
         *       re, "Too many instances of A";
         *       lhs = havoc; // unreachable
         *   }
         * ```
         * where `n` in the above is the dynamic creation bound
         *
         * NB we do *not* handle colliding addresses, that is handled in the decompiler, see [EthereumVariables.simplifyCreate] et al
         */
        val succ = p.splitBlockAfter(createCmd.ptr)

        val newAddressLhs = createCmd.cmd.lhs

        val elseBlock = p.addBlock(succ, listOf(TACCmd.Simple.AssertCmd(
            o = TACSymbol.False, "Dynamic contract creation bound hit when cloning 0x${srcContract.toString(16)}: try increasing the value of ${Config.DynamicCreationBound.userFacingName()}"
        ), TACCmd.Simple.AssigningCmd.AssignHavocCmd(
            lhs = newAddressLhs,
        ), TACCmd.Simple.JumpCmd(succ)))

        val instrumentationVar = TACKeyword.TMP(Tag.Bit256, "!instanceId").toUnique("!")
        fun getInstanceIdInstrumentation(i: Int) : CommandWithRequiredDecls<TACCmd.Simple>? {
            if(isPrototype) {
                return null
            }
            return CommandWithRequiredDecls(
                listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = instrumentationVar,
                        rhs = i.asTACExpr
                    )
                ),
                instrumentationVar
            )
        }
        fun assumeNoCollision(forTarget: IClonedContract) : CommandWithRequiredDecls<TACCmd.Simple>? {
            if(computedAddress == null) {
                return null
            }
            return scene.getNonPrecompiledContracts().mapNotNull {
                if(it.instanceId == forTarget.instanceId) {
                    return@mapNotNull null
                }
                ExprUnfolder.unfoldPlusOneCmd("noOverlapAssume", with(TACExprFactUntyped) {
                    LNot(Eq((it.addressSym as TACSymbol).asSym(), computedAddress.asSym()))
                }) {
                    TACCmd.Simple.AssumeCmd(it.s)
                }.merge(it.addressSym as TACSymbol).merge(computedAddress)
            }.let(CommandWithRequiredDecls.Companion::mergeMany)
        }


        val allocStart = targetContracts.foldIndexed(elseBlock) { iterationKey: Int, elseDest: NBId, tgtAddr: IClonedContract ->
            val ind = tgtAddr.createdContractInstance // AKA, what value should we compare tacContractsCreated[A] to
            /*
               temp for tacContractsCreated[A]
             */
            val createdCount = TACKeyword.TMP(Tag.Bit256, "${srcContract.toString(16)}!currCount").toUnique("!")
            val creationCountCmp = TACKeyword.TMP(Tag.Bool, "!creationCountCmp").toUnique("!")

            /**
             * The body of the instantiation block.
             */
            val staticAlloc = MutableCommandWithRequiredDecls<TACCmd.Simple>().also {
                it.extend(CommandWithRequiredDecls(
                    listOfNotNull(
                        /**
                         * IFF used with CREATE2:
                         * address of tgtAddr (a clone of A) = create2Address
                         */
                        if (computedAddress != null) {
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = tgtAddr.addressSym as TACSymbol.Var,
                                rhs = computedAddress.asSym()
                            )
                        } else null,
                        /**
                         * newAddressLhs = the address of tgtAddr (a clone of A)
                         */
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            lhs = newAddressLhs,
                            rhs = (tgtAddr.addressSym as TACSymbol).asSym()
                        ),
                        TACCmd.Simple.WordStore(
                            /**
                             * "Increment" the value of tacContractsCreated
                             */
                            base = TACKeyword.CONTRACT_COUNT.toVar(),
                            loc = srcContract.asTACSymbol(),
                            value = (ind + 1).asTACSymbol()
                        )
                    ),
                    setOfNotNull(
                        newAddressLhs,
                        TACKeyword.CONTRACT_COUNT.toVar(),
                        tgtAddr.addressSym as TACSymbol.Var,
                        computedAddress
                    )
                ))
            }
            getInstanceIdInstrumentation(iterationKey)?.let(staticAlloc::extend)
            assumeNoCollision(tgtAddr)?.let(staticAlloc::extend)
            if(isPrototype) {
                /**
                 * Contracts created via the prototype should still have their state initialized to 0.
                 *
                 * XXX(jtoman): what about immutables? those are technically derived from the source contract??? Is
                 * this a use case we care about?
                 *
                 * (for non prototype contracts, we put this initialization in the constructor inlining code)
                 */
                staticAlloc.extend(Inliner.initializeFreshStorage(
                    tgtAddr
                ))
            }

            staticAlloc.extend(
                TACCmd.Simple.JumpCmd(succ)
            )
            val staticAllocBlock = p.addBlock(elseDest, staticAlloc.toCommandWithRequiredDecls())
            val comparisonBlock = CommandWithRequiredDecls(listOf(
                // genesisNonce = tacContractsCreated[A]
                TACCmd.Simple.AssigningCmd.WordLoad(
                    lhs = createdCount,
                    base = TACKeyword.CONTRACT_COUNT.toVar(),
                    loc = srcContract.asTACSymbol()
                ),
                // nonceCmp = genesisNonce == ind
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = creationCountCmp,
                    rhs = TACExpr.BinRel.Eq(
                        createdCount.asSym(),
                        TACSymbol.lift(ind).asSym()
                    )
                ),
                // if genesisNonce == ind then staticAllocBlock else elseDest
                TACCmd.Simple.JumpiCmd(
                    cond = creationCountCmp,
                    dst = staticAllocBlock,
                    elseDst = elseDest
                )
            ), setOf(
                TACKeyword.CONTRACT_COUNT.toVar(),
                createdCount,
                creationCountCmp
            ))
            p.addBlock(elseDest, comparisonBlock)
        }

        /* Jump to the dispatcher code */
        p.replaceCommand(createCmd.ptr, listOf(createCmd.cmd, TACCmd.Simple.JumpCmd(allocStart)))
        updateCreateReferences(src, createSumm, p, srcContract)

        if(isPrototype) {
            /*
              This is the call to create(), NOT the call to the built in function create (which we replaced above)
             */
            p.replaceCommand(create.ptr, listOf(
                TACCmd.Simple.LabelCmd("Simplified out invocation of create()")
            ))
            return
        }

        /**
         * This is effectively a specialized dispatcher that switches over the address of the newly chosen contract,
         * and inlines the (specialized) constructor implementation.
         *
         * However, we do "hijack" the CONSTRUCTOR_RETURN variable to instead use the value returned from the constructor
         * call (assiged in the constructor inlining, see [Inliner.prepareConstructor]). It also generates code that reverts the contract counts if the constructor
         * fails. This is *technically* redundant if the constructors caller always immediately reverts (which also resets
         * the counts), but better safe than sorry.
         *
         * This is why we split up constructor inlining and address generation; all of the revert handling/return code
         * handling logic comes after the callcore, which could be in a *different* part of the code from the
         * actual call to create (although this is unlikely, but better to not rely on the current behavior of the
         * decompiler!)
         *
         * Thus, the result of this instrumentation is:
         * ```
         * if(create.to == A$Clone1) {
         *    CONSTRUCTOR_RETURN = A$Clone1.constructor();
         * } else if(create.to = A$Clone2) {
         *    CONSTRUCTOR_RETURN = A$Clone2.constructor();
         * } ... else { assert false, "impossible"; }
         * tacContractsCreated[A] = tacContractsCreated[A] - (CONSTRUCTOR_RETURN == 0 ? 1 : 0)
         * ```
         *
         * where the inlining process ensures that CONSTRUCTOR_RETURN is set to 0 if the constructor reverts, whereby
         * the contract is "unallocated" by way of decrementing the count associated with A.
         */
        val callSucc = p.splitBlockAfter(create.ptr)
        val sink = p.addBlock(callSucc, CommandWithRequiredDecls(listOf(
            TACCmd.Simple.AssertCmd(
                o = TACSymbol.False,
                "Impossible"
            ),
            TACCmd.Simple.JumpCmd(callSucc)
        )))
        val returnCode = TACKeyword.CONSTRUCTOR_RETURN.toVar(callIndex = create.ptr.block.calleeIdx)
        /*
          "compile" tacContractsCreated[A] - (CONSTRUCTOR_RETURN == 0 ? 1 : 0) to
          tmp!createFailed = CONSTRUCTOR_RETURN == 0
          tmp!dec = tmp!createFailed ? 1 : 0
          tmp!prev = tacContractsCreated[A]
          tmp!newAmount = tmp!prev - tmp!dec
          tacContractsCreated[A] = tmp!newAmount
         */
        val countFixup = TACKeyword.TMP(Tag.Bit256, "!output").let { currCount ->
            CommandWithRequiredDecls(TACCmd.Simple.AssigningCmd.WordLoad(
                lhs = currCount,
                base = TACKeyword.CONTRACT_COUNT.toVar(),
                loc = srcContract.asTACSymbol()
            ), setOf(currCount, TACKeyword.CONTRACT_COUNT.toVar(), returnCode)).merge(
                ExprUnfolder.unfoldPlusOneCmd("countAdj", with(TACExprFactUntyped) {
                    Ite(
                        i = Eq(returnCode.asSym(), TACExpr.zeroExpr),
                        t = Sub(currCount.asSym(), 1.asTACExpr),
                        e = currCount.asSym()
                    )
                }) { freshAmount ->
                    TACCmd.Simple.WordStore(
                        base = TACKeyword.CONTRACT_COUNT.toVar(),
                        loc = srcContract.asTACSymbol(),
                        value = freshAmount.s
                    )
                }
            )
        }.merge(TACCmd.Simple.JumpCmd(callSucc))
        val returnProcess = p.addBlock(callSucc, countFixup)
        val constructorDispatcher = targetContracts.foldIndexed(sink) { instanceKey, next, contract ->
            val constr = contract.getConstructor()
            val constructorForInlining = Inliner.prepareConstructor(
                caller = src,
                tgt = constr!!,
                callSite = create
            )
            // the inlined constructor jumps to the return processing code generated above
            val constructorStart = p.addCode(constructorForInlining, returnProcess)
            // basic comparison
            val nextBlk = ExprUnfolder.unfoldPlusOneCmd("instanceCmp", with(TACExprFactUntyped) {
                Eq(instanceKey.asTACExpr, instrumentationVar.asSym())
            }) { cmpFlag ->
                TACCmd.Simple.JumpiCmd(
                    cond = cmpFlag.s,
                    dst = constructorStart,
                    elseDst = next
                )
            }
            p.addBlock(next, nextBlk)
        }
        p.replaceCommand(create.ptr, listOf(TACCmd.Simple.JumpCmd(constructorDispatcher)))
    }

    /**
     * For every method callee in [src]
     * that was known to *definitely* be a call on an instance created at [createSumm],
     * update these references to record that we now know that the callee is a clone of contract [srcContract]
     *
     * (this is consumed by the auto-dispatcher later)
     */
    private fun updateCreateReferences(
        src: CoreTACProgram,
        createSumm: CreateSummary,
        p: SimplePatchingProgram,
        srcContract: BigInteger,
    ) {
        src.parallelLtacStream().filter {
            it.cmd is TACCmd.Simple.SummaryCmd && it.cmd.summ is CallSummary && (it.cmd.summ.callTarget.any { y -> (y as? CallGraphBuilder.CalledContract.CreatedReference.Unresolved)?.createId == createSumm.createId })
        }.sequential().forEach {
            val summ = it.snarrowOrNull<CallSummary>()!!
            p.replaceCommand(
                it.ptr, listOf(
                    it.narrow<TACCmd.Simple.SummaryCmd>().cmd.copy(
                        summ = summ.copy(
                            callTarget = summ.callTarget.mapToSet {
                                    if((it as? CallGraphBuilder.CalledContract.CreatedReference.Unresolved)?.createId == createSumm.createId){
                                        CallGraphBuilder.CalledContract.CreatedReference.Resolved(
                                            tgtConntractId = srcContract
                                        )
                                    } else{
                                        it
                                    }
                                }
                            )
                        )
                    )
            )
        }
    }
}
