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

package decompiler

import allocator.Allocator
import analysis.CmdPointer
import analysis.Loop
import analysis.assertNotNull
import analysis.getNaturalLoops
import loaders.SoliditySceneTest
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import scene.ITACMethod
import scene.Scene
import spec.cvlast.SolidityContract
import tac.NBId
import tac.StartBlock
import tac.Tag
import utils.mapToSet
import vc.data.*
import vc.data.TACMeta.END_LOOP
import vc.data.TACMeta.START_LOOP
import vc.data.TACSymbol.Const
import vc.data.TACSymbol.Var
import verifier.PartialSelectorTest.a
import verifier.PartialSelectorTest.b
import verifier.PartialSelectorTest.x
import java.math.BigInteger

const val ENTRY_LABEL : Long = 8888
const val EXIT_LABEL: Long = 9999


//We are using both component tests and UT here to check the logic.
//The first is to check the logic on different versions of solidity which eventually create different kind of graphs
// the second is to check specific types of graphs.
open class BmcUnrollLabelsTest : SoliditySceneTest
{
    private fun getMethod(scene: Scene, functionName: String): ITACMethod {
        val m = scene.getContractOrNull(SolidityContract("Test"))?.getMethods()?.firstOrNull {
            it.name == functionName
        } ?: Assertions.fail("Could not find Test-$functionName in decompiler/Loops.sol"
        )
        return m
    }

    private fun getEntryAndExitBlocksFromCode(code: CoreTACProgram, loop: Loop): Pair<Set<NBId>, Set<NBId>>
    {
        val entryBlocks = mutableSetOf<NBId>()
        val exitBlocks = mutableSetOf<NBId>()
        val patching = code.toPatchingProgram()

        fun populateWithEntryAndExitBlocks(value: BigInteger?, block: NBId) {
            if (value == BigInteger.valueOf(EXIT_LABEL)) {
                /* sometimes an additional exit block is added before our labeled block
                due to insertAlongEdge */
                val exitBlock =  if ((patching.getPredecessors(block).size == 1) &&
                    (patching.getPredecessors(block).first() !in loop.body)) {
                    patching.getPredecessors(block).first()
                }
                else {
                    block
                }
                exitBlocks.add(exitBlock)
            }
            else if (value == BigInteger.valueOf(ENTRY_LABEL)) {
                entryBlocks.add(block)
            }
        }

        code.code.forEach { (block, cmds) ->
            cmds.forEach { cmd ->
                if (cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
                    if (cmd.rhs is TACExpr.Sym.Const) {
                        populateWithEntryAndExitBlocks(value = (cmd.rhs as TACExpr.Sym.Const).s.value, block)
                    }
                }
                else if (cmd is TACCmd.Simple.AssigningCmd.ByteStore) {
                    if (cmd.loc is Const && cmd.value is Const) {
                        populateWithEntryAndExitBlocks(value = cmd.loc.asSym().evalAsConst(), block)
                    }
                }
            }
        }
        return Pair(entryBlocks, exitBlocks)
    }

    //return a set of pairs of blockId and loopId for both entry and exitBlocks
    private fun getEntryAndExitBlocksByAnnotations(code: CoreTACProgram):
            Pair<Set<NBId>, Set<NBId>> {
        val entryBlocks = mutableSetOf<NBId>()
        val exitBlocks = mutableSetOf<NBId>()
        code.blockgraph.forEach {
            val commands = code.analysisCache.graph.elab(it.key).commands
            commands.forEach { cmd ->
                val annotCmd = cmd.cmd as? TACCmd.Simple.AnnotationCmd
                if (annotCmd?.annot?.k == START_LOOP) {
                    entryBlocks.add(it.key)
                }
                if (annotCmd?.annot?.k == END_LOOP) {
                    exitBlocks.add(it.key)
                }
            }

        }
        return Pair(entryBlocks, exitBlocks)
    }

    private fun verifyLoop(@Suppress("SameParameterValue") solcFilePath: String, functionName:String, solc:String, validateLoopSnippetConsistency: Boolean) {

        val scene = this.loadScene(solcFilePath, solc)
        val m = getMethod(scene, functionName)
        val oldCode = m.code
        val newCode = BMCRunner(1, oldCode as CoreTACProgram).bmcUnroll()

        // See CERT-3861 for why we skip this check in the case of nested loops with revert.
        // This is due to a bug, and the proposed fix is described in the ticket.
        if (validateLoopSnippetConsistency) {
            validateLoopSnippetConsistency(newCode)
        }

        //expected entry/exit blocks
        val result = getNaturalLoops(oldCode.analysisCache.graph).map { loop ->
            getEntryAndExitBlocksFromCode(newCode, loop)
        }
        val expectedEntryBlocks = result.unzip().first.flatten().toSet()
        val expectedExitBlocks = result.unzip().second.flatten().toSet()


        //actual entry/exit blocks
        val (entryBlocksLabeled, exitBlocksLabeled) = getEntryAndExitBlocksByAnnotations(newCode)

        //check that the entry blocks are the same
        Assertions.assertEquals(expectedEntryBlocks, entryBlocksLabeled)

        // compilers solc8+ will add the revert check which immediately returns, so some of the returns blocks
        // are actually loop exit block, this is why we are not checking equality
        Assertions.assertTrue(exitBlocksLabeled.containsAll(expectedExitBlocks))
    }



    private fun annotateLabels(coreTACProgram: CoreTACProgram, loop: Loop) : SimplePatchingProgram{
        val bmcRunner = BMCRunner(3, coreTACProgram)
        val loopId = Allocator.getFreshId(Allocator.Id.LOOP)
        return bmcRunner.annotateLoop(loop, loopId)
    }

    /**
     * Creates a TAC identical in structure to the pre-unrolling TAC obtained from Test/Unrolling/ComplexControlFlow.
    * To get a visual depiction of the command graph, see:
    * https://www.notion.so/certora/Displaying-the-TAC-Command-Graph-During-Debug-9f67adf3c8ba4af9883ac2fec6eba6d7
     */
    private fun create_complex_control_flow_tac() = TACProgramBuilder {
        a assign 1
        x assign TACExpr.BinRel.Gt(a.asSym(), BigInteger.valueOf(0).asTACExpr())
        jumpCond(x)
        jump(1) {
            b assign 1
        }
        jump(2) {
            b assign 2
            jump(3) {
                b assign 3
                jumpCond(x)
                jump(4) {
                    b assign 4
                }
                jump(5) {
                    b assign 5
                    jumpCond(x)
                    jump(6) {
                        b assign 6
                        jump(9) {
                            b assign 9
                            jump(3)
                        }
                    }
                    jump(7) {
                        b assign 7
                        jump(8) {
                            b assign 8
                            jump(3)
                        }
                    }
                }
            }
        }
    }.code

    sealed class Annot {
        data class StartLoop(val loopId: Int) : Annot()
        data class StartIter(val iteration: Int): Annot()
    }

    @Test
    fun loopSnippetConsistency() {
        val preUnrolling = create_complex_control_flow_tac()
        unrollAndValidateLoopSnippetConsistency(preUnrolling)
    }

    //this test is to check what happens if the edge which precedes the entry block has an additional successor.
    @Test
    fun loopInAnIf() {
        var coreTacProgram = CoreTACProgram.empty("loopInAnIf")
        var patching = coreTacProgram.toPatchingProgram()
        val startCondVar = Var("startCondition", Tag.Bool)
        val monotoneVar = Var("counter", Tag.Bit256)
        val condVar = Var("condition", Tag.Bool)
        patching.addVarDecls(setOf(monotoneVar, condVar, startCondVar))

        /*
         * CFG:
         *  0. loopInitializerBlock (monotoneVar := 0)
         *
         *     if startCondVar jumpto loopHeadBlock else jumpto loopExitBlock
         *     |              |
         *     |              V
         *     |      1. loopHeadBlock (condVar := monotoneVar < 10; if condVar jumpto loopTailBlock else jumpto loopExitBlock)
         *     |        | ^      \
         *     |        | |       V
         *     |        | |
         *     |        V |
         *     V        2. loopTailBlock (monotoneVar := monotoneVar + 1; jumpto loopHeadBlock)
         *     3. loopExitBlock (return)
        */

        val loopExitBlock = patching.addBlock(
                StartBlock.copy(origStartPc = 3),
                listOf(
                        TACCmd.Simple.ReturnSymCmd(TACSymbol.True),
                )
        )
        val loopTailBlock = patching.addBlock(
                StartBlock.copy(origStartPc = 2),
                listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACExpr.Vec.Add(monotoneVar.asSym(), TACSymbol.lift(1).asSym())),
                        // JUMP to HeadBlock is added later
                )
        )
        val loopHeadBlock = patching.addBlock(
                StartBlock.copy(origStartPc = 1),
                listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, TACExpr.BinRel.Lt(monotoneVar.asSym(), TACSymbol.lift(10).asSym())),
                        TACCmd.Simple.JumpiCmd(dst = loopTailBlock, cond = condVar, elseDst = loopExitBlock),
                )
        )
        val loopInitializerBlock = patching.addBlock(
                StartBlock.copy(),
                listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACSymbol.lift(0)),
                        TACCmd.Simple.JumpiCmd(dst = loopHeadBlock, cond = startCondVar, elseDst = loopExitBlock),
                )
        )


        coreTacProgram = patching.toCode(coreTacProgram)
        patching = coreTacProgram.toPatchingProgram()

        // Need to add the backedge only after refreshing patching because patching can't add a JUMP command to a block
        // that isn't in the "original" graph
        patching.insertAfter(CmdPointer(loopTailBlock, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))

        coreTacProgram = patching.toCode(coreTacProgram)

        val loop = Loop(head = loopHeadBlock, tail = loopTailBlock, body = setOf(loopHeadBlock, loopTailBlock))
        val newPatching = annotateLabels(coreTacProgram, loop)
        val newCode = newPatching.toCode(coreTacProgram)
        unrollAndValidateLoopSnippetConsistency(newCode)
        val (entryBlocksLabeled, exitBlocksLabeled) = getEntryAndExitBlocksByAnnotations(newCode)
        //in this case a new block loopStart should be added
        Assertions.assertTrue(newPatching.getPredecessors(loopHeadBlock).size == 2)
        Assertions.assertTrue(newPatching.getPredecessors(loopHeadBlock).first { it !in loop.body } != loopInitializerBlock)
        val loopStart = newPatching.getPredecessors(loopHeadBlock).first { it !in loop.body }
        Assertions.assertTrue(entryBlocksLabeled.size == 1)
        Assertions.assertEquals(entryBlocksLabeled.first() , loopStart)

        //in this case a new block loopEnd should be added
        Assertions.assertTrue(newPatching.getSuccessors(loopHeadBlock).size == 2)
        val loopEnd = newPatching.getSuccessors(loopHeadBlock).first { it !in loop.body }
        Assertions.assertTrue(exitBlocksLabeled.size == 1)
        Assertions.assertEquals(exitBlocksLabeled.first(), loopEnd)
    }


    //this test is to check what happens when the original loop is compiled into a bifid one.
    // in this case the loops should be merged into a single one before computing the annotations
    @Test
    fun bifidLoop() {
        var code = CoreTACProgram.empty("twoLoopsAsOne")
        var patching = code.toPatchingProgram()
        val startCondVar = Var("startCondition", Tag.Bool)
        val monotoneVar = Var("counter", Tag.Bit256)
        val condVar = Var("loopCondition", Tag.Bool)
        val anotherCondVar = Var("anotherCondition", Tag.Bool)

        patching.addVarDecls(setOf(monotoneVar, condVar, startCondVar, anotherCondVar))

        /*
         * CFG:
         *  0. loopInitializerBlock (monotoneVar := 0)
         *     |      V
         *     |      V
         *     |      V
         *     |      1. loopHeadBlock (condVar := monotoneVar < 10; if condVar jumpto loopTailBlock else jumpto loopExitBlock)
         *            /         | ^
         *           /         | |
         *          /         | |
         *         /          V |
         *        /         2. conditionBlock if startCondVar jumpto loopTail1Block else jumpto loopTail2Block
         *       /        |                                                                           \
         *      /         V                                                                           V
         *     |         3. loopTail1Block (monotoneVar := monotoneVar + 1; jumpto loopHeadBlock)     4. loopTail2Block (monotoneVar := monotoneVar + 2; jumpto loopHeadBlock)
         *     5. loopExitBlock (return)
        */

        val loopExitBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 5),
            listOf(
                TACCmd.Simple.ReturnSymCmd(TACSymbol.True),
            )
        )
        val loopTail1Block = patching.addBlock(
            StartBlock.copy(origStartPc = 4),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACExpr.Vec.Add(monotoneVar.asSym(), TACSymbol.lift(1).asSym())),
                // JUMP to HeadBlock is added later
            )
        )

        val loopTail2Block = patching.addBlock(
            StartBlock.copy(origStartPc = 3),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACExpr.Vec.Add(monotoneVar.asSym(), TACSymbol.lift(2).asSym())),
                // JUMP to HeadBlock is added later
            )
        )

        val conditionBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 2),
            listOf(
                TACCmd.Simple.JumpiCmd(dst = loopTail1Block, cond = anotherCondVar, elseDst = loopTail2Block),
            )
        )

        val loopHeadBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 1),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, TACExpr.BinRel.Lt(monotoneVar.asSym(), TACSymbol.lift(10).asSym())),
                TACCmd.Simple.JumpiCmd(dst = conditionBlock, cond = startCondVar, elseDst = loopExitBlock),
            )
        )

        val loopInitializerBlock = patching.addBlock(
            StartBlock.copy(),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACSymbol.lift(0)),
                TACCmd.Simple.JumpiCmd(dst = loopHeadBlock, cond = startCondVar, elseDst = loopExitBlock),
            )
        )

        code = patching.toCode(code)
        patching = code.toPatchingProgram()

        // Need to add the backedge only after refreshing patching because patching can't add a JUMP command to a block
        // that isn't in the "original" graph
        patching.insertAfter(CmdPointer(loopTail1Block, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))
        patching.insertAfter(CmdPointer(loopTail2Block, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))
        code = patching.toCode(code)

        val loops = getNaturalLoops(code.analysisCache.graph)
        Assertions.assertTrue(loops.size == 2)
        val mergedLoops = BMCRunner(1, code).getMergedLoops(loops)
        Assertions.assertTrue(mergedLoops.size == 1)
        val loop = mergedLoops.first()
        val newPatching = annotateLabels(code, loop)
        val newCode = newPatching.toCode(code)
        unrollAndValidateLoopSnippetConsistency(newCode)
        val (entryBlocksLabeled, exitBlocksLabeled) = getEntryAndExitBlocksByAnnotations(newCode)

        //in this case a new block loopStart should be added
        Assertions.assertTrue(entryBlocksLabeled.size == 1)
        Assertions.assertTrue(newPatching.getPredecessors(loopHeadBlock).size == 3)
        Assertions.assertTrue(newPatching.getPredecessors(loopHeadBlock).first { it !in loop.body } != loopInitializerBlock)
        val loopStart = newPatching.getPredecessors(loopHeadBlock).first { it !in loop.body }
        Assertions.assertTrue(entryBlocksLabeled.size == 1)
        Assertions.assertEquals(entryBlocksLabeled.first() , loopStart)

        //in this case a new block loopEnd should be added
        Assertions.assertTrue(newPatching.getSuccessors(loopHeadBlock).size == 2)
        val loopEnd = newPatching.getSuccessors(loopHeadBlock).first { it !in loop.body }
        Assertions.assertTrue(exitBlocksLabeled.size == 1)
        Assertions.assertEquals(exitBlocksLabeled.first(), loopEnd)
    }

    protected fun templateSimpleLoop(solc: String) {
        verifyLoop("decompiler/Loops.sol", "simpleLoop", solc, validateLoopSnippetConsistency = true)
    }

    protected fun templateSimpleReturn(solc: String) {
        verifyLoop("decompiler/Loops.sol", "loopWithReturn", solc, validateLoopSnippetConsistency = true)
    }

    protected fun templateSimpleReturn2(solc: String) {
        verifyLoop("decompiler/Loops.sol", "loopWithReturn2", solc, validateLoopSnippetConsistency = true)
    }

    protected fun templateSimpleBreak(solc: String) {
        verifyLoop("decompiler/Loops.sol", "loopWithBreak", solc, validateLoopSnippetConsistency = true)
    }

    protected fun templateSimpleRevert(solc: String) {
        verifyLoop("decompiler/Loops.sol", "loopWithRevert", solc, validateLoopSnippetConsistency = true)
    }

    protected fun templateNestedLoop(solc: String) {
        verifyLoop("decompiler/Loops.sol", "nestedLoop", solc, validateLoopSnippetConsistency = false)
    }

    protected fun templateNestedLoopWithRevert(solc: String) {
        verifyLoop("decompiler/Loops.sol", "nestedRevert", solc, validateLoopSnippetConsistency = false)
    }

    protected fun templateTwoLoops(solc: String) {
        verifyLoop("decompiler/Loops.sol", "twoLoops", solc, validateLoopSnippetConsistency = true)
    }
}
fun unrollAndValidateLoopSnippetConsistency(preUnrolling: CoreTACProgram) {
    val bmc = BMCRunner(UNROLL_CONST = 2, code = preUnrolling)
    val postUnrolling = bmc.bmcUnroll()
    validateLoopSnippetConsistency(postUnrolling)
}

fun validateLoopSnippetConsistency(unrolledTAC: CoreTACProgram) {
    val sorted = unrolledTAC.topoSortFw
    Assertions.assertTrue(sorted.isNotEmpty()) { "Expected a non-empty list of topo-sorted blocks" }
//  For each nbid, maintains a stack of StartLoop/StartIter annotations
    val nbidToLoopState = mutableMapOf<NBId, List<BmcUnrollLabelsTest.Annot>>()
    nbidToLoopState[sorted[0]] = listOf()
    val g = unrolledTAC.analysisCache.graph

    for (nbid in sorted) {
        val predecessors = g.pred(nbid)
        val predState : List <BmcUnrollLabelsTest.Annot> = if (predecessors.isEmpty()) {
            // Verify that we are root
            check(nbid == sorted[0]) {"The only node without predecessors should be the graph root."}
            emptyList()
        } else {
            /** We assume that all predecessors have the same state.
            * This may not be true for all TACs, but it holds for the specific graph returned by
            * create_complex_control_flow_tac */
            val predStates = predecessors.mapToSet {
                val predLoopState = nbidToLoopState[it]
                assertNotNull(predLoopState, "Expected to have a state for block $it (predecessor of $nbid)")
                predLoopState
            }
            Assertions.assertTrue(predStates.size == 1) {"Expected all predecessors of $nbid to have the same loop state (got $predStates)"}
            predStates.single()
        }
        nbidToLoopState[nbid] = predState
        val code = unrolledTAC.code[nbid] ?: Assertions.fail("Failed to find the code of $nbid")
        var nbidState = predState
        for (cmd in code) {
            val lastAnnot = nbidState.lastOrNull()
            when (val annotationCmdVal = (cmd as? TACCmd.Simple.AnnotationCmd)?.annot?.v)  {
                is SnippetCmd.EVMSnippetCmd.LoopSnippet.StartLoopSnippet -> {
                    nbidState = nbidState.plus(BmcUnrollLabelsTest.Annot.StartLoop(loopId = annotationCmdVal.loopIndex))
                }
                is SnippetCmd.EVMSnippetCmd.LoopSnippet.StartIter -> {
                    Assertions.assertTrue(lastAnnot is BmcUnrollLabelsTest.Annot.StartLoop) {
                        "Expected the stack head to be a BmcUnrollLabelsTest.Annot.StartLoop) (found $lastAnnot)"
                    }
                    nbidState = nbidState.plus(BmcUnrollLabelsTest.Annot.StartIter(iteration = annotationCmdVal.iteration))
                }
                is SnippetCmd.EVMSnippetCmd.LoopSnippet.EndIter ->  {
                    Assertions.assertTrue(lastAnnot is BmcUnrollLabelsTest.Annot.StartIter && lastAnnot.iteration == annotationCmdVal.iteration) {
                        "Expected the stack head to be a BmcUnrollLabelsTest.Annot.StartIter (found $lastAnnot)"
                    }
                    nbidState = nbidState.dropLast(1)
                }
                is SnippetCmd.EVMSnippetCmd.LoopSnippet.EndLoopSnippet -> {
                    Assertions.assertTrue(lastAnnot is BmcUnrollLabelsTest.Annot.StartLoop && lastAnnot.loopId == annotationCmdVal.loopId) {
                        "Expected the stack head to be a BmcUnrollLabelsTest.Annot.StartLoop) (found $lastAnnot)"
                    }
                    nbidState = nbidState.dropLast(1)
                }
            }
        }
        nbidToLoopState[nbid] = nbidState
    }
}
