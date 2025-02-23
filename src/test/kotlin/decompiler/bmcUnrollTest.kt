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

import analysis.CmdPointer
import analysis.Loop
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import tac.StartBlock
import tac.Tag
import utils.safeAsInt
import vc.data.CoreTACProgram
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol

class BmcUnrollTest {
    private val LOOP_COUNT = 10

    private fun guessUnrollConst(coreTACProgram: CoreTACProgram, loop: Loop, UNROLL_CONST: Int = 1): Int? {
        val bmcRunner = BMCRunner(UNROLL_CONST, coreTACProgram)
        return bmcRunner.guessUnrollConst(loop)?.safeAsInt()
    }
    @Test
    fun simpleMonotoneIncreasing() {
        var coreTacProgram = CoreTACProgram.empty("monotoneIncreasingProgram")
        var patching = coreTacProgram.toPatchingProgram()

        val monotoneVar = TACSymbol.Var("counter", Tag.Bit256)
        val condVar = TACSymbol.Var("condition", Tag.Bool)
        patching.addVarDecls(setOf(monotoneVar, condVar))

        /*
         * CFG:
         *        0. loopInitializerBlock (monotoneVar := 0)
         *                |
         *                V
         *        1. loopHeadBlock (condVar := monotoneVar < 10; if condVar jumpto loopTailBlock else jumpto loopExitBlock)
         *          | ^      \
         *          | |       V
         *          | |      3. loopExitBlock (return)
         *          V |
         *   2. loopTailBlock (monotoneVar := monotoneVar + 1; jumpto loopHeadBlock)
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
                TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, TACExpr.BinRel.Lt(monotoneVar.asSym(), TACSymbol.lift(LOOP_COUNT).asSym())),
                TACCmd.Simple.JumpiCmd(dst = loopTailBlock, cond = condVar, elseDst = loopExitBlock),
            )
        )
        patching.addBlock(
            StartBlock.copy(),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACSymbol.lift(0)),
                TACCmd.Simple.JumpCmd(loopHeadBlock),
            )
        )

        coreTacProgram = patching.toCode(coreTacProgram)
        patching = coreTacProgram.toPatchingProgram()

        // Need to add the backedge only after refreshing patching because patching can't add a JUMP command to a block that isn't in the "original" graph
        patching.insertAfter(CmdPointer(loopTailBlock, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))

        coreTacProgram = patching.toCode(coreTacProgram)
        unrollAndValidateLoopSnippetConsistency(coreTacProgram)

        val loop = Loop(head = loopHeadBlock, tail = loopTailBlock, body = setOf(loopHeadBlock, loopTailBlock))
        Assertions.assertEquals(LOOP_COUNT, guessUnrollConst(coreTacProgram, loop))
    }

    @Test
    fun simpleMonotoneIncreasingSigned() {
        var coreTacProgram = CoreTACProgram.empty("monotoneIncreasingProgram")
        var patching = coreTacProgram.toPatchingProgram()

        val monotoneVar = TACSymbol.Var("counter", Tag.Bit256)
        val condVar = TACSymbol.Var("condition", Tag.Bool)
        patching.addVarDecls(setOf(monotoneVar, condVar))

        /*
         * CFG:
         *        0. loopInitializerBlock (monotoneVar := 0)
         *                |
         *                V
         *        1. loopHeadBlock (condVar := monotoneVar < 10; if condVar jumpto loopTailBlock else jumpto loopExitBlock)
         *          | ^      \
         *          | |       V
         *          | |      3. loopExitBlock (return)
         *          V |
         *   2. loopTailBlock (monotoneVar := monotoneVar + 1; jumpto loopHeadBlock)
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
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, TACExpr.BinRel.Slt(monotoneVar.asSym(), TACSymbol.lift(LOOP_COUNT).asSym())),
                        TACCmd.Simple.JumpiCmd(dst = loopTailBlock, cond = condVar, elseDst = loopExitBlock),
                )
        )
        patching.addBlock(
                StartBlock.copy(),
                listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACSymbol.lift(0)),
                        TACCmd.Simple.JumpCmd(loopHeadBlock),
                )
        )

        coreTacProgram = patching.toCode(coreTacProgram)
        patching = coreTacProgram.toPatchingProgram()

        // Need to add the backedge only after refreshing patching because patching can't add a JUMP command to a block that isn't in the "original" graph
        patching.insertAfter(CmdPointer(loopTailBlock, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))

        coreTacProgram = patching.toCode(coreTacProgram)
        unrollAndValidateLoopSnippetConsistency(coreTacProgram)

        val loop = Loop(head = loopHeadBlock, tail = loopTailBlock, body = setOf(loopHeadBlock, loopTailBlock))
        Assertions.assertEquals(LOOP_COUNT, guessUnrollConst(coreTacProgram, loop))
    }


    @Test
    fun simpleMonotoneIncreasingOppositeOrder() {
        var coreTacProgram = CoreTACProgram.empty("monotoneIncreasingProgram")
        var patching = coreTacProgram.toPatchingProgram()

        val monotoneVar = TACSymbol.Var("counter", Tag.Bit256)
        val condVar = TACSymbol.Var("condition", Tag.Bool)
        patching.addVarDecls(setOf(monotoneVar, condVar))

        /*
         * CFG:
         *        0. loopInitializerBlock (monotoneVar := 0)
         *                |
         *                V
         *        1. loopHeadBlock (condVar := monotoneVar < 10; if condVar jumpto loopTailBlock else jumpto loopExitBlock)
         *          | ^      \
         *          | |       V
         *          | |      3. loopExitBlock (return)
         *          V |
         *   2. loopTailBlock (monotoneVar := 1 + monotoneVar; jumpto loopHeadBlock)
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
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACExpr.Vec.Add(TACSymbol.lift(1).asSym(), monotoneVar.asSym())),
                        // JUMP to HeadBlock is added later
                )
        )
        val loopHeadBlock = patching.addBlock(
                StartBlock.copy(origStartPc = 1),
                listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, TACExpr.BinRel.Lt(monotoneVar.asSym(), TACSymbol.lift(LOOP_COUNT).asSym())),
                        TACCmd.Simple.JumpiCmd(dst = loopTailBlock, cond = condVar, elseDst = loopExitBlock),
                )
        )
        patching.addBlock(
                StartBlock.copy(),
                listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACSymbol.lift(0)),
                        TACCmd.Simple.JumpCmd(loopHeadBlock),
                )
        )

        coreTacProgram = patching.toCode(coreTacProgram)
        patching = coreTacProgram.toPatchingProgram()

        // Need to add the backedge only after refreshing patching because patching can't add a JUMP command to a block that isn't in the "original" graph
        patching.insertAfter(CmdPointer(loopTailBlock, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))

        coreTacProgram = patching.toCode(coreTacProgram)
        unrollAndValidateLoopSnippetConsistency(coreTacProgram)

        val loop = Loop(head = loopHeadBlock, tail = loopTailBlock, body = setOf(loopHeadBlock, loopTailBlock))
        Assertions.assertEquals(LOOP_COUNT, guessUnrollConst(coreTacProgram, loop))
    }


    @Test
    fun simpleMonotoneDecreasing() {
        var coreTacProgram = CoreTACProgram.empty("monotoneIncreasingProgram")
        var patching = coreTacProgram.toPatchingProgram()

        val monotoneVar = TACSymbol.Var("counter", Tag.Bit256)
        val condVar = TACSymbol.Var("condition", Tag.Bool)
        patching.addVarDecls(setOf(monotoneVar, condVar))

        /*
         * CFG:
         *        0. loopInitializerBlock (monotoneVar := 10)
         *                |
         *                V
         *        1. loopHeadBlock (condVar := monotoneVar > 0; if condVar jumpto loopTailBlock else jumpto loopExitBlock)
         *          | ^      \
         *          | |       V
         *          | |      3. loopExitBlock (return)
         *          V |
         *   2. loopTailBlock (monotoneVar := monotoneVar - 1; jumpto loopHeadBlock)
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
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACExpr.BinOp.Sub(monotoneVar.asSym(), TACSymbol.lift(1).asSym())),
                // JUMP to HeadBlock is added later
            )
        )
        val loopHeadBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 1),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, TACExpr.BinRel.Gt(monotoneVar.asSym(), TACSymbol.lift(0).asSym())),
                TACCmd.Simple.JumpiCmd(dst = loopTailBlock, cond = condVar, elseDst = loopExitBlock),
            )
        )
        patching.addBlock(
            StartBlock.copy(),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACSymbol.lift(LOOP_COUNT)),
                TACCmd.Simple.JumpCmd(loopHeadBlock),
            )
        )

        coreTacProgram = patching.toCode(coreTacProgram)
        patching = coreTacProgram.toPatchingProgram()

        // Need to add the backedge only after refreshing patching because patching can't add a JUMP command to a block that isn't in the "original" graph
        patching.insertAfter(CmdPointer(loopTailBlock, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))

        coreTacProgram = patching.toCode(coreTacProgram)
        unrollAndValidateLoopSnippetConsistency(coreTacProgram)

        val loop = Loop(head = loopHeadBlock, tail = loopTailBlock, body = setOf(loopHeadBlock, loopTailBlock))
        Assertions.assertEquals(LOOP_COUNT, guessUnrollConst(coreTacProgram, loop))
    }

    @Test
    fun simpleMonotoneDecreasingSigned() {
        var coreTacProgram = CoreTACProgram.empty("monotoneIncreasingProgram")
        var patching = coreTacProgram.toPatchingProgram()

        val monotoneVar = TACSymbol.Var("counter", Tag.Bit256)
        val condVar = TACSymbol.Var("condition", Tag.Bool)
        patching.addVarDecls(setOf(monotoneVar, condVar))

        /*
         * CFG:
         *        0. loopInitializerBlock (monotoneVar := 10)
         *                |
         *                V
         *        1. loopHeadBlock (condVar := monotoneVar > 0; if condVar jumpto loopTailBlock else jumpto loopExitBlock)
         *          | ^      \
         *          | |       V
         *          | |      3. loopExitBlock (return)
         *          V |
         *   2. loopTailBlock (monotoneVar := monotoneVar - 1; jumpto loopHeadBlock)
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
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACExpr.BinOp.Sub(monotoneVar.asSym(), TACSymbol.lift(1).asSym())),
                        // JUMP to HeadBlock is added later
                )
        )
        val loopHeadBlock = patching.addBlock(
                StartBlock.copy(origStartPc = 1),
                listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, TACExpr.BinRel.Sgt(monotoneVar.asSym(), TACSymbol.lift(0).asSym())),
                        TACCmd.Simple.JumpiCmd(dst = loopTailBlock, cond = condVar, elseDst = loopExitBlock),
                )
        )
        patching.addBlock(
                StartBlock.copy(),
                listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACSymbol.lift(LOOP_COUNT)),
                        TACCmd.Simple.JumpCmd(loopHeadBlock),
                )
        )

        coreTacProgram = patching.toCode(coreTacProgram)
        patching = coreTacProgram.toPatchingProgram()

        // Need to add the backedge only after refreshing patching because patching can't add a JUMP command to a block that isn't in the "original" graph
        patching.insertAfter(CmdPointer(loopTailBlock, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))

        coreTacProgram = patching.toCode(coreTacProgram)
        unrollAndValidateLoopSnippetConsistency(coreTacProgram)

        val loop = Loop(head = loopHeadBlock, tail = loopTailBlock, body = setOf(loopHeadBlock, loopTailBlock))
        Assertions.assertEquals(LOOP_COUNT, guessUnrollConst(coreTacProgram, loop))
    }


    @Test
    fun notMonotoneIncreasing() {
        var coreTacProgram = CoreTACProgram.empty("monotoneIncreasingProgram")
        var patching = coreTacProgram.toPatchingProgram()

        val monotoneVar = TACSymbol.Var("counter", Tag.Bit256)
        val condVar = TACSymbol.Var("condition", Tag.Bool)
        patching.addVarDecls(setOf(monotoneVar, condVar))

        /*
         * CFG:
         *        0. loopInitializerBlock (monotoneVar := 0)
         *                |
         *                V
         *      1. loopHeadBlock (condVar := monotoneVar < 10; if condVar jumpto loopTailBlock else jumpto loopExitBlock)
         *       ^   |      \
         *      /    |       V
         *     /     |      3. loopExitBlock (return)
         *    |      V
         *    |  4. loopBodyBlock (monotoneVar := monotoneVar & 1; jumpto loopTailBlock)
         *    |     |
         *    |     V
         *   2. loopTailBlock (monotoneVar := monotoneVar + 1; jumpto loopHeadBlock)
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
        val loopBodyBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 4),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACExpr.BinOp.BWAnd(monotoneVar.asSym(), TACSymbol.lift(1).asSym())),
                TACCmd.Simple.JumpCmd(loopTailBlock),
            )
        )
        val loopHeadBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 1),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, TACExpr.BinRel.Lt(monotoneVar.asSym(), TACSymbol.lift(LOOP_COUNT).asSym())),
                TACCmd.Simple.JumpiCmd(dst = loopBodyBlock, cond = condVar, elseDst = loopExitBlock),
            )
        )
        patching.addBlock(
            StartBlock.copy(),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACSymbol.lift(0)),
                TACCmd.Simple.JumpCmd(loopHeadBlock),
            )
        )

        coreTacProgram = patching.toCode(coreTacProgram)
        patching = coreTacProgram.toPatchingProgram()

        // Need to add the backedge only after refreshing patching because patching can't add a JUMP command to a block that isn't in the "original" graph
        patching.insertAfter(CmdPointer(loopTailBlock, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))

        coreTacProgram = patching.toCode(coreTacProgram)
        unrollAndValidateLoopSnippetConsistency(coreTacProgram)

        val loop = Loop(head = loopHeadBlock, tail = loopTailBlock, body = setOf(loopHeadBlock, loopBodyBlock, loopTailBlock))
        Assertions.assertEquals(null, guessUnrollConst(coreTacProgram, loop))
    }

    @Test
    fun notMonotoneDecreasing() {
        var coreTacProgram = CoreTACProgram.empty("monotoneIncreasingProgram")
        var patching = coreTacProgram.toPatchingProgram()

        val monotoneVar = TACSymbol.Var("counter", Tag.Bit256)
        val condVar = TACSymbol.Var("condition", Tag.Bool)
        patching.addVarDecls(setOf(monotoneVar, condVar))

        /*
         * CFG:
         *        0. loopInitializerBlock (monotoneVar := 10)
         *                |
         *                V
         *      1. loopHeadBlock (condVar := monotoneVar > 0; if condVar jumpto loopTailBlock else jumpto loopExitBlock)
         *       ^   |      \
         *      /    |       V
         *     /     |      3. loopExitBlock (return)
         *    |      V
         *    |  4. loopBodyBlock (monotoneVar := monotoneVar | 1; jumpto loopTailBlock)
         *    |     |
         *    |     V
         *   2. loopTailBlock (monotoneVar := monotoneVar - 1; jumpto loopHeadBlock)
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
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACExpr.BinOp.Sub(monotoneVar.asSym(), TACSymbol.lift(1).asSym())),
                // JUMP to HeadBlock is added later
            )
        )
        val loopBodyBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 4),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACExpr.BinOp.BWOr(monotoneVar.asSym(), TACSymbol.lift(1).asSym())),
                TACCmd.Simple.JumpCmd(loopTailBlock),
            )
        )
        val loopHeadBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 1),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACExpr.BinOp.BWOr(monotoneVar.asSym(), TACSymbol.lift(1).asSym())),
                TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, TACExpr.BinRel.Gt(monotoneVar.asSym(), TACSymbol.lift(0).asSym())),
                TACCmd.Simple.JumpiCmd(dst = loopBodyBlock, cond = condVar, elseDst = loopExitBlock),
            )
        )
        patching.addBlock(
            StartBlock.copy(),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACSymbol.lift(LOOP_COUNT)),
                TACCmd.Simple.JumpCmd(loopHeadBlock),
            )
        )

        coreTacProgram = patching.toCode(coreTacProgram)
        patching = coreTacProgram.toPatchingProgram()

        // Need to add the backedge only after refreshing patching because patching can't add a JUMP command to a block that isn't in the "original" graph
        patching.insertAfter(CmdPointer(loopTailBlock, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))

        coreTacProgram = patching.toCode(coreTacProgram)
        unrollAndValidateLoopSnippetConsistency(coreTacProgram)

        val loop = Loop(head = loopHeadBlock, tail = loopTailBlock, body = setOf(loopHeadBlock, loopBodyBlock, loopTailBlock))
        Assertions.assertEquals(null, guessUnrollConst(coreTacProgram, loop))
    }

    @Test
    fun advancedMonotoneIncreasing() {
        var coreTacProgram = CoreTACProgram.empty("monotoneIncreasingProgram")
        var patching = coreTacProgram.toPatchingProgram()

        val monotoneVar = TACSymbol.Var("counter", Tag.Bit256)
        val monotoneVar2 = TACSymbol.Var("counter2", Tag.Bit256)
        val condVar = TACSymbol.Var("condition", Tag.Bool)
        patching.addVarDecls(setOf(monotoneVar, monotoneVar2, condVar))

        /*
         * CFG:
         *        0. loopInitializerBlock (monotoneVar := 0)
         *                |
         *                V
         *      1. loopHeadBlock (condVar := monotoneVar < 10; if condVar jumpto loopTailBlock else jumpto loopExitBlock)
         *       ^   |      \
         *      /    |       V
         *     /     |      3. loopExitBlock (return)
         *    |      V
         *    |  4. loopBodyBlock (monotonVar2 := monotoneVar + 1; jumpto loopTailBlock)
         *    |     |
         *    |     V
         *   2. loopTailBlock (monotoneVar := monotoneVar2; jumpto loopHeadBlock)
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
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, monotoneVar2),
                // JUMP to HeadBlock is added later
            )
        )
        val loopBodyBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 4),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar2, TACExpr.Vec.Add(monotoneVar.asSym(), TACSymbol.lift(1).asSym())),
                TACCmd.Simple.JumpCmd(loopTailBlock),
            )
        )
        val loopHeadBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 1),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, TACExpr.BinRel.Lt(monotoneVar.asSym(), TACSymbol.lift(LOOP_COUNT).asSym())),
                TACCmd.Simple.JumpiCmd(dst = loopBodyBlock, cond = condVar, elseDst = loopExitBlock),
            )
        )
        patching.addBlock(
            StartBlock.copy(),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACSymbol.lift(0)),
                TACCmd.Simple.JumpCmd(loopHeadBlock),
            )
        )

        coreTacProgram = patching.toCode(coreTacProgram)
        patching = coreTacProgram.toPatchingProgram()

        // Need to add the backedge only after refreshing patching because patching can't add a JUMP command to a block that isn't in the "original" graph
        patching.insertAfter(CmdPointer(loopTailBlock, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))

        coreTacProgram = patching.toCode(coreTacProgram)
        unrollAndValidateLoopSnippetConsistency(coreTacProgram)

        val loop = Loop(head = loopHeadBlock, tail = loopTailBlock, body = setOf(loopHeadBlock, loopBodyBlock, loopTailBlock))
        Assertions.assertEquals(LOOP_COUNT, guessUnrollConst(coreTacProgram, loop))
    }


    //for now we are not supporting loops where the update on the iterating variable is too
    // complicated : for instance for
    // (int y=0; y<CONST; y++)
    // ...
    // x = x+y
    // y = x
    // If we add the support, we should update the test.
    @Test
    fun tooAdvancedMonotoneIncreasing() {
        var coreTacProgram = CoreTACProgram.empty("monotoneIncreasingProgram")
        var patching = coreTacProgram.toPatchingProgram()

        val monotoneVar = TACSymbol.Var("counter", Tag.Bit256)
        val monotoneVar2 = TACSymbol.Var("counter2", Tag.Bit256)
        val condVar = TACSymbol.Var("condition", Tag.Bool)
        patching.addVarDecls(setOf(monotoneVar, monotoneVar2, condVar))

        /*
         * CFG:
         *        0. loopInitializerBlock (monotoneVar := 0)
         *                |
         *                V
         *      1. loopHeadBlock (condVar := monotoneVar < 10; if condVar jumpto loopTailBlock else jumpto loopExitBlock)
         *       ^   |      \
         *      /    |       V
         *     /     |      3. loopExitBlock (return)
         *    |      V
         *    |  4. loopBodyBlock (monotoneVar2 := monotoneVar + monotoneVar2; jumpto loopTailBlock)
         *    |     |
         *    |     V
         *   2. loopTailBlock (monotoneVar := monotoneVar2; jumpto loopHeadBlock)
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
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, monotoneVar2),
                        // JUMP to HeadBlock is added later
                )
        )
        val loopBodyBlock = patching.addBlock(
                StartBlock.copy(origStartPc = 4),
                listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar2, TACExpr.Vec.Add(monotoneVar.asSym(), monotoneVar2.asSym())),
                        TACCmd.Simple.JumpCmd(loopTailBlock),
                )
        )
        val loopHeadBlock = patching.addBlock(
                StartBlock.copy(origStartPc = 1),
                listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, TACExpr.BinRel.Lt(monotoneVar.asSym(), TACSymbol.lift(LOOP_COUNT).asSym())),
                        TACCmd.Simple.JumpiCmd(dst = loopBodyBlock, cond = condVar, elseDst = loopExitBlock),
                )
        )
        patching.addBlock(
                StartBlock.copy(),
                listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACSymbol.lift(0)),
                        TACCmd.Simple.JumpCmd(loopHeadBlock),
                )
        )

        coreTacProgram = patching.toCode(coreTacProgram)
        patching = coreTacProgram.toPatchingProgram()

        // Need to add the backedge only after refreshing patching because patching can't add a JUMP command to a block that isn't in the "original" graph
        patching.insertAfter(CmdPointer(loopTailBlock, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))

        coreTacProgram = patching.toCode(coreTacProgram)
        unrollAndValidateLoopSnippetConsistency(coreTacProgram)

        val loop = Loop(head = loopHeadBlock, tail = loopTailBlock, body = setOf(loopHeadBlock, loopBodyBlock, loopTailBlock))
        Assertions.assertEquals(null, guessUnrollConst(coreTacProgram, loop))
    }


    @Test
    fun advancedMonotoneDecreasing() {
        var coreTacProgram = CoreTACProgram.empty("monotoneIncreasingProgram")
        var patching = coreTacProgram.toPatchingProgram()

        val monotoneVar = TACSymbol.Var("counter", Tag.Bit256)
        val monotoneVar2 = TACSymbol.Var("counter2", Tag.Bit256)
        val condVar = TACSymbol.Var("condition", Tag.Bool)
        patching.addVarDecls(setOf(monotoneVar, monotoneVar2, condVar))

        /*
         * CFG:
         *        0. loopInitializerBlock (monotoneVar := 10)
         *                |
         *                V
         *      1. loopHeadBlock (condVar := monotoneVar > 1; if condVar jumpto loopTailBlock else jumpto loopExitBlock)
         *       ^   |      \
         *      /    |       V
         *     /     |      3. loopExitBlock (return)
         *    |      V
         *    |  4. loopBodyBlock (monotoneVar2 := monotoneVar - 1; jumpto loopTailBlock)
         *    |     |
         *    |     V
         *   2. loopTailBlock (monotoneVar := monotoneVar2; jumpto loopHeadBlock)
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
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, monotoneVar2),
                // JUMP to HeadBlock is added later
            )
        )
        val loopBodyBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 4),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar2, TACExpr.BinOp.Sub(monotoneVar.asSym(), TACSymbol.lift(1).asSym())),
                TACCmd.Simple.JumpCmd(loopTailBlock),
            )
        )
        val loopHeadBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 1),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, TACExpr.BinRel.Gt(monotoneVar.asSym(), TACSymbol.lift(1).asSym())),
                TACCmd.Simple.JumpiCmd(dst = loopBodyBlock, cond = condVar, elseDst = loopExitBlock),
            )
        )
        patching.addBlock(
            StartBlock.copy(),
            listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACSymbol.lift(LOOP_COUNT)),
                TACCmd.Simple.JumpCmd(loopHeadBlock),
            )
        )

        coreTacProgram = patching.toCode(coreTacProgram)
        patching = coreTacProgram.toPatchingProgram()

        // Need to add the backedge only after refreshing patching because patching can't add a JUMP command to a block that isn't in the "original" graph
        patching.insertAfter(CmdPointer(loopTailBlock, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))

        coreTacProgram = patching.toCode(coreTacProgram)
        unrollAndValidateLoopSnippetConsistency(coreTacProgram)

        val loop = Loop(head = loopHeadBlock, tail = loopTailBlock, body = setOf(loopHeadBlock, loopBodyBlock, loopTailBlock))
        Assertions.assertEquals(LOOP_COUNT - 1, guessUnrollConst(coreTacProgram, loop))
    }

//for now we are not supporting loops where the update on the iterating variable is too
// complicated : for instance for
// (int y=0; y>CONST; y++)
// ...
// x = y-x
// y = x
// If we add the support, we should update the test.
@Test
fun tooAdvancedMonotoneDecreasing() {
    var coreTacProgram = CoreTACProgram.empty("monotoneIncreasingProgram")
    var patching = coreTacProgram.toPatchingProgram()

    val monotoneVar = TACSymbol.Var("counter", Tag.Bit256)
    val monotoneVar2 = TACSymbol.Var("counter2", Tag.Bit256)
    val condVar = TACSymbol.Var("condition", Tag.Bool)
    patching.addVarDecls(setOf(monotoneVar, monotoneVar2, condVar))

    /*
     * CFG:
     *        0. loopInitializerBlock (monotoneVar := 10)
     *                |
     *                V
     *      1. loopHeadBlock (condVar := monotoneVar > 1; if condVar jumpto loopTailBlock else jumpto loopExitBlock)
     *       ^   |      \
     *      /    |       V
     *     /     |      3. loopExitBlock (return)
     *    |      V
     *    |  4. loopBodyBlock (monotoneVar2 := monotoneVar - 1; jumpto loopTailBlock)
     *    |     |
     *    |     V
     *   2. loopTailBlock (monotoneVar := monotoneVar2; jumpto loopHeadBlock)
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
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, monotoneVar2),
                    // JUMP to HeadBlock is added later
            )
    )
    val loopBodyBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 4),
            listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar2, TACExpr.BinOp.Sub(monotoneVar.asSym(), monotoneVar2.asSym())),
                    TACCmd.Simple.JumpCmd(loopTailBlock),
            )
    )
    val loopHeadBlock = patching.addBlock(
            StartBlock.copy(origStartPc = 1),
            listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, TACExpr.BinRel.Gt(monotoneVar.asSym(), TACSymbol.lift(1).asSym())),
                    TACCmd.Simple.JumpiCmd(dst = loopBodyBlock, cond = condVar, elseDst = loopExitBlock),
            )
    )
    patching.addBlock(
            StartBlock.copy(),
            listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(monotoneVar, TACSymbol.lift(LOOP_COUNT)),
                    TACCmd.Simple.JumpCmd(loopHeadBlock),
            )
    )

    coreTacProgram = patching.toCode(coreTacProgram)
    patching = coreTacProgram.toPatchingProgram()

    // Need to add the backedge only after refreshing patching because patching can't add a JUMP command to a block that isn't in the "original" graph
    patching.insertAfter(CmdPointer(loopTailBlock, 0), listOf(TACCmd.Simple.JumpCmd(loopHeadBlock)))

    coreTacProgram = patching.toCode(coreTacProgram)
    unrollAndValidateLoopSnippetConsistency(coreTacProgram)

    val loop = Loop(head = loopHeadBlock, tail = loopTailBlock, body = setOf(loopHeadBlock, loopBodyBlock, loopTailBlock))
    //we should not guess in such cases, it's too complicated and we go for soundness
    Assertions.assertEquals(null, guessUnrollConst(coreTacProgram, loop))
}

}

