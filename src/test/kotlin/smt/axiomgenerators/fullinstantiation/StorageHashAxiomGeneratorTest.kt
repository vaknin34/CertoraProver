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

package smt.axiomgenerators.fullinstantiation

import config.Config
import evm.EVM_MOD_GROUP256
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import smt.HashingScheme
import smt.solverscript.LExpressionFactory
import smt.solverscript.SmtTheory
import smt.solverscript.functionsymbols.NonSMTInterpretedFunctionSymbol
import smtlibutils.data.SatResult
import tac.Tag
import vc.data.HashFamily
import vc.data.LExpression
import vc.data.TACBuiltInFunction
import java.math.BigInteger

internal class StorageHashAxiomGeneratorTest {

    private val skeySort = TACBuiltInFunction.Hash.skeySort

    private val niaLegacyHashingTestSetup = getNiaLegacyHashingTestSetup()

    private fun getNiaLegacyHashingTestSetup(
        gapSize: BigInteger = EVM_MOD_GROUP256,
        maxSoliditySlot: BigInteger = Config.MaxBaseStorageSlot.get()
    ) = MockLExpToSmtLib.TestSetup.makeNiaSetup(HashingScheme.Legacy()) { lxf: LExpressionFactory ->
        listOf(StorageHashAxiomGeneratorLegacy(lxf, gapSize, maxSoliditySlot))
    }

    private val niaDatatypesHashingTestSetup =
        MockLExpToSmtLib.TestSetup.makeNiaSetup(HashingScheme.Datatypes) { lxf: LExpressionFactory ->
            listOf(StorageHashAxiomGeneratorDataTypes(lxf))
        }

    private val niaPlainInjectivityHashingTestSetup =
        MockLExpToSmtLib.TestSetup.makeNiaSetup(HashingScheme.PlainInjectivity) { lxf: LExpressionFactory ->
            listOf(StorageHashAxiomGeneratorPlainInjectivity(
                lxf,
                targetTheory = SmtTheory.fromString("QF_UFNIA"),
                axiomatizeKeccack = true
            ))
        }


    private fun LExpressionFactory.toSkey(exp: LExpression) =
        applyExp(NonSMTInterpretedFunctionSymbol.Hash.ToSkey, exp)

    /**
     * Builds a standard keccack hash with the given arguments; sets the length field as "32 * <number of arguments>".
     */
    private fun LExpressionFactory.keccack(vararg args: LExpression): LExpression {
        val arity = args.size
        return applyExp(
            NonSMTInterpretedFunctionSymbol.Hash.SimpleHashN(arity + 1, HashFamily.Keccack),
            listOf(toSkey(litInt(arity * 32))) + args.toList()
        )
    }

    /**
     * Creates a formula for testing the "hash functions of different arities can't collide" feature of our hashing.
     */
    private fun formulaNonCollisionSameArity01(): (LExpressionFactory) -> List<LExpression> =
        { lxf: LExpressionFactory ->
            val (x1, x2, x3) = listOf("x1", "x2", "x3").map { lxf.makeConstant(it, skeySort) }
            val (y1, y2, y3) = listOf("y1", "y2", "y3").map { lxf.makeConstant(it, skeySort) }
            val h1 = lxf.makeConstant("h1", skeySort)
            val h2 = lxf.makeConstant("h2", skeySort)
            listOf(
                lxf {
                    or(
                        x1 neq y1,
                        x2 neq y2,
                        x3 neq y3,
                    )
                },
                lxf { h1 eq keccack(x1, x2, x3) },
                lxf { h2 eq keccack(y1, y2, y3) },
                lxf { h1 eq h2 },
            )
        }

    @Test
    fun nonCollisionSameArity01Legacy() {
        val res = MockLExpToSmtLib.setupAndCheck(
            niaLegacyHashingTestSetup,
            formulaNonCollisionSameArity01(),
        )
        assertEquals(SatResult.UNSAT, res.satResult)
    }

    @Test
    fun nonCollisionSameArity01Datatypes() {
        val res = MockLExpToSmtLib.setupAndCheck(
            niaDatatypesHashingTestSetup,
            formulaNonCollisionSameArity01(),
        )
        assertEquals(SatResult.UNSAT, res.satResult)
    }

    @Test
    fun nonCollisionSameArity01PlainInjectivity() {
        val res = MockLExpToSmtLib.setupAndCheck(
            niaPlainInjectivityHashingTestSetup,
            formulaNonCollisionSameArity01(),
        )
        assertEquals(SatResult.UNSAT, res.satResult)
    }

    /**
     * Creates a formula for testing the "hash functions of different arities can't collide" feature of our hashing.
     */
    private fun formulaNonCollisionDifferentArities01(): (LExpressionFactory) -> List<LExpression> =
        { lxf: LExpressionFactory ->
            val x = lxf.makeConstant("x", skeySort)
            val y = lxf.makeConstant("y", skeySort)
            val z = lxf.makeConstant("z", skeySort)
            val h1 = lxf.makeConstant("h1", skeySort)
            val h2 = lxf.makeConstant("h2", skeySort)

            listOf(
                // nb we can't directly equate the two apply expressions for this test because
                // ConstantComputerWithHashSimplifications transforms that equality into `false` and we want to
                // test the axiomatization, not the ConstantComputer
                lxf { h1 eq keccack(x) },
                lxf { h2 eq keccack(y, z) },
                lxf { h1 eq h2 },
            )
        }

    @Test
    fun nonCollisionDifferentArities01Legacy() {
        val res = MockLExpToSmtLib.setupAndCheck(
            niaLegacyHashingTestSetup,
            formulaNonCollisionDifferentArities01(),
        )
        assertEquals(SatResult.UNSAT, res.satResult)
    }

    @Test
    fun nonCollisionDifferentArities01Datatypes() {
        val res = MockLExpToSmtLib.setupAndCheck(
            niaDatatypesHashingTestSetup,
            formulaNonCollisionDifferentArities01(),
        )
        assertEquals(SatResult.UNSAT, res.satResult)
    }

    @Test
    fun nonCollisionDifferentArities01Pi() {
        val res = MockLExpToSmtLib.setupAndCheck(
            niaPlainInjectivityHashingTestSetup,
            formulaNonCollisionDifferentArities01(),
        )
        assertEquals(SatResult.UNSAT, res.satResult)
    }

    private fun LExpressionFactory.makeConstant(name: String, type: Tag = Tag.Bit256) =
        this.const(name, type, null)

    /**
     * Creates a formula for testing the "large gaps" feature of our hashing.
     *
     * @param addition allows to switch out the addition operation (e.g. in data types hashing we might want to use
     *          skeyadd)
     */
    private fun formulaLargeGaps01(
        additiveOffsetUpperBound: BigInteger = EVM_MOD_GROUP256,
    ): (LExpressionFactory) -> List<LExpression> =
        { lxf: LExpressionFactory ->
            val x = lxf.makeConstant("x", skeySort)
            val y = lxf.makeConstant("y", skeySort)
            val z = lxf.makeConstant("z", Tag.Bit256)
            val h1 = lxf.makeConstant("h1", skeySort)
            val h2 = lxf.makeConstant("h2", skeySort)
            listOf(
                lxf { x neq y },
                lxf { h1 eq keccack(x) },
                lxf { h2 eq keccack(y) },
                lxf { z.within(litInt(0), litInt(additiveOffsetUpperBound)) },
                lxf { applyExp(NonSMTInterpretedFunctionSymbol.Hash.SkeyAdd, h1, z) eq h2 },
            )
        }

    @Test
    fun largeGapsLegacy01() {
        val res = MockLExpToSmtLib.setupAndCheck(
            niaLegacyHashingTestSetup,
            formulaLargeGaps01()
        )
        assertEquals(SatResult.UNSAT, res.satResult)
    }

    @Test
    fun largeGapsLegacy02GapSizeTooSmall() {
        val res = MockLExpToSmtLib.setupAndCheck(
            getNiaLegacyHashingTestSetup(gapSize = BigInteger.valueOf(256L)),
            formulaLargeGaps01()
        )
        assertEquals(SatResult.SAT, res.satResult)
    }

    @Test
    fun largeGapsLegacy02OffsetSmallEnough() {
        val res = MockLExpToSmtLib.setupAndCheck(
            getNiaLegacyHashingTestSetup(gapSize = BigInteger.valueOf(256L)),
            formulaLargeGaps01(additiveOffsetUpperBound = BigInteger.valueOf(256L))
        )
        assertEquals(SatResult.UNSAT, res.satResult)
    }

    @Test
    fun largeGapsDatatypes01() {
        val res = MockLExpToSmtLib.setupAndCheck(
            niaDatatypesHashingTestSetup,
            formulaLargeGaps01()
        )
        assertEquals(SatResult.UNSAT, res.satResult)
    }

    @Test
    fun largeGapsPi01() {
        val res = MockLExpToSmtLib.setupAndCheck(
            niaPlainInjectivityHashingTestSetup,
            formulaLargeGaps01()
        )
        assertEquals(SatResult.UNSAT, res.satResult)
    }

    /**
     * Creates a formula for testing the "reserved slots" feature of our hashing.
     *
     * TODO: this test is wrong (created before separation of to_skey and "basic"); it should be sat
     *   - make this into a test "collision with symbolic skey" (collisions can happen)
     *   - make a test "non-collision with basic" -- replace x with a small constant
     *        (and, in a variant with something symbolic but small)
     */
    private fun formulaReservedSlots01(
        maxSoliditySlot: BigInteger = Config.MaxBaseStorageSlot.get(),
    ): (LExpressionFactory) -> List<LExpression> =
        { lxf: LExpressionFactory ->
            val x = lxf.makeConstant("x", Tag.Bit256)
            val xToSkey = lxf.makeConstant("xToSkey", skeySort)
            val z = lxf.makeConstant("z", Tag.Bit256)
            val h1 = lxf.makeConstant("h1", skeySort)
            listOfNotNull(
                lxf { xToSkey eq toSkey(x) },
                lxf { h1 eq keccack(xToSkey) },
                lxf { z.within(litInt(0), litInt(maxSoliditySlot)) },
                lxf { applyExp(NonSMTInterpretedFunctionSymbol.Hash.ToSkey, z) eq h1 },
            )
        }

    @Test
    fun reservedSlotsLegacy01() {
        val res = MockLExpToSmtLib.setupAndCheck(
            niaLegacyHashingTestSetup,
            formulaReservedSlots01()
        )
        assertEquals(SatResult.UNSAT, res.satResult)
    }

    /**
     * actually used slot exceeds the `maxSoliditySlot` information we give to the axiom generator
     * --> expected to collide
     * (we also need to decrease the gapSize to trigger this)
     */
    @Test
    fun reservedSlotsLegacy02() {
        val res = MockLExpToSmtLib.setupAndCheck(
            getNiaLegacyHashingTestSetup(maxSoliditySlot = 3000.toBigInteger(), gapSize = BigInteger.valueOf(3000L)),
            formulaReservedSlots01(maxSoliditySlot = 5000.toBigInteger())
        )
        assertEquals(SatResult.SAT, res.satResult)
    }

    @Test
    fun reservedSlotsDatatypes01() {
        val res = MockLExpToSmtLib.setupAndCheck(
            niaDatatypesHashingTestSetup,
            formulaReservedSlots01()
        )
        assertEquals(SatResult.UNSAT, res.satResult)
    }

    @Test
    fun reservedSlotsPi01() {
        val res = MockLExpToSmtLib.setupAndCheck(
            niaPlainInjectivityHashingTestSetup,
            formulaReservedSlots01()
        )
        assertEquals(SatResult.UNSAT, res.satResult)
    }
}

