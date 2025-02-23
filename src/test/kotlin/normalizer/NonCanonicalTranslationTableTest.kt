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

package normalizer

import annotation.SolidityVersion
import annotation.SolidityVersions
import annotation.WithOptimizedFlag
import infra.CVLFlow
import loaders.SolidityContractTest
import loaders.SoliditySceneTest
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import parallel.ParallelPool.Companion.runInherit
import parallel.Scheduler.compute
import parallel.forkEvery
import parallel.pcompute
import tac.MetaKey
import utils.`to?`
import vc.data.CoreTACProgram
import vc.data.TACCmd
import kotlin.random.Random
import kotlin.io.path.Path

class NonCanonicalTranslationTableTest : SolidityContractTest, SoliditySceneTest {
    private fun testPatching(solc: String, optimize: Boolean, vararg paths: String) {
        val baseRandomizer = Randomizer(Random(0))
        sequence { yield(baseRandomizer.fork()) }.zip(paths.asSequence()).toList()
            .forkEvery { (randomizer, path) ->
                compute {
                    loadTestContractMethod(path, solc, optimize).code as CoreTACProgram
                }.bind {
                    compute {
                        testPatching(listOf(it), randomizer)
                    }
                }
            }.pcompute().runInherit()
    }

    private fun testPatching(tacs: List<CoreTACProgram>, baseRandomizer: Randomizer) =
        tacs.map { it to baseRandomizer.fork() }.forkEvery { (ctp, randomizer) ->
            compute {
                val ptrs = (0..10).map {
                    val key = MetaKey<String>("test-key-${it}", restore = true)
                    val suffix = randomizer.nextInt()
                    Triple(ctp.randCmdPointer(randomizer), key, suffix)
                }

                val pushMetas = { value: String ->
                    ptrs.fold(ctp) { cur, (ptr, key, suffix) ->
                        cur.pushMeta(ptr, key, "$value$suffix")
                    }
                }
                val ctpHaha = pushMetas("haha")
                val ctpJaja = pushMetas("jaja")
                val ctpJajaDigest = ctpJaja.digest()
                // added non-canonical data - digest should be the same
                Assertions.assertEquals(ctpHaha.digest(), ctpJajaDigest)
                val (_, table) = NonCanonicalTranslationTable(ctpHaha)
                val (annotatedCtp, _) = NonCanonicalTranslationTable(ctpJaja)
                // annotating should affect the digest (since we added annotation keys)
                Assertions.assertNotEquals(annotatedCtp.digest(), ctpJajaDigest)

                val patchedCtp = table.patch(annotatedCtp)
                for ((ptr, key, suffix) in ptrs) {
                    Assertions.assertEquals(
                        annotatedCtp.code[ptr.block]!![ptr.pos].meta[key]!!, "jaja$suffix"
                    )
                    Assertions.assertEquals(
                        patchedCtp.code[ptr.block]!![ptr.pos].meta[key]!!, "haha$suffix"
                    )
                }

                val (annotatedCtp2X, _) = NonCanonicalTranslationTable(annotatedCtp)
                // re-annotating should not affect digest
                Assertions.assertEquals(annotatedCtp.digest(), annotatedCtp2X.digest())

                val patchedTransformedCtpJaja =
                    table.patch(modifyTopology(annotatedCtp, randomizer))
                patchedTransformedCtpJaja.parallelLtacStream().forEach { (_, cmd) ->
                    for ((suffix, value) in ptrs.mapNotNull { (_, key, suffix) -> suffix `to?` cmd.meta[key] }) {
                        Assertions.assertEquals("haha$suffix", value)
                    }
                }
            }
        }.pcompute().runInherit()


    /**
     * A utility use to create an annotatedCtp with different topology that can be patched
     * I.e. finding a Command by CmdPointer will not work
     * **/
    private fun modifyTopology(annotatedCtp: CoreTACProgram, randomizer: Randomizer): CoreTACProgram {
        // make sure the [CmdPointer]s are different
        val modifiedField = NBIdFieldSelector.FRESH_COPY
        val (mapper, _, _) = annotatedCtp.createNBIdMapper(modifiedField, randomizer)
        val (newBlocks, newGraph, procedures) = annotatedCtp.remap(mapper, Unit)
        // make sure te position in block is different
        val blocksWithNop = newBlocks.mapValues { (_, cmds) ->
            cmds.flatMap {
                listOfNotNull(
                    TACCmd.Simple.NopCmd.takeIf { randomizer.nextInt(cmds.size) == cmds.lastIndex },
                    it
                )
            }
        }
        return annotatedCtp.copy(code = blocksWithNop, blockgraph = newGraph, procedures = procedures)
    }


    @Test
    fun moolyExDefault() {
        testPatching(
            CVLFlow().transformResultsToTACs(CVLFlow().getProverQuery(Path("src/test/resources/cvl/NonLinear/MoolyEx/MoolyExDefault.conf"))),
            Randomizer(Random(0))
        )
    }


    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V6_1, SolidityVersion.V6_10])
    @WithOptimizedFlag
    fun testArrayAnalysisPatching(solc: String, optimize: Boolean) = testPatching(
        solc, optimize,
        "analysis/AbiDecode.sol",
        "analysis/AbiDecodeDynamic.sol",
        "analysis/AbiDecodeDynamicWide.sol",
        "analysis/TestDecodeReturnBuffer.sol",
        "analysis/StringReturn.sol",
        "analysis/ArrayArgument.sol",
        "analysis/ArrayAddressArgument.sol",
        "analysis/StringArgument.sol",
        "analysis/StringArgumentCalldata.sol",
        "analysis/EncodePacked.sol",
        "analysis/StorageStringPackedEncode.sol",
        "analysis/StructArrayArgument.sol",
        "analysis/StructWithArrayReturn.sol",
        "analysis/ConstantUintAlloc.sol",
        "analysis/ConstantStructAlloc.sol",
        "analysis/StringGetter.sol",
        "analysis/StringInMapGetter.sol",
        "analysis/OptimizedAddressReturn.sol",
    )

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V4_25, SolidityVersion.V7_0, SolidityVersion.V6_8, SolidityVersion.V6_10])
    @WithOptimizedFlag
    fun testConstantSizeDigests(solc: String, optimize: Boolean) = testPatching(
        solc, optimize,
        "analysis/ConstantUintAlloc.sol",
        "analysis/ConstantStructAlloc.sol",
        "analysis/StringGetter.sol",
        "analysis/StringInMapGetter.sol",
        "analysis/OptimizedAddressReturn.sol",
    )

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.ANY_4])
    @WithOptimizedFlag
    fun testInlineAssemblyDigests(solc: String, optimize: Boolean) =
        testPatching(solc, optimize, "analysis/InlineAssembly.sol")

    @ParameterizedTest
    @SolidityVersions(
        [SolidityVersion.V6_10, SolidityVersion.V7_0,
            SolidityVersion.V6_8, SolidityVersion.V8_2, SolidityVersion.V7_6, SolidityVersion.V8_11,
            SolidityVersion.V8_9, SolidityVersion.V8_13, SolidityVersion.V8_28]
    )
    @WithOptimizedFlag
    fun testABIV2EncodingDigests(solc: String, optimize: Boolean) = testPatching(
        solc, optimize,
        "analysis/StringReturn.sol",
        "analysis/ArrayArgument.sol",
        "analysis/ArrayAddressArgument.sol",
        "analysis/StringArgument.sol",
        "analysis/StringArgumentCalldata.sol",
        "analysis/EncodePacked.sol",
        "analysis/StorageStringPackedEncode.sol",
        "analysis/StructArrayArgument.sol",
        "analysis/StructWithArrayReturn.sol"
    )
}
