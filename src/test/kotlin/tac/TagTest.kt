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

package tac

import annotations.PollutesGlobalState
import config.CommandLineParser
import config.Config
import config.ConfigScope
import config.ConfigType
import io.mockk.every
import io.mockk.mockk
import kotlinx.coroutines.runBlocking
import log.*
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import report.DummyLiveStatsReporter
import scene.IScene
import solver.SolverResult
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder
import vc.data.TACSymbol
import vc.data.asTACSymbol
import vc.data.parser.serializeTAC
import verifier.TACVerifier
import java.io.File

class TagTest : TACBuilderAuxiliaries() {

    private val mockScene = mockk<IScene>()
    init { every { mockScene.getContracts() } returns listOf() }

    private val baseTags = setOf<Tag>(
        Tag.Int,
        Tag.Bit32,
        Tag.Bit64,
        Tag.Bit128,
        Tag.Bit256,
        Tag.Bit512,
        Tag.Bool,
        Tag.ByteMap,
        Tag.WordMap
    )

    private val complexTags = setOf(
        Tag.UserDefined.UninterpretedSort("sort"),
        Tag.UserDefined.Struct(
            "struct",
            baseTags.mapIndexed { idx, t -> Tag.UserDefined.Struct.Field("${t}${idx}", t) }),
    ) + baseTags.map { Tag.GhostMap(listOf(it), it) } + baseTags.zipWithNext()
        .map { Tag.GhostMap(it.toList(), it.first) }

    private fun <T> testUnique(tags: Set<Tag>, transform: (Tag) -> T) {
        Assertions.assertEquals(tags.size, tags.map(transform).distinct().size)
    }

    @Test
    fun testHashCodes() {
        testUnique(baseTags + complexTags) { it.hashCode() }
    }

    @Test
    fun testToString() {
        testUnique(baseTags + complexTags) { it.toString() }
    }

    @Test
    fun baseTagsStability() {
        baseTags.forEach {
            Assertions.assertEquals(it::class.java.name.hashCode(), it.hashCode()) { "Unexpected hashcode of $it (first variant)" }
            Assertions.assertEquals(it.javaClass.name.hashCode(), it.hashCode()) { "Unexpected hashcode of $it (second variant)" }
        }
    }

    @Test
    fun testBitwidthUniqueness() {
        val bitTags = listOf(
            Tag.Bits(8),
            Tag.Bits(8),
            Tag.Bits(16),
            Tag.Bits(32),
            Tag.Bits(64),
            Tag.Bits(128),
            Tag.Bits(256),
            Tag.Bits(512),
            Tag.Bit32,
            Tag.Bit64,
            Tag.Bit128,
            Tag.Bit256,
            Tag.Bit512,
        )
        bitTags.forEach { bi ->
            bitTags.forEach { bj ->
                Assertions.assertEquals(bi.bitwidth == bj.bitwidth, bi == bj, "$bi == $bj")
            }
        }
        listOf(Tag.Bit32, Tag.Bit64, Tag.Bit128, Tag.Bit256, Tag.Bit512).forEach { first ->
            val second = Tag.Bits(first.bitwidth)
            Assertions.assertTrue(first === second) { "identity: $first === $second" }
        }
    }

    @Test
    fun testBit64() {
        runBlocking {
            val ctp = TACProgramBuilder {
                val a = newVar("a64", Tag.Bit64)
                val b = newVar("b64", Tag.Bit64)
                a assign 123.asTACSymbol(Tag.Bit64).asSym()
                b assign Add(a.asSym(), a.asSym())
                x assign Eq(a.asSym(), b.asSym())
                assert(x.asSym())
            }.code
            val res = TACVerifier.verify(mockScene, ctp, DummyLiveStatsReporter)
            assert(res.firstExampleInfo.solverResult == SolverResult.SAT)
        }
    }

    @Test
    fun testBit40() {
        runBlocking {
            val ctp = TACProgramBuilder {
                val a = newVar("a40", Tag.Bits(40))
                val b = newVar("b40", Tag.Bits(40))
                a assign 123.asTACSymbol(Tag.Bits(40)).asSym()
                b assign Add(a.asSym(), a.asSym())
                x assign Eq(a.asSym(), b.asSym())
                assert(x.asSym())
            }.code
            val res = TACVerifier.verify(mockScene, ctp, DummyLiveStatsReporter)
            assert(res.firstExampleInfo.solverResult == SolverResult.SAT)
        }
    }

    @Test
    fun serializeAndDeserializeTest() {
        val key = MetaKey<TACSymbol.Var>("test-key")
        val preSerializeCTP = TACProgramBuilder {
            val a = newVar("a8", Tag.Bits(8))
            a assign 123.asTACSymbol(Tag.Bits(8)).asSym()
            val b = newVar("b16", Tag.Bits(16))
            b assign 123.asTACSymbol(Tag.Bits(16)).asSym()
            val c = newVar("c32", Tag.Bit32)
            c assign 123.asTACSymbol(Tag.Bit32).asSym()
            val d = newVar("d64", Tag.Bit64)
            d assign 123.asTACSymbol(Tag.Bit64).asSym()
            val e = newVar("e128", Tag.Bit128)
            e assign 123.asTACSymbol(Tag.Bit128).asSym()
            val f = newVar("f256", Tag.Bit256)
            f assign 123.asTACSymbol(Tag.Bit256).asSym()
            val g = newVar("g512", Tag.Bit512)
            g assign 123.asTACSymbol(Tag.Bit512).asSym()
            val h = newVar("h40", Tag.Bits(40))
            h assign 123.asTACSymbol(Tag.Bits(40)).asSym()
            addMetaToLastCmd(key, h)
        }.code

        ConfigScope(Config.VerifyTACDumps, true).use {
            val path = File("test.tac")
            try {
                Assertions.assertDoesNotThrow {
                    serializeTAC(preSerializeCTP, path.absolutePath)
                }
            } finally {
                path.delete()
            }
        }
    }
}
