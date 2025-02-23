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

@file:kotlinx.serialization.UseSerializers(BigIntegerSerializer::class)
package vc.data

import allocator.SuppressRemapWarning
import cache.utils.ObjectSerialization
import kotlinx.serialization.json.Json
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.io.TempDir
import tac.MetaKey
import utils.AmbiSerializable
import utils.BigIntegerSerializer
import utils.DataOutputEncoder
import utils.letIf
import vc.data.parser.ReadableTACJson
import java.io.FileReader
import java.io.ObjectOutputStream
import java.io.OutputStream
import java.io.Serializable
import java.nio.file.Path
import java.math.BigInteger
import java.security.DigestOutputStream
import java.security.MessageDigest
import java.util.*


/**
 * These tests suggest that java's singleton set, used under the hood for single-element sets in kotlin is responsible
 * for "java serialization inconsistencies".
 *
 * By "serialization inconsistencies", we mean that the original object and the roundtrip result are not the same,
 * even though this cannot be detected by kotlin equality. By kotlin equality the objects agree, but the
 * MD5 digests of these objects are different.
 *
 * In this case, the object in question is an annotation, whose value field is a class (PushRecordMock)
 * containing a particular instance of CallSummary as a member. PushRecordMock is on purpose NOT KSerializble, so that
 * serializing it as the value of the annotation will fall back to JavaBlobSerializer.
 *
 * The sigResolution field of CallSummary is seen at runtime to be a java singleton set. As the tests show, if
 * we replace sigResolution in our CallSummary instance with an empty set, the digests of the resulting annotation are
 * consistent. Otherwise, they are not.
 *
 * Moreover, we show an attempt at further isolating the issue which does not work: Namely, we run the experiment with a
 * mock version of call summary whose only field is a one element set. We see that the digests in this case remain consistent.
 *
 * This suggests that the way sigResolution is serialized as a part of call summary depends on more context that just
 * the content of the field itself.
 *
 */
class CallSummarySerializationInconsistency {
    @TempDir
    lateinit var tempDir: Path

    // Not KSerializable on purpose!!!
    @SuppressRemapWarning
    data class PushRecordMock(val callSummary: CallSummary?) : Serializable

    @SuppressRemapWarning
    data class PushRecordMockWithCallSummaryMock(val callSummary: CallSummaryMock?) : Serializable

    @kotlinx.serialization.Serializable
    data class CallSummaryMock(val sigResolution: Set<BigInteger>) : AmbiSerializable

    object Meta {
        val STACK_PUSH_MOCK = MetaKey<PushRecordMock>("call.trace.push.mock")
        val STACK_PUSH_SUMMARY_MOCK = MetaKey<PushRecordMockWithCallSummaryMock>("call.trace.push.mock.mock")
    }

    private fun getProblematicCallSummary(): CallSummary {
        val path = "src/test/kotlin/vc/data/problematicCallSummary.txt"
        // CallSummary internally contains CallInput, which has a map (`rangeToDecomposedArg`)
        // whose keys are classes (structured)
        val jsonDecoder = Json { allowStructuredMapKeys = true }
        return jsonDecoder.decodeFromString(CallSummary.serializer(), FileReader(path).readText())
    }

    @Test
    fun mockPushRecordWithMockCallSummary() {
        val callSummary = CallSummaryMock(sigResolution = setOf(BigInteger("2515520926")))
        val annot = TACCmd.Simple.AnnotationCmd.Annotation(Meta.STACK_PUSH_SUMMARY_MOCK, PushRecordMockWithCallSummaryMock(callSummary))
        val digestBefore = annot.digest()

        val annotAfter = annot.roundTrip()
        val digestAfter = annotAfter.digest()

        // For some reason mocking the summary is not good enough, we still get that the digests are equal
        assertTrue(digestBefore == digestAfter) { "Inconsistent digests" }
    }

    @Test
    fun mockPushRecordWithRealCallSummary() {
        testDigestConsistency(true)
        testDigestConsistency(false)
    }

    private fun testDigestConsistency(emptySigResolution: Boolean) {
        val callSummary =
            getProblematicCallSummary()
                .letIf(emptySigResolution) {
                    it.copy(sigResolution = setOf())
                }


        val annot = TACCmd.Simple.AnnotationCmd.Annotation(Meta.STACK_PUSH_MOCK, PushRecordMock(callSummary))
        val roundTripped = annot.roundTrip()

        val digestBefore = annot.digest()
        val digestAfter = roundTripped.digest()

        assertTrue(digestBefore == digestAfter)
    }

    private fun <T : Serializable> T.roundTrip(): T {
        val path = tempDir.resolve("obj.bin").toString()
        ObjectSerialization.writeObject(this, path)
        return ObjectSerialization.readObject(path)
    }

    private fun <T : Serializable> TACCmd.Simple.AnnotationCmd.Annotation<T>.digest(): String {

        val dos =
            DigestOutputStream(OutputStream.nullOutputStream(), MessageDigest.getInstance("MD5"))

        val dataEncoderBefore = DataOutputEncoder(ObjectOutputStream(dos), ReadableTACJson.serializersModule)

        dataEncoderBefore.encodeSerializableValue(
            TACCmd.Simple.AnnotationCmd.Annotation.Serializer,
            this
        )
        return Base64.getUrlEncoder().withoutPadding().encodeToString(dos.messageDigest.digest())
    }
}
