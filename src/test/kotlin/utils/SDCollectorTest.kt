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

package utils

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import statistics.*

class SDCollectorTest {
    @Test
    fun uniqueByType() {
        val features =
            listOf(
                AggregatedElapsedTimeStats(ElapsedTimeStats()),
                ElapsedTimeStats(),
                TimeStampStats(),
                ScalarKeyValueStats<String>(),
                ScalarKeyValueStats<Boolean>(),
                GeneralKeyValueStats<String>(),
                GeneralKeyValueStats<Boolean>(),
            )
        val feature = features.first()
        Assertions.assertTrue(features.drop(1).all { it.fullFeatureKey() != feature.fullFeatureKey() })
    }

    @Test
    fun immutableFork() {
        val features =
            listOf(
                AggregatedElapsedTimeStats(ElapsedTimeStats()),
                ElapsedTimeStats(),
                TimeStampStats(),
                ScalarKeyValueStats(),
                GeneralKeyValueStats(),
            )
        for (feature in features) {
            feature.extractedData.addAll((0L..6L).map { SDElement("$it".toTimeTag(), it) })
            val forked = feature.fork("fork".toSDFeatureKey(), "it".toSDFeatureKey())
            Assertions.assertEquals(feature.extractedData, forked.extractedData)
            feature.extractedData.addAll((10L..16L).map { SDElement(StatsTag("$it"), it) })
            Assertions.assertNotEquals(feature.extractedData, forked.extractedData)
        }
    }

    @Test
    fun aggregateFromElapsed() {
        val elapsedTimeStats =
            ElapsedTimeStats(extractedData = (0L..6L).map { SDElement("${it % 2}".toTimeTag(), it) }.toMutableList())
        val aggregated =
            AggregatedElapsedTimeStats(elapsedTimeStats).let { it.descriptor.describeData(it.extractedData) }
        Assertions.assertEquals(aggregated.values.sum(), (0L..6L).sum())
        Assertions.assertEquals(aggregated["0"], (0L..6L).step(2).sum())
        Assertions.assertEquals(aggregated["1"], (1L..6L).step(2).sum())
    }
}
