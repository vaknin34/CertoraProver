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

package config.component

import config.ConfigType
import config.TransformationAgnosticConfig
import org.apache.commons.cli.Option

object EventConfig {

    const val EVENT_TAG_MAX_LENGTH: Int = 45
    const val MAX_EVENT_TAGS: Int = 3

    val UserDefinedEventTags: ConfigType.StringSetCmdLine = object : ConfigType.StringSetCmdLine(
        null,
        Option(
            "eventTags",
            true,
            "user-defined tag that can be used to label related events"
        )
    ), TransformationAgnosticConfig {

        override fun check(newValue: HashSet<String>): Boolean = newValue.size <= MAX_EVENT_TAGS &&
            newValue.all { it.length <= EVENT_TAG_MAX_LENGTH }

        override fun illegalArgMessage(newValue: HashSet<String>): String =
            if (newValue.size > MAX_EVENT_TAGS) {
                "Maximum $MAX_EVENT_TAGS tags are allowed but found ${newValue.size}"
            } else {
                val tooLongTags = newValue.filter { it.length > EVENT_TAG_MAX_LENGTH }
                require(tooLongTags.isNotEmpty()) {
                    "Expected $newValue to have a string whose length is longer than $EVENT_TAG_MAX_LENGTH "
                }
                "The following tags are too long: $tooLongTags. Tag's length must not exceed $EVENT_TAG_MAX_LENGTH"
            }
    }

    val EnableEventReporting: ConfigType.BooleanCmdLine = object : ConfigType.BooleanCmdLine(
        true,
        Option(
            "enableEventReporting",
            true,
            "set whether to enable event reporting  [default: true]"
        )
    ), TransformationAgnosticConfig {
        override fun illegalArgMessage(newValue: Boolean): String = ""
    }

}
