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

package config

import annotations.PollutesGlobalState
import datastructures.stdcollections.listOf

@PollutesGlobalState
sealed class AWSConfig(default: String, name: String, private val envVarName: String) :
    ConfigType<String>(default, name, postponeRegister = true),
    TransformationAgnosticConfig {

    companion object {

        val QUEUES = listOf(
            "events.fifo",       // The notification events queue
            "testEvents.fifo"   // Queue for testing purposes
        )

        val REGIONS = listOf(
            "us-east-1", // N. Virginia
            "us-east-2", // Ohio
            "us-west-1", // N. California
            "us-west-2", // Oregon
            "ap-east-1", // Hong Kong
            "ap-south-1", // Mumbai
            "ap-northeast-1", // Tokyo
            "ap-northeast-2", // Seoul
            "ap-northeast-3", // Osaka-Local
            "ap-southeast-1", // Singapore
            "ap-southeast-2", // Sydney
            "ca-central-1", // Central
            "eu-central-1", // Frankfurt
            "eu-west-1", // Ireland
            "eu-west-2", // London
            "eu-west-3", // Paris
            "eu-north-1", // Stockholm
            "me-south-1", // Bahrain
            "sa-east-1" // Sao Paulo
        )
    }

    init {
        System.getenv(envVarName)?.also(::set)
        register()
    }

    object AWSRegion : AWSConfig(
        "us-west-2",
        "AWSRegion",
        "AWS_REGION"
    ) {
        override fun check(newValue: String): Boolean =
            checkRegionName(newValue) // check if it is a valid name w.r.t. AWS API

        override fun illegalArgMessage(newValue: String): String = "Illegal AWS region name"

    }

    object SQSQueueName : AWSConfig(
        "events.fifo",
        "EventQueue",
        "QUEUE_NAME"
    ) {
        // queue name must end with ".fifo"
        override fun check(newValue: String): Boolean =
            checkQueueName(newValue)
        override fun illegalArgMessage(newValue: String): String = "Illegal AWS SQS queue name"

    }


    fun checkQueueName(queue: String): Boolean {
        return QUEUES.contains(queue)
    }

    fun checkRegionName(region: String): Boolean {
        return REGIONS.contains(region)
    }

}
