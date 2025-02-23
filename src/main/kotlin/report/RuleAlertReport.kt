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

package report

import datastructures.NonEmptyList
import kotlinx.serialization.json.*
import datastructures.stdcollections.*
import datastructures.toNonEmptyList
import utils.CertoraException

sealed class RuleAlertReport<out T: RuleAlertReport.Single<T>> {

    abstract val asList: List<T>

    fun join(other: RuleAlertReport<*>?) = flatten(listOfNotNull(this, other))

    companion object {
        infix fun RuleAlertReport<*>?.join(other: RuleAlertReport<*>?): RuleAlertReport<*>? = this?.join(other) ?: other

        operator fun<T: Single<T>> invoke(ruleAlertReports: List<T>): RuleAlertReport<T>? =
            ruleAlertReports.toNonEmptyList()?.let(::invoke)

        operator fun <T : Single<T>> invoke(ruleAlertReports: NonEmptyList<T>): RuleAlertReport<T> =
            if (ruleAlertReports.size == 1) {
                ruleAlertReports.head
            } else {
                Multiple(
                    ruleAlertReports.head, ruleAlertReports[1], ruleAlertReports.subList(2, ruleAlertReports.size)
                )
            }

        fun flatten(ruleAlertReports: List<RuleAlertReport<*>?>) =
            RuleAlertReport(
                mutableListOf<Single<*>>().also {
                    ruleAlertReports.forEach { ruleAlertReport ->
                        when (ruleAlertReport) {
                            null -> { }
                            is Single<*> -> it.add(ruleAlertReport)
                            is Multiple<*> -> it.addAll(ruleAlertReport.asList)
                        }
                    }
                }
            )

        /**
         * In the case of a success, returns the result (of type [T]).
         * Otherwise, returns the specified default result ([default]) along with
         * a [RuleAlertReport.Error], containing the specified error message.
         */
        fun <T> Result<T>.getOrDefaultWithAlert(
            default: T,
            alertMsg: String
        ): Pair<T, Error?> = this.fold(
            onSuccess = { it to null },
            onFailure = {
                default to
                    Error(
                        msg = alertMsg + it.message?.let { throwableMsg -> " $throwableMsg" }.orEmpty(),
                        throwable = it
                    )
            }
        )

    }

    /**
     * Alerts that should appear in problems view of a specific rule.
     * @property msg: detailed description of the alert
     * @property severity: info, warning or error
     * @property reason: a possible exception that causes the alert
     */
    sealed class Single<out T : Single<T>> : RuleAlertReport<T>(), TreeViewReportable {
        abstract val msg: String
        abstract val severity: String
        abstract val reason: CertoraException?
        override val treeViewRepBuilder = TreeViewRepJsonObjectBuilder {
            put(key = TreeViewReportAttribute.SEVERITY(), value = severity)
            put(key = TreeViewReportAttribute.MESSAGE(), value = msg)
        }
        protected fun checkMsgIsNotEmpty() {
            check(msg.isNotEmpty()) {
                "Was about to create a new RuleAlertReport.Single with an empty message (alert severity: $severity)"
            }
        }
    }

    data class Info(override val msg: String, override val reason: CertoraException? = null) : Single<Info>() {
        init {
            checkMsgIsNotEmpty()
        }

        override val asList: List<Info> = listOf(this)
        override val severity: String
            get() = "info"
    }

    data class Warning(override val msg: String, override val reason: CertoraException? = null) : Single<Warning>() {
        init {
            checkMsgIsNotEmpty()
        }
        constructor(msg: String, throwable: Throwable?) : this(
            msg, throwable?.let { CertoraException.fromException(throwable) }
        )

        override val asList: List<Warning> = listOf(this)
        override val severity: String
            get() = "warning"
    }

    data class Error(override val msg: String, override val reason: CertoraException? = null) : Single<Error>() {
        init {
            checkMsgIsNotEmpty()
        }
        constructor(msg: String, throwable: Throwable?) : this(
            msg, throwable?.let { CertoraException.fromException(throwable) }
        )

        override val asList: List<Error> = listOf(this)
        override val severity: String
            get() = "error"
    }

    /**
     * Holds at least two [RuleAlertReport.Single]s.
     */
    data class Multiple<out T: Single<T>>(val firstAlert: T, val secondAlert: T, val otherAlerts: List<T>): RuleAlertReport<T>() {

        override val asList: List<T> = mutableListOf<T>().also {
            it.add(firstAlert)
            it.add(secondAlert)
            it.addAll(otherAlerts)
        }
    }

}
