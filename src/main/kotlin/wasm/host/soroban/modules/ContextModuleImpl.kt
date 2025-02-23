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

package wasm.host.soroban.modules

import analysis.CommandWithRequiredDecls.Companion.mergeMany
import datastructures.stdcollections.*
import tac.*
import vc.data.*
import wasm.host.soroban.*
import wasm.host.soroban.types.*
import wasm.tacutils.*
import wasm.traps.*

internal object ContextModuleImpl : ModuleImpl() {
    fun init() = mergeMany(
        assignHavoc(TACKeyword.SOROBAN_LEDGER_VERSION.toVar()),
        assignHavoc(TACKeyword.SOROBAN_LEDGER_SEQUENCE.toVar()),
        assignHavoc(TACKeyword.SOROBAN_LEDGER_TIMESTAMP.toVar()),
        assignHavoc(TACKeyword.SOROBAN_MAX_LIVE_UNTIL_LEDGER.toVar()),
        BytesType.new(TACKeyword.SOROBAN_LEDGER_NETWORK_ID.toVar()) { 32.asTACExpr }
    )

    override fun getFuncImpl(funcName: String, args: List<TACSymbol>, retVar: TACSymbol.Var?) =
        when(funcName) {
            "log_from_linear_memory" -> noVisibleEffect()
            "contract_event" -> noVisibleEffect()

            "fail_with_error" -> Trap.trap("fail_with_error")

            "get_current_contract_address" -> Contract.getCurrentAddress(retVar!!)

            "get_ledger_version" -> getLedgerVersion(retVar!!)
            "get_ledger_sequence" -> getLedgerSequence(retVar!!)
            "get_ledger_timestamp" -> getLedgerTimestamp(retVar!!)
            "get_ledger_network_id" -> getLedgerNetworkId(retVar!!)
            "get_max_live_until_ledger" -> getMaxLiveUntilLedger(retVar!!)

            "obj_cmp" -> compareObjects(retVar!!, args[0], args[1])

            else -> null
        }

    fun getLedgerVersion(dest: TACSymbol.Var) =
        assign(dest) { TACKeyword.SOROBAN_LEDGER_VERSION.toVar().asSym() }

    fun getLedgerSequence(dest: TACSymbol.Var) =
        assign(dest) { TACKeyword.SOROBAN_LEDGER_SEQUENCE.toVar().asSym() }

    fun getLedgerTimestamp(dest: TACSymbol.Var) =
        assign(dest) { TACKeyword.SOROBAN_LEDGER_TIMESTAMP.toVar().asSym() }

    fun getLedgerNetworkId(dest: TACSymbol.Var) =
        assign(dest) { TACKeyword.SOROBAN_LEDGER_NETWORK_ID.toVar().asSym() }

    fun getMaxLiveUntilLedger(dest: TACSymbol.Var) =
        assign(dest) { TACKeyword.SOROBAN_MAX_LIVE_UNTIL_LEDGER.toVar().asSym() }

    /**
        Compares two vals for equality.  This is a structural comparison, so we compare digests rather than comparing
        the vals directly.  We do not support ordering semantics at this time; unequal vals result in a nondet result
        of 1 or -1.
     */
    private fun compareObjects(retVar: TACSymbol.Var, obj1: TACSymbol, obj2: TACSymbol) =
        Val.withDigest(obj1.asSym()) { obj1Digest ->
            Val.withDigest(obj2.asSym()) { obj2Digest ->
                mergeMany(
                    assignHavoc(retVar),
                    assume {
                        ((obj1Digest eq obj2Digest) implies (retVar.asSym() eq 0.asTACExpr)) and (
                            (obj1Digest neq obj2Digest) implies (
                                (retVar.asSym() eq 1.asTACExpr) or (retVar.asSym() eq (0.asTACExpr sub 1.asTACExpr))
                            )
                        )
                    }
                )
            }
        }
}
