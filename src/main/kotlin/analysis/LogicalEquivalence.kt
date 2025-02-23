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

package analysis

import vc.data.*
import analysis.smtblaster.*
import analysis.rustblaster.*
import vc.data.TACExpr
import vc.data.TACSymbol
import parser.*
import config.Config
import log.*
import smtlibutils.data.Cmd

object LogicalEquivalence {
    private val blaster = SmtExpBitBlaster()
    private val rustBlaster = RustBlasterPool(isDaemon = true)

    fun equiv(assume: List<Cmd>, e1: TACExpr, e2: TACExpr, blasterImpl: IBlaster) : Boolean {
        val testEgg = Config.TestMode.get()

        val restrictToBitvector = true
        val e1egg = TACToEgg.convert(e1, restrictToBitvector)
        val e2egg = TACToEgg.convert(e2, restrictToBitvector)

        // If the rust solver supports this expression, use it
        // TODO: Support assumptions so that we can run egg for more queries
        return if (e1egg != null && e2egg != null && assume.isEmpty()) {
            // Use the `logical_eq` function on the rust side, which determines if two
            // EggTAC expressions are equal with a given timeout at the third argument
            val eggStr = try {
                rustBlaster.blast("(logical_eq $e1egg $e2egg 250)")
            } catch (x: Exception) {
                // Fail in CI by asserting false
                // TODO always fail when the rust code is more stable
                Logger.alwaysError("Logical equality query failed when checking $e1egg = $e2egg", x)
                assert(false)
                return equivz3(assume, e1, e2, blasterImpl)?.first ?: false
            }

            val eggSexp = parseSexp(eggStr, 0).first

            // The egg solver can prove they are equal (UNSAT), unequal (SAT), or neither
            val (provedEqual, provedUnequal) = when (eggSexp) {
                is SList -> {
                    Pair(eggSexp.children[0].toString() == "true", eggSexp.children[1].toString() == "true")
                }
                else -> {
                    Logger.alwaysError("egg result is not a list: $eggStr")
                    assert(false)
                    return equivz3(assume, e1, e2, blasterImpl)?.first ?: false
                }
            }


            val eggDecided = provedEqual || provedUnequal

            // In testing mode, check that z3 and the egg solver agree
            if (testEgg) {
                val (z3res, z3timeout) = equivz3(assume, e1, e2, blasterImpl) ?: (false to true)
                if (!z3timeout && eggDecided && z3res != provedEqual) {
                    throw IllegalStateException("UNSOUNDNESS ERROR! egg proved a different result than z3\n Egg: $provedEqual \n Z3: $z3res")
                }
            }

            if (eggDecided) {
                provedEqual
            } else {
                // Fall back on z3 if egg couldn't decide
                equivz3(assume, e1, e2, blasterImpl)?.first ?: false
            }
        } else {
            equivz3(assume, e1, e2, blasterImpl)?.first ?: false
        }
    }

    private fun equivz3(assume: List<Cmd>, e1: TACExpr, e2: TACExpr, blasterImpl: IBlaster) : Pair<Boolean, Boolean>? {
        val freeVars = mutableSetOf<TACSymbol.Var>()
        val vm: (TACSymbol.Var) -> String = {
            freeVars.add(it)
            it.toSMTRep()
        }

        return blaster.blastExpr(e1, vm)?.let { smt1 ->
            blaster.blastExpr(e2, vm)?.let { smt2 ->
                val script = SmtExpScriptBuilder.buildBVScript(assume) {
                    for(freeVar in freeVars) {
                        declare(freeVar.toSMTRep())
                    }
                    define("first-expr") { smt1 }
                    define("second-expr") { smt2 }
                    assert {
                        lnot(eq(
                            toIdent("first-expr"),
                            toIdent("second-expr")
                        ))
                    }
                    checkSat()
                }
                blasterImpl.blastSmtOrTimeout(script)
            }
        }
    }

    fun equiv(e1: TACExpr, e2 : TACExpr) : Boolean {
        return equiv(listOf(), e1, e2, Z3Blaster)
    }

    // checks with z3 whether under [assume] the expressions [e1] and [e2] may alias.
    // if the result is sat, it found a way to render [e1]==[e2], otherwise they may not alias
    // returns a pair (unsat, timeout) where unsat = false if may alias
    private fun mayAliasZ3(assume: List<Cmd>, e1: TACExpr, e2: TACExpr, blasterImpl: IBlaster) : Pair<Boolean, Boolean>? {
        val freeVars = mutableSetOf<TACSymbol.Var>()
        val vm: (TACSymbol.Var) -> String = {
            freeVars.add(it)
            it.toSMTRep()
        }

        return blaster.blastExpr(e1, vm)?.let { smt1 ->
            blaster.blastExpr(e2, vm)?.let { smt2 ->
                val script = SmtExpScriptBuilder.buildBVScript(assume) {
                    for(freeVar in freeVars) {
                        declare(freeVar.toSMTRep())
                    }
                    define("first-expr") { smt1 }
                    define("second-expr") { smt2 }
                    assert {
                        eq(
                            toIdent("first-expr"),
                            toIdent("second-expr")
                        )
                    }
                    checkSat()
                }
                blasterImpl.blastSmtOrTimeout(script)
            }
        }
    }

    fun mayAlias(e1: TACExpr, e2: TACExpr) = mayAliasZ3(listOf(), e1, e2, Z3Blaster)?.let { (unsatEq, _) ->
        !unsatEq // if sat, then may alias
    }
}
