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

package analysis.smtblaster

import smtlibutils.data.*

abstract class AbstractSmtExpTermBuilder: ISMTTermBuilder<Sort, SmtExp> {
    val script = FactorySmtScript

    override fun eq(op1: SmtExp, op2: SmtExp): SmtExp {
        return script.apply(SmtIntpFunctionSymbol.Core.Eq(), op1, op2)
    }

    override fun toIdent(string: String): SmtExp {
        return script.qualIdentifier(script.simpleIdentifier(string))
    }

    override fun land(ops: List<SmtExp>): SmtExp {
        return script.and(*ops.toTypedArray())
    }

    override fun lor(op: List<SmtExp>): SmtExp {
        return script.or(*op.toTypedArray())
    }

    override fun lnot(op: SmtExp): SmtExp {
        return script.not(op)
    }

    override fun ite(cond: SmtExp, trBranch: SmtExp, falseBranch: SmtExp): SmtExp {
        return script.apply(SmtIntpFunctionSymbol.Core.Ite(), cond, trBranch, falseBranch)
    }

    override fun apply(f: String, ops: List<SmtExp>): SmtExp {
        return script.apply(SmtFunctionSymbol.fromIdentifier(script.simpleIdentifier(f)), ops.toList())
    }

    abstract fun fork() : AbstractSmtExpTermBuilder
}