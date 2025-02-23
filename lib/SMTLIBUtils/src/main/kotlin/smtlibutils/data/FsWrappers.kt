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

package smtlibutils.data

fun SmtIntpFunctionSymbol.Companion.wrapBinary(exp: SmtExp.Apply): BinaryFsExpWrapper {
    check(exp.fs is SmtIntpFunctionSymbol)
    check(exp.args.size == 2)
    return BinaryFsExpWrapper(exp)
}
data class BinaryFsExpWrapper(val appExp: SmtExp.Apply) {
    val fs: SmtIntpFunctionSymbol = appExp.fs as SmtIntpFunctionSymbol
    val e1: SmtExp = appExp.args[0]
    val e2: SmtExp = appExp.args[1]
}


