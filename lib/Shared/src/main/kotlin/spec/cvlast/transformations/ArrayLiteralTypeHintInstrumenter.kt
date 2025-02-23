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

package spec.cvlast.transformations

import spec.cvlast.CVLCmd
import spec.cvlast.CVLExp
import spec.cvlast.transformer.CVLAstTransformer
import spec.cvlast.transformer.CVLCmdTransformer
import spec.cvlast.transformer.CVLExpTransformer
import utils.CollectingResult
import utils.CollectingResult.Companion.lift

object ArrayLiteralTypeHintInstrumenter : CVLAstTransformer<Nothing>(
    cmdTransformer = object : CVLCmdTransformer<Nothing>(
        expTransformer = object : CVLExpTransformer<Nothing> { }
    ) {
        override fun def(cmd: CVLCmd.Simple.Definition): CollectingResult<CVLCmd, Nothing> {
            return if(cmd.type != null && cmd.exp is CVLExp.ArrayLitExp) {
                check(cmd.idL.size == 1)
                cmd.copy(
                    exp = cmd.exp.updateTag(
                        cmd.exp.tag.copy(
                            annotation = CVLExp.ArrayLitExp.ArrayLiteralTypeHint(cmd.type)
                        )
                    )
                ).lift()
            } else {
                super.def(cmd)
            }
        }
    }
)
