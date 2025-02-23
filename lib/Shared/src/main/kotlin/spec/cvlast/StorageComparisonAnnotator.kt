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

package spec.cvlast

import spec.cvlast.StorageComparisonChecker.isStorageOperand
import spec.cvlast.transformer.CVLAstTransformer
import spec.cvlast.transformer.CVLCmdTransformer
import spec.cvlast.transformer.CVLExpTransformer
import spec.cvlast.typechecker.CVLError
import utils.*
import utils.CollectingResult.Companion.map

class StorageComparisonAnnotator(ast: CVLAst) : CVLAstTransformer<CVLError>(
    cmdTransformer = object : CVLCmdTransformer<CVLError>(
        expTransformer = object : CVLExpTransformer<CVLError> {
            override fun expr(exp: CVLExp): CollectingResult<CVLExp, CVLError> {
                return super.expr(exp).map { expMapped ->
                    if (expMapped is CVLExp.RelopExp && expMapped.r.isStorageOperand()) {
                        val basis = when(val t = expMapped.r.getCVLType()) {
                            is CVLType.PureCVLType.VMInternal.BlockchainState -> {
                                ComparisonBasis.All(ghostUniverse)
                            }
                            is CVLType.PureCVLType.VMInternal.StorageReference -> {
                                t.basis
                            }
                            else -> `impossible!`
                        }
                        expMapped.updateTag(
                            expMapped.tag.copy(
                                annotation = ComparisonType(
                                    basis = basis,
                                    trySkolem = false
                                )
                            )
                        )
                    } else {
                        expMapped
                    }
                }
            }

            val ghostUniverse by lazy {
                ast.ghosts.filter { !it.persistent }.map {
                    StorageBasis.Ghost(it)
                }
            }
        }
    ) {
        override fun assertCmd(cmd: CVLCmd.Simple.Assert): CollectingResult<CVLCmd, CVLError> {
            return super.assertCmd(cmd).map {
                // when would it not?
                if(it !is CVLCmd.Simple.Assert) {
                    return@map it
                }
                val annot = it.exp.tag.annotation as? ComparisonType ?: return@map it
                it.copy(
                    exp = it.exp.updateTag(
                        it.exp.tag.copy(
                            annotation = annot.copy(trySkolem = true)
                        )
                    )
                )
            }
        }
    }
)
