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

import spec.cvlast.transformer.CVLAstTransformer
import spec.cvlast.transformer.CVLCmdTransformer
import spec.cvlast.transformer.CVLExpTransformer
import spec.cvlast.typechecker.CVLError
import spec.cvlast.typechecker.ImmutableAccessMismatch
import spec.cvlast.typechecker.StorageAccessMismatch
import spec.cvlast.typedescriptors.FromVMContext
import utils.CollectingResult
import utils.CollectingResult.Companion.asError
import utils.CollectingResult.Companion.bind
import utils.CollectingResult.Companion.lift
import utils.CollectingResult.Companion.ok

/**
 * Checks the invariants described in the documentation for [StorageAccessMarker]
 */
object StorageAccessChecker : CVLAstTransformer<CVLError>(
    CVLCmdTransformer(
        expTransformer = object : CVLExpTransformer<CVLError> {
            override fun expr(exp: CVLExp): CollectingResult<CVLExp, CVLError> {
                val eType = exp.getCVLType()
                val properAnnotationCheck = if (eType is CVLType.VM && eType.context == FromVMContext.StateValue) {
                    if (exp.tag.annotation is StorageAccessMarker || exp.tag.annotation is ImmutableAccessMarker) {
                        ok
                    } else {
                        StorageAccessMismatch(
                            location = exp.getRangeOrEmpty(),
                            message = "Internal type checking error: expected access expression $exp to be tagged with an access marker, but none was found"
                        ).asError()
                    }
                } else {
                    ok
                }
                val expectedAccessFormCheck = when (exp.tag.annotation) {
                    is ImmutableAccessMarker -> {
                        when (exp) {
                            is CVLExp.FieldSelectExp -> ok
                            else -> ImmutableAccessMismatch(
                                location = exp.getRangeOrEmpty(),
                                message = "Internal type checking error: direct immutable access expression $exp does not have expected format"
                            ).asError()
                        }
                    }
                    is StorageAccessMarker -> {
                        when (exp) {
                            is CVLExp.ArrayDerefExp,
                            is CVLExp.FieldSelectExp -> ok

                            else -> StorageAccessMismatch(
                                location = exp.getRangeOrEmpty(),
                                message = "Internal type checking error: direct storage access expression $exp does not have expected format"
                            ).asError()
                        }
                    }
                    else -> ok // checked above
                }
                return super.expr(exp).bind(properAnnotationCheck, expectedAccessFormCheck) { e, _, _ ->
                    e.lift()
                }
            }
        }
    )
) {
    override fun preserved(preserved: CVLPreserved): CollectingResult<CVLPreserved, CVLError> {
        /**
         * Skip preserved blocks. These are never actually typechecked (and will tank in the `getCVLType` above) and appear completely vestigial.
         */
        return preserved.lift()
    }
}
