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

import spec.cvlast.typedescriptors.FromVMContext
import spec.cvlast.typedescriptors.VMTypeDescriptor
import utils.CollectingResult
import utils.CollectingResult.Companion.bind
import utils.CollectingResult.Companion.lift

/**
 * Common class to hold the semantics for resolving the (concrete) syntax of x.f. If `x` is a contract name and `f` is the
 * name of an enum, treat this as looking up an enum definition,
 * if `x.f` has type `Enum` and `x = C.g` where `C` is a code contract, then treat it as an enum constant, otherwise
 * treat it as a struct lookup. Also handles the case where the base object of the struct field is a VM type.
 */
object FieldSelectSemantics {
    fun <E, R> fieldSemantics(
        exp: CVLExp.FieldSelectExp,
        vmTypeHandler: (CVLType.VM) -> CollectingResult<CVLType.PureCVLType, E>,
        fieldHandler: (structType: CVLType.PureCVLType.Struct, fieldName: String) -> CollectingResult<R, E>,
        codeContractNameHandler: (contract: CVLType.PureCVLType.Primitive.CodeContract, member: String) -> CollectingResult<R, E>,
        arrayLenHandler: (arrayType: CVLType.PureCVLType) -> CollectingResult<R, E>,
        badType: (CVLType.PureCVLType) -> CollectingResult<Nothing, E>,
        storageAccess: (accessedType: VMTypeDescriptor, field: String) -> CollectingResult<R, E>
    ) : CollectingResult<R, E> {
        val type = exp.structExp.getCVLType()
        if(type is CVLType.VM && type.context is FromVMContext.StateValue) {
            return storageAccess(
                type.descriptor, exp.fieldName
            )
        }
        return (when(type) {
            is CVLType.VM -> vmTypeHandler(type)
            is CVLType.PureCVLType -> type.lift()
        }).bind { ty: CVLType.PureCVLType ->
            when (ty) {
                is CVLType.PureCVLType.Struct ->
                    fieldHandler(ty, exp.fieldName)
                is CVLType.PureCVLType.Primitive.CodeContract -> {
                    codeContractNameHandler(ty, exp.fieldName)
                }
                is CVLType.PureCVLType.CVLArrayType -> {
                    arrayLenHandler(ty)
                }

                else -> badType(ty)
            }
        }
    }
}
