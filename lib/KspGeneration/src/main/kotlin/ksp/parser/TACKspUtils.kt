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

package ksp.parser

import com.google.devtools.ksp.getAllSuperTypes
import com.google.devtools.ksp.isAbstract
import com.google.devtools.ksp.symbol.*

const val tacCmdSimple = "vc.data.TACCmd.Simple"
const val tacSymbol = "vc.data.TACSymbol"
const val tacVar = "vc.data.TACSymbol.Var"
const val tacExpr = "vc.data.TACExpr"
const val metaMapType = "tac.MetaMap"
const val argList = "mapOfMetaMap"
const val hashFamily = "vc.data.HashFamily"
fun KSValueParameter.isOfType(qualifiedName: String) =
    this.type.resolve().declaration.qualifiedName?.asString() == qualifiedName

fun KSValueParameter.isEnumType(): Boolean =
    (type.resolve().declaration as? KSClassDeclaration)?.classKind == ClassKind.ENUM_CLASS

fun KSClassDeclaration.isConcreteSubClassOf(superTypeName: String) =
        !this.isAbstract()
        && !this.isCompanionObject
        && Modifier.SEALED !in this.modifiers
        && this.inheritsFrom(superTypeName)

fun KSValueParameter.hasOverrideModifier(klass: KSClassDeclaration) = klass.declarations.find { decl ->
    decl is KSPropertyDeclaration && decl.simpleName == this.name }?.modifiers?.contains(Modifier.OVERRIDE) ?: false
fun KSTypeArgument.isTACExpr() = this.type?.resolve()?.declaration?.qualifiedName?.asString() == tacExpr

fun KSTypeArgument.isTACExprOrInheritsFrom() = this.isTACExpr() ||
    (this.type?.resolve()?.declaration as? KSClassDeclaration)?.inheritsFrom(tacExpr) == true

fun KSValueParameter.isList() = this.type.resolve().declaration.simpleName.asString() == "List"

fun KSValueParameter.isListOf(typeArgument: String) = isList() && this.type.resolve().arguments.singleOrNull()?.let {
    (it.type?.resolve()?.declaration as? KSClassDeclaration)?.qualifiedName?.asString() == typeArgument } ?: false

fun KSValueParameter.isListTACExprBounded() = this.type.resolve().declaration.simpleName.asString() == "List"
    && this.type.resolve().arguments.singleOrNull()?.isTACExprOrInheritsFrom() ?: false

fun KSClassDeclaration.inheritsFrom(superTypeName: String) = this.getAllSuperTypes().any {
    (it.declaration as? KSClassDeclaration)?.qualifiedName?.asString() == superTypeName
}

fun IsConsecutiveListsInConstructor(decl: KSClassDeclaration) : Boolean{
    val params = decl.primaryConstructor?.parameters
    val range = 0 until (params?.let { it.size - 1 } ?: 0)
    for (i in range) {
        if (params!![i].isList() && params[i + 1].isList()) {
            return true
        }
    }
    return false
}
