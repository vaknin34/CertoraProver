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

import com.google.devtools.ksp.getVisibility
import com.google.devtools.ksp.isAbstract
import com.google.devtools.ksp.processing.Dependencies
import com.google.devtools.ksp.processing.Resolver
import com.google.devtools.ksp.processing.SymbolProcessor
import com.google.devtools.ksp.processing.SymbolProcessorEnvironment
import com.google.devtools.ksp.symbol.*

class TACExprPrinterGeneratorProcessor(private val environment: SymbolProcessorEnvironment) : SymbolProcessor {

    val generatedClassName = "TACPrinter"
    val generatedFuncName = "printExpr"
    val allParamKinds = mutableSetOf<KSType>()

    //types derived from TacExpr that their subtypes won't have a branch in when(e:Expr) is
    val abstractExprTypesToPrinters = mapOf(
        "$tacExpr.Apply" to "printer($argList)",
        "$tacExpr.Vec.IntMul" to "printer($argList)",
        "$tacExpr.Vec.IntAdd" to "printer($argList)",
        "$tacExpr.Vec.Add" to "printer($argList)",
        "$tacExpr.MapDefinition" to "printer($argList)"
    )


    //types with custom printer function
    val exprTypesToPrinters = mapOf("$tacExpr" to generatedFuncName,
                                    "$tacExpr.Sym.Const" to "\"\${s.printer($argList)}\"",
                                    "$tacExpr.Sym.Var" to "\"\${s.printer($argList)}\"",
                                    "$tacExpr.StructConstant" to "\"\${this.printer($argList)}\"",
                                    "$tacExpr.StructAccess" to "\"\${this.printer($argList)}\"",
                                    "$tacExpr.QuantifiedFormula" to "\"\${this.printer($argList)}\"",
                                    "$tacExpr.Unconstrained" to "\"\${this.printer()}\"",
                                    "$tacExpr.SimpleHash" to "\"\${this.printer($argList)}\"",
                                    "$tacExpr.AnnotationExp" to "\"\${this.printer($argList)}\"",
        )

    private val genericExprNames = setOf("$tacExpr.AnnotationExp")

    val paramTypesPrinters = mapOf<String, String>()
    val generatedFunctionDecl = "$generatedFuncName($argList : MutableMap<MetaMap,Int>)"
    val generatedFunctionCall = """$generatedFuncName($argList)"""

    fun isSuperTypePrinterImplemented(decl : KSDeclaration) = abstractExprTypesToPrinters.any{ (decl as? KSClassDeclaration)?.inheritsFrom(it.key) ?: false}
    private fun generatePrinterFromConstructor(declaration: KSClassDeclaration): String =
        if (Modifier.DATA !in declaration.modifiers || declaration.primaryConstructor == null) {
            "TODO()"
        }
        else if (declaration.qualifiedName?.asString()?.let { it in exprTypesToPrinters} ?: false) {
            "${declaration.qualifiedName!!.asString().let {exprTypesToPrinters[it]}}"
        }
        else if (checkAmbiguity(declaration)) {
            environment.logger.error("Ambiguous constructor, can't auto create printer ")
            "TODO: Ambiguous constructor"
        }
        else {
            allParamKinds.addAll(declaration.primaryConstructor!!.parameters.map { it.type.resolve() })
            "\"${declaration.simpleName.asString()}(${declaration.primaryConstructor!!.parameters.joinToString(" ")
            {
                when {
                    it.isOfType(tacVar)  -> "\${${it}.printer($argList)}"
                    it.isListTACExprBounded() -> "\${$it.joinToString(\" \") {it.$generatedFunctionCall}}"
                    it.isOfType(tacExpr) -> "\${$it.$generatedFunctionCall}"
                    (it.name?.asString() == "tag") && it.hasOverrideModifier(declaration) -> ""
                    else -> {
                        environment.logger.error("$it not implemented as auto print, either add this type as auto printed, or add the ${declaration.simpleName.asString()} " +
                        "to exprTypesToPrinters dictionary")
                        "TODO: $it"
                    }
                }
            }})\""
        }

    override fun process(resolver: Resolver): List<KSAnnotated> {
        val tacExprKsName = resolver.getKSNameFromString(tacExpr)
        val tacExprRoot =  resolver.getClassDeclarationByName(tacExprKsName) ?: return listOf()
        if (tacExprRoot.containingFile == null) {
            return listOf()
        }
        if (tacExprRoot.containingFile !in resolver.getNewFiles()) {
            return listOf()
        }
        val exprPrinterGenerations = mutableListOf<Pair<String,String>>()
        object : KSVisitorVoid(){
            override fun visitDeclaration(declaration: KSDeclaration, data: Unit) {
                super.visitDeclaration(declaration, data)
                if(declaration is KSDeclarationContainer) {
                    declaration.declarations.forEach {
                        this.visitDeclaration(it, data)
                    }
                }

                if(declaration !is KSClassDeclaration
                    || ((declaration.isAbstract() || Modifier.SEALED in declaration.modifiers)
                        && (declaration.qualifiedName?.asString() !in abstractExprTypesToPrinters))
                    || isSuperTypePrinterImplemented(declaration)
                    || declaration.isCompanionObject
                    || !declaration.inheritsFrom(tacExpr)
                    || declaration.getVisibility() != Visibility.PUBLIC) {
                    return
                }
                environment.logger.info("processing $declaration}")
                when(declaration.classKind) {
                    ClassKind.CLASS -> {
                        val qName = declaration.qualifiedName!!.asString()
                        if (qName in abstractExprTypesToPrinters) {
                            exprPrinterGenerations.add(qName to abstractExprTypesToPrinters[qName]!!)
                        }
                        else if (qName in exprTypesToPrinters) {
                            exprPrinterGenerations.add(qName to exprTypesToPrinters[qName]!!)
                        } else {
                            exprPrinterGenerations.add(qName to generatePrinterFromConstructor(declaration))
                        }
                    }
                    else -> {
                        exprPrinterGenerations.add(declaration.simpleName.asString() to "TODO!!")
                        environment.logger.error("can't auto generate printer for ${declaration.simpleName}")
                    }
                }
            }
        }.visitDeclaration(tacExprRoot, Unit)
        val generatedFile = """
package vc.data.parser
import tac.MetaMap
import $tacExpr
/**
* Generated by [${this::class.qualifiedName}]
Possible parameter types:
${allParamKinds.joinToString("\n")}
*/
fun TACExpr.$generatedFunctionDecl : String {
    return when (this) {
        ${exprPrinterGenerations.joinToString("\n\t\tis ", "is ") { (name, code) ->
                val name2 = if (name in genericExprNames) {
                    "$name<*>"
                } else {
                    name
                }
                "$name2 -> $code"
            }
        }
    }
}
""".trimIndent()
            val out = environment.codeGenerator.createNewFile(
                Dependencies(false, tacExprRoot.containingFile!!), "vc.data.parser", "$generatedFuncName", "kt")
            out.bufferedWriter().use { os ->
                os.write(generatedFile)
            }
            return listOf()
    }


    fun checkAmbiguity(decl :KSClassDeclaration ) : Boolean {
        return IsConsecutiveListsInConstructor(decl)
    }
}
