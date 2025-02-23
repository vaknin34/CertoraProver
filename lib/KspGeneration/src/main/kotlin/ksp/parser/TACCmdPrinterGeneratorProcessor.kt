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

import com.google.devtools.ksp.processing.Dependencies
import com.google.devtools.ksp.processing.Resolver
import com.google.devtools.ksp.processing.SymbolProcessor
import com.google.devtools.ksp.processing.SymbolProcessorEnvironment
import com.google.devtools.ksp.symbol.*

class TACCmdPrinterGeneratorProcessor(private val environment: SymbolProcessorEnvironment) : SymbolProcessor {

    val generatedClassName = "printCmd"

    val customCmdPrinters = mapOf(
        "AnnotationCmd" to "printer($argList)",
        "SummaryCmd" to "printer($argList)"
    )

    private val directArgTypesPrint = mapOf(
        "vc.data.TACExpr" to  "printExpr($argList)",
        "vc.data.TACSymbol" to "printer($argList)",
        "vc.data.TACSymbol.Var" to "printer($argList)",
        "vc.data.TACSymbol.Const" to "printer($argList)",
        "kotlin.String" to "Quoted()",
        "tac.NBId" to "toString()",
    )





    private fun processConstructorParameter(parameter: KSValueParameter): String {
        val tyFqn = parameter.type.resolve().declaration.qualifiedName!!.asString()
        return if (parameter.isEnumType()) {
            "\${${parameter.name?.asString()}.toString().Quoted()}"
        } else if (parameter.isListOf(tacSymbol)) {
            "\${$parameter.joinToString(\" \") {it.printer($argList)}}"
        } else {
            when (tyFqn) {
                in directArgTypesPrint -> "\${${parameter.name!!.asString()}.${directArgTypesPrint[tyFqn]!!}}"
                else -> {
                    environment.logger.error(
                        "Do not know how to automatically print $tyFqn",
                        parameter
                    )
                    "[ERROR]"
                }
            }
        }
    }

    override fun process(resolver: Resolver): List<KSAnnotated> {
        val cmdPrinterGenerations = mutableMapOf<String, String>()
        val tacSimpleRoot = resolver.getClassDeclarationByName(resolver.getKSNameFromString(tacCmdSimple))
            ?: return listOf()
        if (tacSimpleRoot.containingFile == null) {
            return listOf()
        }
        if (tacSimpleRoot.containingFile !in resolver.getNewFiles()) {
            return listOf()
        }
        /**
         * Cmd printer visitor
         */
        object : KSVisitorVoid(){

            override fun visitDeclaration(declaration: KSDeclaration, data: Unit) {
                super.visitDeclaration(declaration, data)
                if(declaration is KSDeclarationContainer) {
                    declaration.declarations.forEach {
                        this.visitDeclaration(it, data)
                    }
                }
                if( declaration !is KSClassDeclaration || !declaration.isConcreteSubClassOf(tacCmdSimple)) {
                    return
                }
                environment.logger.info("visiting declaration of ${declaration.qualifiedName?.asString()}")
                when(declaration.classKind) {
                    ClassKind.OBJECT -> cmdPrinterGenerations.put(declaration.qualifiedName!!.asString(), "\"${declaration.simpleName.asString()}\"")
                    ClassKind.CLASS -> {
                    //the TACCmd.Simple.printCmd should be exhaustive
                    //check if the class declaration contains either (modifier
                        if (declaration.simpleName.asString() in customCmdPrinters) {
                            cmdPrinterGenerations.put(declaration.qualifiedName!!.asString(), customCmdPrinters[declaration.simpleName.asString()]!!)
                        } else {
                            if (checkAmbiguity(declaration)) {
                                environment.logger.error(
                                    "ambiguous parameter types ${declaration.simpleName.asString()}", declaration
                                )
                            }
                            val constructorArgs =
                                //iterate all the parameters (except metamap) of the primary constructor and find a printer for them
                                declaration.primaryConstructor!!.parameters
                                    .filter{ it.type.resolve().declaration.qualifiedName!!.asString()!=metaMapType}
                                    .map { parameter ->
                                        environment.logger.info(
                                            " processing parameter: ${parameter.name?.asString().orEmpty()}")
                                        processConstructorParameter(parameter)
                                    }.joinToString(" ")
                                        val metaParamString = "\$metaRef"
                                        val fullCall = """"${declaration.simpleName.asString()}$metaParamString $constructorArgs""""
                                        cmdPrinterGenerations.put(declaration.qualifiedName!!.asString(), fullCall)
                            }
                    }
                    else -> {
                        environment.logger.error("Do not know how to automatically parse class type ${declaration.simpleName.asString()}", declaration)
                        cmdPrinterGenerations.put(declaration.qualifiedName!!.asString(), "Todo()")
                    }
                }
            }
        }.visitDeclaration(tacSimpleRoot, Unit)
        val generatedFile = """
package vc.data.parser
import tac.MetaMap
import vc.data.TACCmd
/**
*   Generated by [${this::class.qualifiedName}]
*/
fun TACCmd.Simple.printCmd($argList: MutableMap<MetaMap,Int>) : String {
    val metaRef = printMetaString($argList, meta)
    return when(this) {
        ${cmdPrinterGenerations.entries.joinToString("\n\t\t") {(name, generationCode) ->
            "is $name -> $generationCode" }}
   }
}
""".trimIndent()
        val out = environment.codeGenerator.createNewFile(
            Dependencies(false, tacSimpleRoot.containingFile!!), "vc.data.parser", generatedClassName, "kt")
        out.bufferedWriter().use { os ->
            os.write(generatedFile)
        }
        return listOf()
    }

    private fun checkAmbiguity(decl: KSClassDeclaration) : Boolean{
        return IsConsecutiveListsInConstructor(decl)
    }
}
