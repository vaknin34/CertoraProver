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
import com.google.devtools.ksp.processing.Dependencies
import com.google.devtools.ksp.processing.Resolver
import com.google.devtools.ksp.processing.SymbolProcessor
import com.google.devtools.ksp.processing.SymbolProcessorEnvironment
import com.google.devtools.ksp.symbol.*

/**
 * generates AbstractTACParseCmdHandler.kt
 * will parse all the TACCmd.Simple subclasses and create parser for all concrete types based on the arguments.
 * For creating a customParser for specific TACCmd, add the annotation vc.data.parser.CustomTacParser to the declaration
 * i.e.
 * @CustomTacParser
 * data class CmdThatNeedsCustomParser(arg1: UnknownToParserType) : Simple()
 * [TACParserGeneratorProcessor]
 */
class TACParserGeneratorProcessor(private val environment: SymbolProcessorEnvironment) : SymbolProcessor {

    private val generatedClassName = """AbstractTACParserCmd"""

    private val cmdNameParamName = "name"
    private val cmdArgumentsParamName = "args"

    private val cmdArgumentsTypeName = "CmdArguments"

    private val parsedCmdArgumentsType = "List<$cmdArgumentsTypeName>"

    private val metaParamName = "meta"

    private val throwCastExceptionName = """throwCastingException"""

    private val utilsClass = "TACCmdParserUtils"
    private val directCommandTypes = mapOf(
        "tac.NBId" to Triple("CmdArguments.BlockID", "blockIds", "$utilsClass.getValueBlock"),
        "kotlin.String" to Triple("CmdArguments.TACString", "str", "$utilsClass.getValueString"),
        "vc.data.TACExpr" to Triple("CmdArguments.TACExprArg", "exp", "$utilsClass.getValueExpr")
    )




    private val argumentGetterName = "$utilsClass.getNthArg"

    private val symbolExtractorName = "$utilsClass.getValueSymbol"
    private val variableExtractorName = "$utilsClass.getValueVar"

    private val resolveMetaMapName = "$utilsClass.resolveMetaReference"

    private val convenienceTypes = mapOf(
        "vc.data.TACSymbol" to symbolExtractorName,
        "vc.data.TACSymbol.Var" to variableExtractorName
    )


    private fun isAutoParseType(tyName: KSName) = tyName.asString().let { fqn ->
        fqn in convenienceTypes || fqn in directCommandTypes || fqn == metaMapType
    }

    override fun process(resolver: Resolver): List<KSAnnotated> {
        val tacSimpleRoot = resolver.getClassDeclarationByName(resolver.getKSNameFromString(tacCmdSimple))
            ?: return listOf()
        if (tacSimpleRoot.containingFile == null) {
            return listOf()
        }
        if (tacSimpleRoot.containingFile !in resolver.getNewFiles()) {
            return listOf()
        }

        val generations = mutableListOf<Pair<String, String>>()
        val customGenerators = mutableListOf<String>()
        object : KSVisitorVoid() {
            override fun visitDeclaration(declaration: KSDeclaration, data: Unit) {
                super.visitDeclaration(declaration, data)
                if(declaration is KSDeclarationContainer) {
                    declaration.declarations.forEach {
                        this.visitDeclaration(it, data)
                    }
                }
                if (declaration !is KSClassDeclaration || !declaration.isConcreteSubClassOf(tacCmdSimple)) {
                    return
                }
                when(declaration.classKind) {
                    ClassKind.OBJECT -> generations.add(declaration.simpleName.asString() to declaration.qualifiedName!!.asString())
                    ClassKind.CLASS -> {
                        environment.logger.info("visiting ${declaration.simpleName.asString()}")
                        if (declaration.annotations.any { //check that it doesn't have CustomParser annotation?
                                environment.logger.info("declaration: ${declaration.simpleName.asString()}: annotation: ${it.annotationType.resolve().declaration.qualifiedName?.asString()}")
                                it.annotationType.resolve().declaration.qualifiedName?.asString() == "vc.data.parser.CustomTacParser"
                            }) {
                            return
                        }
                        //check if the class declaration contains either (modifier
                        else if (Modifier.DATA !in declaration.modifiers //not a data class?
                            || !declaration.primaryConstructor!!.parameters.all { //has parameters that cannot be generated automatically. (e.g. CmdArguments or metaArg - those params can be generated automatically)
                            isAutoParseType(it.type.resolve().declaration.qualifiedName ?: return@all false)
                        }) {
                            val generatedCall = generateCustomParserStub(declaration, customGenerators)
                            generations.add(declaration.simpleName.asString() to generatedCall)
                        } else {
                            val numPrimaryArgs = declaration.primaryConstructor!!.parameters.count {
                                it.type.resolve().declaration.qualifiedName!!.asString() != metaMapType
                            }

                            fun generateNthAccessor(ind: Int) =
                                "$argumentGetterName(\"${declaration.simpleName.asString()}\", $cmdArgumentsParamName, $ind, $numPrimaryArgs)"

                            val constructorArgs =
                                declaration.primaryConstructor!!.parameters.mapIndexed { ind, parameter ->
                                    when (val tyFqn = parameter.type.resolve().declaration.qualifiedName!!.asString()) {
                                        in directCommandTypes -> "${directCommandTypes[tyFqn]!!.third}(${
                                            generateNthAccessor(
                                                ind
                                            )
                                        })"
                                        in convenienceTypes -> "${convenienceTypes[tyFqn]!!}(${generateNthAccessor(ind)})"
                                        metaMapType -> metaParamName
                                        else -> {
                                            environment.logger.error(
                                                "Do not know how to automatically parse $tyFqn",
                                                parameter
                                            )
                                            "[ERROR]"
                                        }
                                    }
                                }.joinToString(",\n\t")
                            val fullCall = """${declaration.qualifiedName!!.asString()}($constructorArgs)"""
                            generations.add(declaration.simpleName.asString() to fullCall)
                        } //else
                    }
                    else -> {
                        environment.logger.error("Do not know how to automatically parse class type ${declaration.simpleName.asString()}", declaration)
                        return
                    }
                }
            }
        }.visitDeclaration(tacSimpleRoot, Unit)


        val generatedFile = """
package vc.data.parser
import tac.MetaMap
import vc.data.TACSymbolTable
import vc.data.TACCmd
/**
* Generated by: [${this::class.qualifiedName}]
*/
abstract class $generatedClassName(val symbolTable: TACSymbolTable, val mapOfMetaMap: Map<Int,MetaMap>) {

    fun parseCmd($cmdNameParamName: String, $cmdArgumentsParamName: $parsedCmdArgumentsType, metaRef: Int?) : vc.data.TACCmd.Simple {
        val $metaParamName = $resolveMetaMapName(metaRef, mapOfMetaMap)
        return when($cmdNameParamName) {
           ${generations.joinToString("\n\t\t\t") {(name, generationCode) ->
                "\"$name\" -> $generationCode"
            }
           }
           else -> throw IllegalArgumentException("Unknown command name " + $cmdNameParamName)
        }
    }
    ${customGenerators.joinToString("\n\t")}
}
""".trimIndent()
        val out = environment.codeGenerator.createNewFile(
            Dependencies(false, tacSimpleRoot.containingFile!!), "vc.data.parser",
            generatedClassName, "kt")
        out.bufferedWriter().use { os ->
            os.write(generatedFile)
        }

        return listOf()
    }

    private fun generateCustomParserStub(declaration: KSClassDeclaration, customGenerators: MutableList<String>): String {
        val className = declaration.simpleName.asString()
        customGenerators.add(
"""
abstract fun parse$className($cmdArgumentsParamName: $parsedCmdArgumentsType, $metaParamName: $metaMapType): ${declaration.qualifiedName!!.asString()}
""".trimIndent())
        return "parse$className($cmdArgumentsParamName, $metaParamName)"
    }
}
