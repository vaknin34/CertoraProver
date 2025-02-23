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

package builders

import analysis.abi.*
import utils.foldFirst
import java.math.BigInteger

open class SolidityTestBuilder(private val contractName: String) {
    private var ctr = 0

    /* name |-> sig, return, body */
    private val externalMethods =
        mutableMapOf<String, Triple<List<NamedType<LocatedType>>, NamedType<LocatedType>, List<String>>>()

    private val internalMethods =
        mutableMapOf<String, Triple<List<NamedType<LocatedType>>, NamedType<LocatedType>, List<String>>>()

    private val structToName = mutableMapOf<Type.Struct, String>()
    private val declarations = mutableMapOf<Type.Struct, String>()

    /* type -> name, body */
    protected val deepCopies = mutableMapOf<Type, Pair<String, String>>()
    private val decls: List<String>
        get() = declarations.values.toList()
    protected val retName = "ret"
    private fun nextStructName(): String {
        return "T${ctr++}"
    }

    fun getContract(): String {
        val structDecls = decls.joinToString(separator = "\n  ")

        val allMethods = (externalMethods.mapValues {
            it.value to true
        } + internalMethods.mapValues {
            it.value to false
        }).entries.joinToString(separator = "\n") { (fname, m) ->
            val (spec, isExternal) = m
            val (input, retType, body) = spec
            val qualifier = if(isExternal) { "external" } else { "internal" }
            val paramList = input
                .withIndex()
                .joinToString(separator = ", ") { (idx, ty) ->
                    decl(inputVar(idx), ty.ty)
                }
            val sig = "function ${fname}($paramList) $qualifier returns (${decl(retName, retType.ty)})"
            val bodyStr = body.joinToString(separator = "\n") { "${it};" }
            "${sig}\n{\n${bodyStr}\n}"
        }

        val allCopies = deepCopies.values.joinToString(separator = "\n") {
            it.second
        }

        return """
           contract $contractName {
             $structDecls
             $allCopies
             $allMethods
           }
       """.trimIndent()
    }

    protected fun typeName(t: Typed): String =
        when (val ty = t.type) {
            is Type.Primitive -> ty.name
            is Type.Array -> "${typeName(ty.elements)}[]"
            is Type.Struct -> structName(ty)
            is Type.StaticArray -> "${typeName(ty.elements)}[${ty.len}]"
        }

    protected fun structName(t: Type.Struct, qualified: Boolean = false): String {
        return structToName.getOrPut(t) {
            nextStructName()
        }.let {
            if (qualified) {
                "${contractName}.${it}"
            } else {
                it
            }
        }
    }

    protected fun fieldName(f: BigInteger): String = "field_${f}"
    private fun structDecl(t: Type.Struct): String {
        val fields = t
            .members
            .entries
            .sortedBy { it.key }
            .map { "${typeName(it.value)} ${fieldName(it.key)}; " }
            .foldFirst { s1, s2 -> s1 + s2 }

        return "struct ${typeName(t)} { $fields }"
    }

    protected fun <T : Typed> addType(t: T): NamedType<T> {
        val ty = t.type
        if (ty is Type.Struct) {
            declarations.putIfAbsent(ty, structDecl(ty))
            ty.members.forEach { (_, fld) -> addType(fld) }
        } else if(ty is Type.StaticArray) {
            addType(ty.elements)
        } else if(ty is Type.Array) {
            addType(ty.elements)
        }
        return NamedType(t, typeName(t))
    }

    protected fun decl(name: String, type: LocatedType): String {
        return if (type.type is Type.Primitive) {
            "${type.type.name} $name"
        } else {
            "${typeName(type)} ${if(type.inMemory) "memory" else "calldata"} $name"
        }
    }

    protected fun inputVar(i: Int) = "arg_${i}"
    protected fun addMethodTriple(
        input: List<NamedType<LocatedType>>,
        output: NamedType<LocatedType>,
        body: List<String>
    ): String {
        val fname = "f_${externalMethods.size}"
        externalMethods.put(fname, Triple(input, output, body))
        return fname
    }

    protected fun addInternalMethodTriple(
        input: List<NamedType<LocatedType>>,
        output: NamedType<LocatedType>,
        body: List<String>
    ) : String {
        val fname = "fi_${internalMethods.size}"
        internalMethods.put(fname, Triple(input, output, body))
        return fname
    }

    fun indexedPrimitiveTraversals(t: Type): List<Traversal<Int>> {
        val paths = mutableListOf<Traversal<Int>>()
        var ctr = 0
        for (path in primitiveTraversals(Traversal.Root(t))) {
            paths.add(
                path.mapIndices {
                    ctr++
                }
            )
        }
        return paths
    }

    fun qualifiedTypeName(t: Typed): String =
        when (val ty = t.type) {
            is Type.Primitive -> ty.name
            is Type.Array -> "${qualifiedTypeName(ty.elements)}[]"
            is Type.Struct -> structName(ty, qualified=true)
            is Type.StaticArray -> "${qualifiedTypeName(ty.elements)}[${ty.len}]"
        }
}
