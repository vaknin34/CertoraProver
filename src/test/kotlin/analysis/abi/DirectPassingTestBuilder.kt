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

package analysis.abi

import builders.*
import datastructures.stdcollections.*
import net.jqwik.api.*
import net.jqwik.kotlin.api.any
import net.jqwik.kotlin.api.combine
import net.jqwik.kotlin.api.ofSize
import org.junit.jupiter.api.Assertions
import utils.*
import java.math.BigInteger
import kotlin.collections.listOf
import kotlin.collections.mapOf
import kotlin.collections.toList

sealed class ArgBuilder {
    /* x = y */
    data class Var(val i: Int): ArgBuilder() {
        override fun <T : Typed> resultTypeInEnv(e: Env<T>): Type {
            return e.arguments[i].type
        }

        override fun transform(context: List<ArgBuilder>): ArgBuilder {
            return context[i]
        }
    }

    data class AccessField(val ref: ArgBuilder, val field: BigInteger): ArgBuilder() {
        override fun <T : Typed> resultTypeInEnv(e: Env<T>): Type {
            val structType = ref.resultTypeInEnv(e) as Type.Struct
            return structType.members[field]!!
        }

        override fun transform(context: List<ArgBuilder>): ArgBuilder {
            return AccessField(ref.transform(context), field)
        }
    }

    data class DeepCopy(val ref: ArgBuilder): ArgBuilder() {
        override fun <T : Typed> resultTypeInEnv(e: Env<T>): Type {
            return ref.resultTypeInEnv(e)
        }

        override fun transform(context: List<ArgBuilder>): ArgBuilder {
            return DeepCopy(ref.transform(context))
        }

    }

    abstract fun<T: Typed> resultTypeInEnv(e: Env<T>): Type

    abstract fun transform(context: List<ArgBuilder>): ArgBuilder
}

infix fun List<ArgBuilder>.andThen(fs: List<ArgBuilder>): List<ArgBuilder> {
    return fs.map { builder: ArgBuilder ->
        builder.transform(this)
    }
}
data class Env<T: Typed>(val arguments: List<T>) {
    fun<U: Typed> mapTypes(f: (T) -> U): Env<U> = Env(arguments = arguments.map(f))
}

sealed class CallTree {
    abstract val input: Env<LocatedType>

    data class Leaf(
        override val input: Env<LocatedType>,
        val output: ArgBuilder,
    ) : CallTree()

    data class Node(
        override val input: Env<LocatedType>,
        val children: List<Either<Call, InlinedCall>>,
    ) : CallTree()

    data class Call(
        val args: List<ArgBuilder>,
        val child: CallTree
    )

    data class InlinedCall(
        val out: ArgBuilder,
    )

    companion object {
        private fun inlineCall(call: CallTree, transform: List<ArgBuilder>): List<InlinedCall> {
            return when (call) {
                is Leaf ->
                    listOf(
                        InlinedCall(
                            out = call.output.transform(transform),
                        )
                    )

                is Node -> call.children.flatMap { callNode ->
                    callNode.toValue({
                        inlineCall(it.child, transform andThen it.args)
                    }, {
                        listOf(it)
                    })
                }
            }
        }

        fun inlineCallTree(callTree: CallTree): CallTree {
            return when (callTree) {
                is Leaf -> callTree
                is Node -> inlineCall(callTree, callTree.input.arguments.indices.map {
                    ArgBuilder.Var(it)
                }).let {
                    Node(callTree.input, it.map { it.toRight() })
                }
            }
        }
    }
}

data class EquivalenceTest(
    val testMethod: String,
    val contract: String,
    val spec: String
)

fun inlineEquivTestAndSpec(contractName: String, tree: CallTree): EquivalenceTest {
    fun Int.indexName(): String = "i${this}"
    val builder = DirectPassingTestBuilder(contractName, tree)
    val indices = mutableSetOf<String>()
    val primPaths = builder
        .indexedPrimitiveTraversals(builder.retType.type)
        .map {
            it.mapIndices { it.indexName().also { indices.add(it) } }
        }

    val testRet = "testRet"
    val specRet = "inlinedRet"

    val assumeAsserts = mutableListOf<String>()

    // Add conditions on array accesses:
    // For each array access that appears as part of a traversal,
    // require that the index is in bounds. Since there are two
    // results, we check bounds after applying the traversal
    // to one of the results, then assert the lengths are the same.
    primPaths.flatMapToSet {
        it.subTraversals { it as? Traversal.Indexed }
    }.forEach { access ->
        assumeAsserts.add(
            "require(${access.index} < ${access.next.toSolidity(testRet)}.length)"
        )
        assumeAsserts.add(
            "assert(${access.next.toSolidity(testRet)}.length == ${access.next.toSolidity(specRet)}.length)"
        )
    }

    // For each primitive traversal, assert equality
    for (p in primPaths) {
        assumeAsserts.add(
            "assert(${p.toSolidity(testRet)} == ${p.toSolidity(specRet)})"
        )
    }

    val indexArgs = indices.map {
        "uint $it"
    }

    val testArgs = tree.input.arguments.withIndex().map { (i, t) ->
        "${builder.qualifiedTypeName(t)} x${i}"
    }

    val funArgs = tree.input.arguments.indices.map {
        "x${it}"
    }

    val ruleArgs = listOf("env e") + indexArgs + testArgs
    val callArgs = listOf("e") + funArgs

    val typeName = builder.qualifiedTypeName(builder.retType)
    val spec = """
            rule eq_return(${ruleArgs.joinToString(separator = ", ")}) {
                $typeName $testRet = ${builder.testFn}(${callArgs.joinToString(separator = ", ")});
                $typeName $specRet = ${builder.specFn}(${callArgs.joinToString(separator = ", ")});
                ${assumeAsserts.joinToString(separator = "\n") { "${it};" }}
            }
        """.trimIndent()

    return EquivalenceTest(builder.testFn, builder.getContract(), spec)
}

@Provide
fun initialEnv(): Arbitrary<Env<LocatedType>> {
    return initialEnv(1, 3, ::arbitraryType)
}

fun initialEnv(min: Int, max: Int, typeGen: () -> Arbitrary<Type>): Arbitrary<Env<LocatedType>> {
    return typeGen().list().ofSize(min .. max).map {
        Env(it.map { ty ->
            LocatedType(ty, inMemory = true)
        })
    }
}

object ArbitraryArg {
    private fun argBuilders(env: Env<Type>, builder: ArgBuilder): Arbitrary<ArgBuilder> {
        val ty = builder.resultTypeInEnv(env)
        if (ty is Type.Primitive) {
            return Arbitraries.of(builder)
        }

        return Arbitraries.oneOf(
            // Exactly x
            Arbitraries.of(builder),

            // copy(x)
            Arbitraries.of(ArgBuilder.DeepCopy(builder)),

            // Some sub-path of x
            Arbitraries.lazy {
                @Suppress("KotlinConstantConditions")
                when (ty) {
                    is Type.Struct ->
                        Arbitraries.of(ty.members.keys).flatMap { field ->
                            argBuilders(env, ArgBuilder.AccessField(builder, field))
                        }

                    is Type.Array ->
                        // TODO potentially use an index from env
                        Arbitraries.of(builder, ArgBuilder.DeepCopy(builder))

                    // we don't generate static arrays
                    is Type.StaticArray,
                    is Type.Primitive ->
                        `impossible!`
                }
            }
        )
    }

    private fun argBuilders(env: Env<Type>): Arbitrary<ArgBuilder>  {
        return Int.any(env.arguments.indices).flatMap {
            argBuilders(env, ArgBuilder.Var(it))
        }
    }

    private fun callTreeLeaf(env: Env<LocatedType>): Arbitrary<CallTree> {
        return argBuilders(env.mapTypes { it.type }).map { resultBuilder ->
            CallTree.Leaf(env, resultBuilder)
        }
    }

    private fun callTreeNode(env: Env<LocatedType>, minDepth: Int, maxDepth: Int): Arbitrary<CallTree> {
        return call(env, minDepth-1, maxDepth-1).list().ofSize(1..2).map {
            CallTree.Node(
                input = env,
                children = it.map { it.toLeft() }
            ).also {
                checkCallSanity(it)
            }
        }
    }

    fun callTree(env: Env<LocatedType>, minDepth: Int, maxDepth: Int): Arbitrary<CallTree> {
        return if (0 < minDepth) {
            callTreeNode(env, minDepth, maxDepth)
        } else if (maxDepth == 0) {
            callTreeLeaf(env)
        } else {
            val e = Env(env.arguments.toList())
            Arbitraries.oneOf(
                Arbitraries.lazy { callTreeLeaf(e) },
                Arbitraries.lazy { callTreeNode(e, minDepth, maxDepth) }
            )
        }
    }

    fun call(env: Env<LocatedType>, minDepth: Int, maxDepth: Int): Arbitrary<CallTree.Call> {
        return argBuilders(env.mapTypes { it.type })
            .list()
            .ofSize(1..3)
            .flatMap { argBuilders: List<ArgBuilder> ->
                val calleeTypes = argBuilders.map { builder ->
                    builder.resultTypeInEnv(env)
                }
                Boolean.any().list().ofSize(argBuilders.size).map {
                    calleeTypes.zip(it).map {
                        LocatedType(it.first, it.second)
                    }
                }.flatMap {
                    callTree(Env(it), minDepth, maxDepth).map {
                        CallTree.Call(args = argBuilders, child = it)
                    }
                }
            }
    }
}

@Provide
fun arbitraryInteger(): Arbitrary<Type.Primitive.Integer> {
    val widths = listOf(32.toBigInteger())
    val signed = listOf(true, false)
    return combine(
        Arbitraries.of(widths),
        Arbitraries.of(signed),
    ) { w, s ->
        Type.Primitive.Integer(signed = s, bytes = w)
    }
}

@Provide
fun arbitraryPrimitive(): Arbitrary<Type.Primitive> {
    return Arbitraries.oneOf(
        arbitraryInteger(),
        Arbitraries.of(Type.Primitive.Address),
        Arbitraries.of(Type.Primitive.Bytes32),
    )
}

@Provide
fun arbitraryArray(): Arbitrary<Type> {
    // Only 1D for now
    return arbitraryPrimitive().map {
        Type.Array(it)
    }
}

@Provide
fun arbitraryStruct(): Arbitrary<Type> {
    val types = arbitraryType().list().ofSize(1..3)
    return types.map { ts ->
        ts.fold(Pair(BigInteger.ZERO, mapOf<BigInteger, Type>())) { (off, struct), t ->
            val nextOff = off + t.sizeInBytes
            Pair(nextOff, struct + (off to t))
        }.let {
                (_, struct) -> Type.Struct(struct)
        }
    }
}

@Provide
fun arbitraryType(): Arbitrary<Type> {
    return Arbitraries.lazyOf(
        { arbitraryPrimitive() },
        { arbitraryArray() },
        { arbitraryStruct() },
    )
}

class DirectPassingTestBuilder(contractName: String, callTree: CallTree) : SolidityTestBuilder(contractName) {
    val testFn: String
    val specFn: String
    val retType: LocatedType

    private fun deepCopyName(t: Type): String {
        fun go(t: Type): String =
            when(t) {
                is Type.Primitive -> typeName(t)
                is Type.Struct -> structName(t)
                is Type.Array -> "array_${go(t.elements)}"
                is Type.StaticArray -> "staticarray_${go(t.elements)}"
            }

        return "copy_${go(t)}"
    }

    private fun<T: Typed> T.toNamedType() =
        typeName(this).let { NamedType(this, it) }

    private fun callActual(s: Int, i: Int) = "x_${s}_${i}"

    private fun generateDeepCopy(t: Type): Pair<String, String> {
        val body = when (t) {
            is Type.Primitive.Integer -> "ret = (x / 2);"
            is Type.Primitive.Bytes32 -> "ret = bytes32(uint(x) / 2);"
            is Type.Primitive.Address -> "ret = address(uint160(x) / 2);"
            is Type.Struct ->  {
                t.members.map { (off, elt) ->
                    val f = getDeepCopy(elt)
                    "ret.${fieldName(off)} = $f(x.${fieldName(off)});"
                }.joinToString(separator="\n")
            }
            is Type.Array -> {
                val f = getDeepCopy(t.elements)
                """
                    ret = new ${typeName(t)}(x.length);
                    for (uint i = 0; i < x.length; ++i) {
                      ret[i] = $f(x[i]);
                    }
                """.trimIndent()
            }

            is Type.StaticArray -> {
                val f = getDeepCopy(t.elements)

                List(t.len.intValueExact()) {
                    "$f(x[$it])"
                }.joinToString(separator = ", ", prefix = "ret = [ ", postfix = " ]")
            }
        }

        val funName = deepCopyName(t)
        val xDecl = decl("x", LocatedType(t, true))
        val retDecl = decl("ret", LocatedType(t, true))

        return funName to """
            function $funName(${xDecl}) internal returns (${retDecl}) {
                $body
            }
        """.trimIndent()
    }

    private fun getDeepCopy(t: Type): String {
        return deepCopies.getOrPut(t) {
            generateDeepCopy(t)
        }.first
    }

    private fun argBuilderToRHS(env: Env<LocatedType>, builder: ArgBuilder): String {
        return when(builder) {
            is ArgBuilder.Var ->
                inputVar(builder.i)
            is ArgBuilder.AccessField ->
                "${argBuilderToRHS(env, builder.ref)}.${fieldName(builder.field)}"
            is ArgBuilder.DeepCopy -> {
                val deepCopyType = builder.resultTypeInEnv(env)
                val f = getDeepCopy(deepCopyType)
                "${f}(${argBuilderToRHS(env, builder.ref)})"
            }
        }
    }

    private fun generateAssignment(env: Env<LocatedType>, builder: ArgBuilder, dest: String): List<String> {
        unused(env)
        return when(builder) {
            is ArgBuilder.Var ->
                listOf("$dest = ${argBuilderToRHS(env, builder)}")
            is ArgBuilder.AccessField ->
                listOf("$dest = ${argBuilderToRHS(env, builder)}")
            is ArgBuilder.DeepCopy ->
                listOf("$dest = ${argBuilderToRHS(env, builder)}")
        }
    }

    private fun generateCall(env: Env<LocatedType>, callSeq: Int, call: CallTree.Call, methodName: String, ret: String): List<String> {
        val cmds = mutableListOf<String>()
        for ((i, builder) in call.args.withIndex()) {
            val ty = builder.resultTypeInEnv(env).let { LocatedType(it, true) }
            cmds.add(
                decl(callActual(callSeq, i), ty),
            )
            cmds.addAll(
                generateAssignment(env, builder, callActual(callSeq, i))
            )
        }
        val argString = (0..<call.args.size).joinToString(separator = ", ") { callActual(callSeq, it) }
            cmds.add(
                "$ret = this.${methodName}(${argString})"
            )
        return cmds
    }

    private fun walkCallTree(callTree: CallTree): Pair<String, LocatedType> {
        val inputTypes = callTree.input.arguments.map {
            addType(it)
        }
        when (callTree) {
            is CallTree.Leaf -> {
                val outputType = LocatedType(
                    callTree.output.resultTypeInEnv(callTree.input),
                    true
                )
                val body = generateAssignment(callTree.input, callTree.output, retName)
                val fName = addMethodTriple(inputTypes, outputType.toNamedType(), body)
                return fName to outputType
            }

            is CallTree.Node -> {
                val envWithLocals = callTree.input.arguments.toMutableList()
                val argSetup = callTree.children.take(callTree.children.size-1).withIndex().map { (i, it) ->
                    val thisOutput = inputVar(callTree.input.arguments.size + i)
                    val (ty, code) = it.toValue({ call ->
                        val (calledFn, retType) = walkCallTree(call.child)
                        retType to generateCall(Env(envWithLocals), i, call, calledFn, thisOutput)
                    },{ inlinedCall ->
                        val type = inlinedCall.out.resultTypeInEnv(Env(envWithLocals))
                        LocatedType(type, true) to generateAssignment(Env(envWithLocals), inlinedCall.out, thisOutput)
                    })
                    envWithLocals.add(ty)
                    listOf(decl(thisOutput, ty)) + code
                }
                return callTree.children.last().let { call ->
                    val (retType, cmds) = call.toValue({
                        val (calledFn, retType) = walkCallTree(it.child)
                        retType to generateCall(Env(envWithLocals), callTree.children.size-1, it, calledFn, retName)
                    }, { inlinedCall ->
                        val type = inlinedCall.out.resultTypeInEnv(Env(envWithLocals))
                        LocatedType(type, true) to generateAssignment(Env(envWithLocals), inlinedCall.out, retName)
                    })

                    val fName = addMethodTriple(inputTypes, retType.toNamedType(), argSetup.flatten() + cmds)
                    fName to retType
                }
            }
        }
    }

    init {
        val (f, t1) = walkCallTree(callTree)
        val (spec, t2) = walkCallTree(CallTree.inlineCallTree(callTree))
        check(t1 == t2)
        testFn = f
        specFn = spec
        retType = t1
    }
}

sealed class Traversal<out I> {
    abstract val type: Type
    data class Root(override val type: Type): Traversal<Nothing>() {
        override fun <J> mapIndices(f: (Nothing) -> J): Traversal<J> {
            return this
        }
    }

    data class Indexed<I>(val index: I, val next: Traversal<I>): Traversal<I>() {
        override val type: Type
            get() = (next.type as? Type.Array)?.elements ?: (next.type as? Type.StaticArray)?.elements ?: throw IllegalStateException("Next access is $next???")

        override fun<J> mapIndices(f: (I) -> J): Indexed<J> {
            return Indexed(index = f(index), next = next.mapIndices(f))
        }

    }
    data class Field<I>(val next: Traversal<I>, val field: BigInteger): Traversal<I>() {

        override fun <J> mapIndices(f: (I) -> J): Traversal<J> {
            return Field(next = next.mapIndices(f), field = field)
        }

        override val type: Type = (next.type as? Type.Struct)?.members?.get(field) ?: throw IllegalStateException("Have struct, but accessing $next")
    }

    abstract fun<J> mapIndices(f: (I) -> J): Traversal<J>
}

fun primitiveTraversals(p: Traversal<Unit>): List<Traversal<Unit>> {
    return when(val ty = p.type) {
        is Type.Primitive ->
            listOf(p)

        is Type.StaticArray,
        is Type.Array ->
            listOf(Traversal.Indexed(Unit, p))

        is Type.Struct ->
            ty.members.flatMap { (off, _) ->
                primitiveTraversals(Traversal.Field(p, off))
            }


    }
}


fun<I,T: Traversal<I>> Traversal<I>.subTraversals(f: (Traversal<I>) -> T?): List<T> {
    return listOfNotNull(f(this)) + when(this) {
        is Traversal.Indexed -> this.next.subTraversals(f)
        is Traversal.Field -> this.next.subTraversals(f)
        is Traversal.Root -> listOf()
    }
}

fun Traversal<String>.toSolidity(rootVar: String): String {
    fun go(t: Traversal<String>): String {
        return when (t) {
            is Traversal.Field ->
                "${go(t.next)}.field_${t.field}"
            is Traversal.Indexed ->
                "${go(t.next)}[${t.index}]"
            is Traversal.Root ->
                rootVar
        }
    }

    return go(this)
}

fun checkCallSanity(tree: CallTree): LocatedType {
    when (tree) {
        is CallTree.Leaf -> {
            return LocatedType(tree.output.resultTypeInEnv(tree.input), true)
        }
        is CallTree.Node -> {
            val env = tree.input.arguments.toMutableList()
            for (c in tree.children) {
                when (c) {
                    is Either.Left -> {
                        val callEnv = c.d.args.map { it.resultTypeInEnv(Env(env)) }
                        Assertions.assertEquals(c.d.child.input.arguments.map { it.type }, callEnv)
                        val resultType = checkCallSanity(c.d.child)
                        env.add(resultType)
                    }

                    is Either.Right -> {
                        env.add(LocatedType(c.d.out.resultTypeInEnv(Env(env)), true))
                    }
                }
            }
            return env.last()
        }
    }
}
