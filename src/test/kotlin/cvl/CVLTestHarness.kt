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

package cvl

import bridge.types.PrimitiveType
import org.junit.jupiter.api.Assertions.*
import spec.*
import spec.cvlast.*
import spec.cvlast.typechecker.CVLAstTypeChecker
import spec.cvlast.typechecker.CVLError
import spec.cvlast.typedescriptors.EVMTypeDescriptor
import utils.CollectingResult
import utils.CollectingResult.Companion.bind
import utils.CollectingResult.Companion.map
import utils.VoidResult

// TODO CERT-3653: consolidate with `ErrorTests`

open class CVLTestHarness {

    private fun <T, E> CollectingResult<T, E>.succeeded(): Boolean = this is CollectingResult.Result
    companion object {
        const val dummyContractName = "ExampleDummyContract"
        const val dummyFilename = "nofile"

        // TODO: How to represent `bytes`?
        val specialCommonTypes = setOf("env", "method", "calldataarg", "storage", /*"bytes",*/ "mathint")
        // include only uint8,uint128,uint256 and same for int, bytes
        val representativePrimitiveTypes = PrimitiveType.values().filter {
            it.toDescriptor().let { dscrp ->
                if (dscrp is EVMTypeDescriptor.UIntK && (dscrp.bitwidth % 128 != 0 && dscrp.bitwidth != 8)) {
                    false
                } else if (dscrp is EVMTypeDescriptor.IntK && (dscrp.bitwidth % 128 != 0 && dscrp.bitwidth != 8)) {
                    false
                } else if (dscrp is EVMTypeDescriptor.BytesK && (dscrp.bitwidth % 128 != 0 && dscrp.bitwidth != 8)) {
                    false
                } else {
                    true
                }
            }
        }
        val representativeCommonTypes =
            specialCommonTypes.plus(representativePrimitiveTypes.map { it.name }).map { CVLType.valueFromString(it) }
    }

    private fun compileSpec(specTxt: String): CollectingResult<CVLAst, CVLError> {
        val resolver = DummyTypeResolver(SolidityContract(dummyContractName))
        val spec = CVLSource.Raw(dummyFilename, specTxt, false)
        return CVLInput.parseCVLSpec(spec, resolver)
    }

    fun typeCheckSpec(specTxt: String): VoidResult<CVLError> {
        val symbolTable = CVLSymbolTable()
        return compileSpec(specTxt).bind { ast ->
            val symbolTableFiller1 = SymbolTableFiller(symbolTable, ast, emptyMap(), dummyContractName, emptyList())
            symbolTableFiller1.traverseAst().bind(
                // Sanity checks when finalizing the symbol table expect to have a currentContract scope, so add a dummy one.
                symbolTable.addContractScope(SolidityContract.Current, CVLScope.newScope())
            ) { _, _ ->
                symbolTable.finalize()
                val typeChecker = CVLAstTypeChecker(symbolTable)
                typeChecker.typeCheck(ast)
            }.map { }
        }
    }

    fun assertTypeChecks(specTxt: String) {
        val res = typeCheckSpec(specTxt)
        assertTrue(res.succeeded())
    }

    fun assertNotTypeChecksWithError(specTxt: String, expectedError: String) {
        val res = typeCheckSpec(specTxt)
        assertFalse(res.succeeded())
        val errors = (res as CollectingResult.Error).messages
        assertNotNull(errors.singleOrNull()) { "did not get a single error, got: $errors" }
        assertEquals(expectedError, errors.single().message)
    }

    fun assertNotTypeChecks(specTxt: String) {
        val res = typeCheckSpec(specTxt)
        assertFalse(res.succeeded())
    }

    fun assertSyntaxError(specTxt: String, expectedError: String) {
        val res = compileSpec(specTxt)
        assert(res is CollectingResult.Error && res.messages.map {
            it.message
        }.contains(expectedError))
    }

    /**
     * Check that [specTxt] returns a single error of type [ERR].
     * @return the error
     */
    inline fun <reified ERR : CVLError> getSingleError(specTxt: String) : ERR {
        val res = typeCheckSpec(specTxt)
        check(res is CollectingResult.Error)  { "expected one error but got none" }
        check(res.messages.size == 1)         { "expected one error but got ${res.messages.size}" }

        val error = res.messages.single()
        check(error is ERR)    { "incorrect error type; expected [${ERR::class.simpleName}], got [${error.javaClass.simpleName}]." }
        return error
    }

    fun generateSingleParameterlessRule(ruleBody: String) = """
        rule myRule() {
            $ruleBody
        }
    """
}
