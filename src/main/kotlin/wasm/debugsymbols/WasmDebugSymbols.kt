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

package wasm.debugsymbols

import com.dylibso.chicory.wasm.Module
import com.dylibso.chicory.wasm.types.FunctionBody
import com.dylibso.chicory.wasm.types.SectionId
import datastructures.stdcollections.*
import dwarf.*
import kotlinx.serialization.ExperimentalSerializationApi
import report.CVTAlertReporter
import report.CVTAlertSeverity
import report.CVTAlertType
import utils.*
import wasm.ir.WASMAddress
import java.io.File


object WasmDebugSymbolLoader {
    /**
     * This method calls in a new process our own extension of gimli (https://github.com/gimli-rs/gimli). The extension uses
     * Gimli to parse the DWARF information from the WASM file and serializes the required information to JSON.
     *
     * After calling the extension, this method then deserializes the JSON to the data structure [WasmDebugSymbols]
     */
    @OptIn(ExperimentalSerializationApi::class)
    fun generate(wasmFile: File, module: Module, demangleNames: Boolean): WasmDebugSymbols? {
        val codeSectionOffset = WasmSectionOffsets.getSectionOffsets(wasmFile.inputStream())[SectionId.CODE.toByte()]

        if (codeSectionOffset == null) {
            CVTAlertReporter.reportAlert(
                type = CVTAlertType.DIAGNOSABILITY,
                severity = CVTAlertSeverity.WARNING,
                jumpToDefinition = null,
                message = "Failed to extract code section offset in WASM binary. Proceeding without debug information.",
                hint = null
            )
            return null
        }

        val debugSymbols = DebugSymbolLoader.generate(wasmFile, demangleNames)
        return if (debugSymbols == null) {
            null
        } else {
            WasmDebugSymbols(debugSymbols.compilationUnits, codeSectionOffset, module)
        }

    }
}

/**
 * This class contains DebugSymbols generated in DWARF (https://dwarfstd.org/)
 *
 * DWARF information is persisted in a tree structure. This class allows to easily lookup information, for instance, based on the bytecode address of an instructions.
 *
 *
 * More details on DWARF for WebAssembly can be found here: https://yurydelendik.github.io/webassembly-dwarf/
 */
class WasmDebugSymbols(
    compilationUnits: List<CompilationUnit>,
    private val codeSectionOffset: Int,
    val module: Module,
) : DebugSymbols(compilationUnits) {

    /**
     * For each instruction addr, this map stores the DWARFTreeNode related to the method the instruction
     * is contained within.
     */
    private val instructionAddrToMethod: Map<Int, DWARFTreeNode> = buildMap {
        val fbs = module.codeSection()?.functionBodies()?.filterNotNull()
        fbs?.forEach { body ->
            if (body.instructions().isNotEmpty()) {
                val firstInst = body.instructions()[0]
                compilationUnits.forEach { cu ->
                    cu.dwarf_node.postOrderTraversal { node, _, _ ->
                        if (node.dwarf_node_tag == DwTag.SUBPROGRAMM && node.hasHighPcValue() && node.hasLowPcValue()) {
                            if (isInRange(node, WASMAddress(firstInst.address()))) {
                                this[firstInst.address()] = this[firstInst.address()]?.let {
                                    if (it.depth > node.depth) {
                                        node
                                    } else {
                                        it
                                    }
                                } ?: node
                            }
                        }
                    }
                }
            }
        }
    }

    /**
     * This mapping contains for each instruction address the DWARFTreeNode at the deepest level of the tree
     * such that the instruction's address is in the range given by the DWARFTreeNode (i.e. low_pc_value <= addr < low_pc_value holds)
     */
    private val instructionAddrToDeepestNode: Map<WASMAddress, DWARFTreeNode> = buildMap {
        val fbs = module.codeSection()?.functionBodies()?.filterNotNull()

        fbs?.forEach { body ->
            val methodNode = lookUpByFunctionBody(body)
            body.instructions().forEach { ins ->
                methodNode?.postOrderTraversal { node, _, _ ->
                    if (node.hasHighPcValue() && node.hasLowPcValue()) {
                        val addr = WASMAddress(ins.address())
                        if (isInRange(node, addr)) {
                            this[addr] = this[addr]?.let {
                                if (it.depth < node.depth) {
                                    node
                                } else {
                                    it
                                }
                            } ?: node
                        }
                    }
                }
            }
        }
    }

    private fun isInRange(node: DWARFTreeNode, addr: WASMAddress): Boolean {
        check(node.low_pc_value != null && node.high_pc_value != null) { "Expecting the $node to have values for low and high pc, but no values are present" }
        return node.low_pc_value!! + codeSectionOffset <= addr.value && addr.value < node.high_pc_value!! + codeSectionOffset
    }


    private fun lookUpByFunctionBody(fb: FunctionBody): DWARFTreeNode? {
        val potentialMethods = fb.instructions().mapNotNullToSet { instructionAddrToMethod[it.address()] }
        check(potentialMethods.size <= 1) { "The debug information contains several methods for the function body ${potentialMethods.map { it.linkage_name }}" }
        return potentialMethods.firstOrNull()
    }

    override fun lookUpLineNumberInfo(addr: Int): LineNumberInfo? {
        // Since the addresses are relative from the code section start, we need to add the codeSectionOffset here.
        return super.lookUpLineNumberInfo(addr + codeSectionOffset)
    }

    /**
     * For a given instruction addr, this function returns the path in the DWARFTree to the node
     * satisfying the deepest match to be still in range of the node, see [instructionAddrToLineNumberInfo].
     *
     * The returned list is similar to the call stack. For a given It provides the (recursion free) call stack of all inlined method
     * relative to the beginning of a method.
     *
     * Note, nodes of certain type are filtered out as they are irrelevant.
     */
    fun lookUpCallStack(addr: WASMAddress): List<DWARFTreeNode> {
        var currEl = instructionAddrToDeepestNode[addr]
        val res = mutableListOf<DWARFTreeNode>()
        while (currEl != null) {
            res.add(currEl)
            currEl = childToParent[currEl]
        }
        return res.filter { it.dwarf_node_tag != DwTag.COMPILE_UNIT && it.dwarf_node_tag != DwTag.NAMESPACE && it.hasName() && it.hasHighPcValue() && it.hasLowPcValue() }
            .asReversed()
    }
}
