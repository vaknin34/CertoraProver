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

import annotations.TestTags.EXPENSIVE
import net.jqwik.api.*
import spec.cvlast.CVLType
import spec.cvlast.typedescriptors.EVMTypeDescriptor
import spec.cvlast.typedescriptors.FromVMContext
import spec.cvlast.typedescriptors.ToVMContext

@Tag(EXPENSIVE)
class ConverterTestsFull : ConverterTests() {
    @Property(tries = 100000, edgeCases = EdgeCasesMode.NONE, maxDiscardRatio = 300)
    fun testCorrespondenceImpliesConvertibility(
            @ForAll("evmType") evmType: EVMTypeDescriptor,
            @ForAll("fromVMContext") ctxt: FromVMContext
    ) {
        super.templateTestCorrespondenceImpliesConvertibility(evmType, ctxt)
    }

    @Property(tries = 100000, edgeCases = EdgeCasesMode.NONE, maxDiscardRatio = 300)
    fun testReflexivity(
        @ForAll("cvlType") cvlType: CVLType.PureCVLType
    ) {
        super.templateTestReflexivity(cvlType)
    }

    @Property(tries = 100000, edgeCases = EdgeCasesMode.NONE, maxDiscardRatio = 1000)
    fun testTransitivity(
            @ForAll("cvlType") t: CVLType.PureCVLType,
            @ForAll("cvlType") u: CVLType.PureCVLType,
            @ForAll("cvlType") v: CVLType.PureCVLType
    ) {
        super.templateTestTransitivity(t, u, v)
    }

    @Property(tries = 100000, edgeCases = EdgeCasesMode.NONE, maxDiscardRatio = 1000)
    fun testTagSubtyping(
            @ForAll("cvlType") t: CVLType.PureCVLType,
            @ForAll("cvlType") u: CVLType.PureCVLType,
    ) {
        super.templateTestTagSubtyping(t, u)
    }

    @Property(tries = 1000000, edgeCases = EdgeCasesMode.NONE, maxDiscardRatio = 300)
    fun testAntisymmetry(
            @ForAll("cvlType") t: CVLType.PureCVLType,
            @ForAll("cvlType") u: CVLType.PureCVLType
    ) {
        super.templateTestAntisymmetry(t, u)
    }

    @Property(tries = 100000, edgeCases = EdgeCasesMode.NONE, maxDiscardRatio = 1000)
    fun testSubtypingCoherentInConvertibilityFromVM(
            @ForAll("cvlType") t: CVLType.PureCVLType,
            @ForAll("cvlType") u: CVLType.PureCVLType,
            @ForAll("evmType") v: EVMTypeDescriptor,
            @ForAll("fromVMContext") ctxt: FromVMContext
    ) {
        super.templateTestSubtypingCoherentInConvertibilityFromVM(t, u, v, ctxt)
    }

    @Property(tries = 100000, edgeCases = EdgeCasesMode.NONE, maxDiscardRatio = 1000)
    fun fuzzTestSubtypingCoherentInConvertibilityToVM(
            @ForAll("cvlType") t: CVLType.PureCVLType,
            @ForAll("cvlType") u: CVLType.PureCVLType,
            @ForAll("evmType") v: EVMTypeDescriptor,
            @ForAll("toVMContext") ctxt: ToVMContext
    ) {
        super.templateFuzzTestSubtypingCoherentInConvertibilityToVM(t, u, v, ctxt)
    }

    @FromData("problematicSubtypingCoherentInConvertibilityToVMCases")
    @Property
    fun specificTestSubtypingCoherentInConvertibilityToVM(
            @ForAll("cvlType") t: CVLType.PureCVLType,
            @ForAll("cvlType") u: CVLType.PureCVLType,
            @ForAll("evmType") v: EVMTypeDescriptor,
            @ForAll("toVMContext") ctxt: ToVMContext
    ) {
        super.templateSpecificTestSubtypingCoherentInConvertibilityToVM(t, u, v, ctxt)
    }

    @Property(tries = 100000, edgeCases = EdgeCasesMode.NONE, maxDiscardRatio = 300)
    fun testMergingCommutative(
            @ForAll("evmType") t: EVMTypeDescriptor,
            @ForAll("evmType") u: EVMTypeDescriptor
    ) {
        super.templateTestMergingCommutative(t, u)
    }

    @Property(tries = 100000, edgeCases = EdgeCasesMode.NONE, maxDiscardRatio = 1000)
    fun testMergingAssociative(
            @ForAll("evmType") t: EVMTypeDescriptor,
            @ForAll("evmType") u: EVMTypeDescriptor,
            @ForAll("evmType") v: EVMTypeDescriptor
    ) {
        super.templateTestMergingAssociative(t, u, v)
    }

    @Property(tries = 100000, edgeCases = EdgeCasesMode.NONE, maxDiscardRatio = 300)
    fun testConvertibilityImpliesCodeGenWorks(
            @ForAll("cvlType") cvlType: CVLType.PureCVLType,
            @ForAll("evmType") evmType: EVMTypeDescriptor,
            @ForAll("contexts") ctxt: ConversionSpec<*, *, *>
    ) {
        super.templateTestConvertibilityImpliesCodeGenWorks(cvlType, evmType, ctxt)
    }

    @Property(tries = 100000, edgeCases = EdgeCasesMode.NONE, maxDiscardRatio = 300)
    fun testToTagTotal(
        @ForAll("cvlType") cvlType: CVLType.PureCVLType) {
        super.templateTestToTagTotal(cvlType)
    }
}
