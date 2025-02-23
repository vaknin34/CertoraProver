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

import analysis.pta.*
import analysis.pta.abi.*
import annotation.*
import com.certora.collect.*
import loaders.SingleMethodTest
import optimizer.*
import org.junit.jupiter.api.*
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.params.*
import vc.data.CoreTACProgram

typealias PartitionInfo = Map<Partition, Map<PartitionField, Partition>>
typealias PartitionEntry = Map.Entry<Partition, Map<PartitionField, Partition>>

@Disabled("Partition info work not done yet")
class PartitionInfoTest : SingleMethodTest {


    private fun checkIsomorphic(expected: PartitionInfo, actual: PartitionInfo) {
        fun isomorphic(i1: List<PartitionEntry>, i2: List<PartitionEntry>, iso: TreapMap<Int, Int>, ind: Int) : Boolean {
            if(ind == i1.size) {
                return true
            }
            val e1 = i1[ind]
            nxt@for(i in 0..i2.lastIndex) {
                val e2 = i2[i]
                if(iso[e2.key.id] != null && iso[e2.key.id] != e1.key.id) {
                    continue
                }
                if(e2.key.id !in iso && e1.key.id in iso.values) {
                    continue
                }
                if(e1.value.keys != e2.value.keys) {
                    continue
                }
                val builder = iso.builder()
                // the key for e2 is not yet assigned. Try to match the entries.
                builder[e2.key.id] = e1.key.id
                for((k1, p1) in e1.value) {
                    val p2 = e2.value[k1]!!
                    if(p2.id !in builder) {
                        if(p1.id in builder.values) {
                            continue@nxt
                        }
                        builder[p2.id] = p1.id
                    } else if(builder[p2.id]!! != p1.id) {
                        continue@nxt
                    }
                }
                // the keys match. try to continue on to the next entry
                if(isomorphic(i1, i2, builder.build(), ind + 1)) {
                    return true
                }
            }
            return false
        }

        fun isomorphic(i1: PartitionInfo, i2: PartitionInfo) : Boolean {
            return isomorphic(i1.entries.toList(), i2.entries.toList(), treapMapOf(), 0)
        }

        assertTrue(isomorphic(expected, actual)) {
            "Could not find isomorphism between $expected and $actual"
        }
    }

    private fun checkPartitionInfo(src: String, expected: PartitionInfo, solc: String = "solc") {
        val m = this.loadTestMethod(src, solc = solc, optimize = false)
        val p = m.code as CoreTACProgram

        val actual = p.getPartitionInfo()

        checkIsomorphic(expected, actual)
    }

    @Test
    fun nestedStruct() {
        checkPartitionInfo(
            """
                contract Test {
                    struct Foo {
                        uint a;
                        uint b;
                    }
                    struct Bar {
                        Foo foo;
                    }
                    function test(Bar[] memory z) external returns (uint) {
                        return z[100].foo.b + z.length;
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(0, 0) to mapOf(
                    PartitionField.StructField(0) to Partition(1, 0),
                ),
                Partition(1, 0) to mapOf(
                    PartitionField.StructField(0) to Partition(3, 0),
                    PartitionField.StructField(32) to Partition(2, 0),
                ),
            )
        )
    }

    @Test
    fun nestedArray() {
        checkPartitionInfo(
            """
                contract Test {
                    function test(uint[][] memory z) public returns (uint) {
                        return z[0][0] + z[1][1];
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(0, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(1, 0),
                    PartitionField.ArrayElement(32) to Partition(2, 0),
                ),
            )
        )
    }

    @Test
    fun nestedArrayMultipleArguments() {
        checkPartitionInfo(
            """
                contract Test {
                    function test(uint[][] memory z, uint[][] memory y) public returns (uint) {
                        return z[0][0] + y[0][0];
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(0, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(1, 0),
                    PartitionField.ArrayElement(32) to Partition(2, 0),
                ),
                Partition(3, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(4, 0),
                    PartitionField.ArrayElement(32) to Partition(5, 0),
                ),
            )
        )
    }

    @Test
    fun nestedArrayWithCalls() {
        checkPartitionInfo(
            """
                contract Test {
                    function test(uint[][] memory z) public returns (uint) {
                        return foo(z[0]) + foo(z[1]) + bar(z);
                    }
                    function foo(uint[] memory z) public returns (uint) {
                        return z[0];
                    }
                    function bar(uint[][] memory z) public returns (uint) {
                        return z[0][1] + z[1][1];
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(2, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(3, 0),
                    PartitionField.ArrayElement(32) to Partition(1, 0),
                ),
            )
        )
    }


    @Test
    fun simpleArray() {
        checkPartitionInfo(
            """
                contract Test {
                    function test(uint[] memory z) public returns (uint) {
                        return z[0];
                    }
                }
            """.trimIndent(),
            mapOf()
        )
    }


    @Test
    fun simpleStruct() {
        checkPartitionInfo(
            """
                contract Test {
                    struct Foo {
                        uint a;
                        uint b;
                    }
                    function test(Foo memory foo) public returns (uint) {
                        return foo.a + foo.b;
                    }
                }
            """.trimIndent(),
            mapOf()
        )
    }

    @Test
    fun emptyArray() {
        checkPartitionInfo(
            """
                contract Test {
                    function test() public returns (uint) {
                        uint[] memory z = new uint[](0);
                        return z[0];
                    }
                }
            """.trimIndent(),
            mapOf()
        )
    }

    @Test
    fun nestedConstArray() {
        checkPartitionInfo(
            """
                contract Test {
                    function test() public returns (uint) {
                        uint[][] memory z = new uint[][](1);
                        z[0] = new uint[](1);
                        return z[0][0];
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(0, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(1, 0),
                    PartitionField.ArrayElement(32) to Partition(2, 0),
                ),
            )
        )
    }

    @Test
    fun moreNestedConstArray() {
        checkPartitionInfo(
            """
                contract Test {
                    function test() public returns (uint) {
                        uint[][][][] memory z = new uint[][][][](1);
                        z[0] = new uint[][][](1);
                        z[0][0] = new uint[][](1);
                        z[0][0][0] = new uint[](1);
                        return z[0][0][0][0];
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(0, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(1, 0),
                    PartitionField.ArrayElement(32) to Partition(2, 0),
                ),
                Partition(2, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(1, 0),
                    PartitionField.ArrayElement(32) to Partition(3, 0),
                ),
                Partition(3, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(1, 0),
                    PartitionField.ArrayElement(32) to Partition(4, 0),
                ),
            )
        )
    }

    @Test
    fun multipleArrayAssignments() {
        checkPartitionInfo(
            """
                contract Test {
                    function test() public returns (uint) {
                        uint[][] memory z = new uint[][](1);
                        z[0] = new uint[](1);
                        uint a = z[0][0];
                        z = new uint[][](2);
                        z[0] = new uint[](2);
                        uint b = z[0][0];
                        return a + b;
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(1, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(2, 0),
                    PartitionField.ArrayElement(32) to Partition(3, 0),
                ),
                Partition(4, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(2, 0),
                    PartitionField.ArrayElement(32) to Partition(6, 0),
                ),
            )
        )
    }


    @Test
    fun multipleStructAssignments() {
        checkPartitionInfo(
            """
                contract Test {
                    struct Foo {
                        uint a;
                        uint b;
                    }
                    struct Bar {
                        Foo foo;
                    }
                    function test() external returns (uint) {
                        Bar memory z = Bar(Foo(1, 2));
                        uint a = z.foo.a + z.foo.b;
                        z = Bar(Foo(3, 4));
                        uint b = z.foo.a + z.foo.b;
                        return a + b;
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(2, 0) to mapOf(
                    PartitionField.StructField(0) to Partition(0, 0),
                    PartitionField.StructField(32) to Partition(1, 0),
                ),
                Partition(5, 0) to mapOf(
                    PartitionField.StructField(0) to Partition(3, 0),
                    PartitionField.StructField(32) to Partition(4, 0),
                ),
            )
        )
    }


    @Test
    fun nestedEmptyArray() {
        checkPartitionInfo(
            """
                contract Test {
                    function test() external returns (uint) {
                        uint[][] memory z = new uint[][](1);
                        z[0] = new uint[](0);
                        return z[0].length;
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(1, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(2, 0),
                ),
            )
        )
    }

    @Test
    fun nestedMaybeEmptyArray() {
        checkPartitionInfo(
            """
                contract Test {
                    struct Foo {
                        uint[] a;
                    }
                    function test() external returns (uint) {
                        Foo memory z = Foo(new uint[](0));
                        uint[] memory a = z.a;
                        z.a = new uint[](1);
                        uint[] memory b = z.a;
                        return a.length + b.length + b[0];
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(3, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(2, 0),
                    PartitionField.ArrayElement(32) to Partition(5, 0),
                ),
            )
        )
    }

    @Test
    fun structWithArray() {
        checkPartitionInfo(
            """
                contract Test {
                    struct Foo {
                        uint[] a;
                    }
                    function test() external returns (uint) {
                        Foo memory z = Foo(new uint[](1));
                        uint a = z.a[0];
                        z.a = new uint[](3);
                        uint b = z.a[0];
                        return a + b;
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(4, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(2, 0),
                    PartitionField.ArrayElement(32) to Partition(3, 0),
                ),
            )
        )
    }

    @Test
    fun structWithBytes() {
        checkPartitionInfo(
            """
                contract Test {
                    struct Foo {
                        bytes a;
                    }
                    function test(uint n) external returns (uint) {
                        Foo memory z = Foo(new bytes(n));
                        return z.a.length;
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(4, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(2, 0),
                    PartitionField.ArrayElement(1) to Partition(3, 0),
                ),
            )
        )
    }

    @Test
    fun structWithConstantBytes() {
        checkPartitionInfo(
            """
                contract Test {
                    struct Foo {
                        bytes a;
                    }
                    function test() external returns (uint) {
                        Foo memory z = Foo(new bytes(2));
                        return z.a.length;
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(4, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(2, 0),
                    PartitionField.ArrayElement(1) to Partition(3, 0),
                ),
            )
        )
    }

    @Test
    @Tag(annotations.TestTags.TEMPORARY_NO_CI) // CERT-3129
    fun structWithBytesArgument() {
        checkPartitionInfo(
            """
                pragma experimental ABIEncoderV2;
                contract Test {
                    struct Foo {
                        bytes a;
                    }
                    function test(Foo memory z) public returns (bytes1) {
                        return z.a[0];
                    }
                }
            """.trimIndent(),
            mapOf(
                Partition(5, 0) to mapOf(
                    PartitionField.ArrayLength to Partition(4, 0),
                    PartitionField.ArrayElement(1) to Partition(2, 0),
                ),
            )
        )
    }
}

