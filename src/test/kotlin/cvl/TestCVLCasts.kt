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

import infra.CVLFlow
import org.junit.jupiter.api.Test
import kotlin.io.path.Path

class TestCVLCasts: AbstractCVLTest() {

    @Test
    fun testCastExp1() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/CVLSyntax/CastExp/badExample1/badExample1.conf")), listOf(
                ExpType("to_uint256"), ExpType("assert_bool"), ExpType("to_uint256")
            )
        )
    }

    @Test
    fun testCastExp2() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/CVLSyntax/CastExp/badExample2/badExample2.conf")), listOf(
                GeneralType("bad6.spec", 2, 2),
                GeneralType("bad6.spec", 8, 8),
            )
        )
    }

    @Test
    fun testCastExp3() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/CVLSyntax/CastExp/badExample3/badExample3.conf")), listOf(
                ExpType("assert"), ExpType("assert"), ExpType("assert"), ExpType("to")
            )
        )
    }

    @Test
    fun testBytesk() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/CVLSyntax/CastExp/BytesK/badExample/badExample.conf")), listOf(
                ExpType("to"), ExpType("to"), ExpType("to")
            )
        )
    }

    @Test
    fun testToBytesOfLessThan20BytesFromAddress() {
        val confPath = Path("src/test/resources/cvl/CVLSyntax/CastExp/BytesK/badToBytes/CastToBytes.conf")
        val primaryContractName = "CastToBytes"
        val cvlText = """
        rule disallowBytes1() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes1 b = to_bytes1(a);
            assert false, "Type checker allowed cast to bytes1 but it should not have";
        }

        rule disallowBytes2() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes2 b = to_bytes2(a);
            assert false, "Type checker allowed cast to bytes2 but it should not have";
        }

        rule disallowBytes3() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes3 b = to_bytes3(a);
            assert false, "Type checker allowed cast to bytes3 but it should not have";
        }

        rule disallowBytes4() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes4 b = to_bytes4(a);
            assert false, "Type checker allowed cast to bytes4 but it should not have";
        }

        rule disallowBytes5() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes5 b = to_bytes5(a);
            assert false, "Type checker allowed cast to bytes5 but it should not have";
        }

        rule disallowBytes6() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes6 b = to_bytes6(a);
            assert false, "Type checker allowed cast to bytes6 but it should not have";
        }

        rule disallowBytes7() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes7 b = to_bytes7(a);
            assert false, "Type checker allowed cast to bytes7 but it should not have";
        }

        rule disallowBytes8() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes8 b = to_bytes8(a);
            assert false, "Type checker allowed cast to bytes8 but it should not have";
        }

        rule disallowBytes9() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes9 b = to_bytes9(a);
            assert false, "Type checker allowed cast to bytes9 but it should not have";
        }

        rule disallowBytes10() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes10 b = to_bytes10(a);
            assert false, "Type checker allowed cast to bytes10 but it should not have";
        }

        rule disallowBytes11() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes11 b = to_bytes11(a);
            assert false, "Type checker allowed cast to bytes11 but it should not have";
        }

        rule disallowBytes12() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes12 b = to_bytes12(a);
            assert false, "Type checker allowed cast to bytes12 but it should not have";
        }

        rule disallowBytes13() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes13 b = to_bytes13(a);
            assert false, "Type checker allowed cast to bytes13 but it should not have";
        }

        rule disallowBytes14() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes14 b = to_bytes14(a);
            assert false, "Type checker allowed cast to bytes14 but it should not have";
        }

        rule disallowBytes15() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes15 b = to_bytes15(a);
            assert false, "Type checker allowed cast to bytes15 but it should not have";
        }

        rule disallowBytes16() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes16 b = to_bytes16(a);
            assert false, "Type checker allowed cast to bytes16 but it should not have";
        }

        rule disallowBytes17() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes17 b = to_bytes17(a);
            assert false, "Type checker allowed cast to bytes17 but it should not have";
        }

        rule disallowBytes18() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes18 b = to_bytes18(a);
            assert false, "Type checker allowed cast to bytes18 but it should not have";
        }

        rule disallowBytes19() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes19 b = to_bytes19(a);
            assert false, "Type checker allowed cast to bytes19 but it should not have";
        }

        rule disallowBytes20() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes20 b = to_bytes20(a);
            assert false, "Type checker allowed cast to bytes20 but it should not have";
        }

        rule disallowBytes21() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes21 b = to_bytes21(a);
            assert false, "Type checker allowed cast to bytes21 but it should not have";
        }

        rule disallowBytes22() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes22 b = to_bytes22(a);
            assert false, "Type checker allowed cast to bytes22 but it should not have";
        }

        rule disallowBytes23() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes23 b = to_bytes23(a);
            assert false, "Type checker allowed cast to bytes23but it should not have";
        }

        rule disallowBytes24() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes24 b = to_bytes24(a);
            assert false, "Type checker allowed cast to bytes24 but it should not have";
        }

        rule disallowBytes25() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes25 b = to_bytes25(a);
            assert false, "Type checker allowed cast to bytes25 but it should not have";
        }

        rule disallowBytes26() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes26 b = to_bytes26(a);
            assert false, "Type checker allowed cast to bytes26 but it should not have";
        }

        rule disallowBytes27() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes27 b = to_bytes27(a);
            assert false, "Type checker allowed cast to bytes27 but it should not have";
        }

        rule disallowBytes28() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes28 b = to_bytes28(a);
            assert false, "Type checker allowed cast to bytes28 but it should not have";
        }

        rule disallowBytes29() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes29 b = to_bytes29(a);
            assert false, "Type checker allowed cast to bytes29 but it should not have";
        }

        rule disallowBytes30() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes30 b = to_bytes30(a);
            assert false, "Type checker allowed cast to bytes30 but it should not have";
        }

        rule disallowBytes31() {
            address a = 0x3729D00fe4f5eb341f95FDC9051B94A9b6C26160;
            bytes31 b = to_bytes31(a);
            assert false, "Type checker allowed cast to bytes31 but it should not have";
        }
        """.trimIndent()
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(confPath, cvlText, primaryContractName), listOf(
                ExpType("to")
            )
        )
    }

    @Test
    fun testFromBytesOfLessThan20BytesToAddress() {
        val confPath = Path("src/test/resources/cvl/CVLSyntax/CastExp/Address/badFromBytes/CastFromBytes.conf")
        val primaryContractName = "CastFromBytes"
        val cvlText = """
        rule requireBytes1() {
            bytes1 b = to_bytes1(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes1, but it did not";
        }

        rule assertBytes1() {
            bytes1 b = to_bytes1(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes1, but it did not";
        }

        rule requireBytes2() {
            bytes2 b = to_bytes2(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes2, but it did not";
        }

        rule assertBytes2() {
            bytes2 b = to_bytes2(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes2, but it did not";
        }

        rule requireBytes3() {
            bytes3 b = to_bytes3(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes3, but it did not";
        }

        rule assertBytes3() {
            bytes3 b = to_bytes3(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes3, but it did not";
        }

        rule requireBytes4() {
            bytes4 b = to_bytes4(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes4, but it did not";
        }

        rule assertBytes4() {
            bytes4 b = to_bytes4(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes4, but it did not";
        }

        rule requireBytes5() {
            bytes5 b = to_bytes5(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes5, but it did not";
        }

        rule assertBytes5() {
            bytes5 b = to_bytes5(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes5, but it did not";
        }

        rule requireBytes6() {
            bytes6 b = to_bytes6(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes6, but it did not";
        }

        rule assertBytes6() {
            bytes6 b = to_bytes6(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes6, but it did not";
        }

        rule requireBytes7() {
            bytes7 b = to_bytes7(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes7, but it did not";
        }

        rule assertBytes7() {
            bytes7 b = to_bytes7(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes7, but it did not";
        }

        rule requireBytes8() {
            bytes8 b = to_bytes8(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes8, but it did not";
        }

        rule assertBytes8() {
            bytes8 b = to_bytes8(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes8, but it did not";
        }

        rule requireBytes9() {
            bytes9 b = to_bytes9(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes9, but it did not";
        }

        rule assertBytes9() {
            bytes9 b = to_bytes9(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes9, but it did not";
        }

        rule requireBytes10() {
            bytes10 b = to_bytes10(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes10, but it did not";
        }

        rule assertBytes10() {
            bytes10 b = to_bytes10(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes10, but it did not";
        }

        rule requireBytes11() {
            bytes11 b = to_bytes11(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes11, but it did not";
        }

        rule assertBytes11() {
            bytes11 b = to_bytes11(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes11, but it did not";
        }

        rule requireBytes12() {
            bytes12 b = to_bytes12(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes12, but it did not";
        }

        rule assertBytes12() {
            bytes12 b = to_bytes12(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes12, but it did not";
        }

        rule requireBytes13() {
            bytes13 b = to_bytes13(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes13, but it did not";
        }

        rule assertBytes13() {
            bytes13 b = to_bytes13(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes13, but it did not";
        }

        rule requireBytes14() {
            bytes14 b = to_bytes14(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes14, but it did not";
        }

        rule assertBytes14() {
            bytes14 b = to_bytes14(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes14, but it did not";
        }

        rule requireBytes15() {
            bytes15 b = to_bytes15(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes15, but it did not";
        }

        rule assertBytes15() {
            bytes15 b = to_bytes15(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes15, but it did not";
        }

        rule requireBytes16() {
            bytes16 b = to_bytes16(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes16, but it did not";
        }

        rule assertBytes16() {
            bytes16 b = to_bytes16(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes16, but it did not";
        }

        rule requireBytes17() {
            bytes17 b = to_bytes17(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes17, but it did not";
        }

        rule assertBytes17() {
            bytes17 b = to_bytes17(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes17, but it did not";
        }

        rule requireBytes18() {
            bytes18 b = to_bytes18(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes18, but it did not";
        }

        rule assertBytes18() {
            bytes18 b = to_bytes18(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes18, but it did not";
        }

        rule requireBytes19() {
            bytes19 b = to_bytes19(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes19, but it did not";
        }

        rule assertBytes19() {
            bytes19 b = to_bytes19(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes19, but it did not";
        }

        rule requireBytes20() {
            bytes20 b = to_bytes20(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes20, but it did not";
        }

        rule assertBytes20() {
            bytes20 b = to_bytes20(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes20, but it did not";
        }

        rule requireBytes21() {
            bytes21 b = to_bytes21(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes21, but it did not";
        }

        rule assertBytes21() {
            bytes21 b = to_bytes21(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes21, but it did not";
        }

        rule requireBytes22() {
            bytes22 b = to_bytes22(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes22, but it did not";
        }

        rule assertBytes22() {
            bytes22 b = to_bytes22(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes22, but it did not";
        }

        rule requireBytes23() {
            bytes23 b = to_bytes23(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes23, but it did not";
        }

        rule assertBytes23() {
            bytes23 b = to_bytes23(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes23, but it did not";
        }

        rule requireBytes24() {
            bytes24 b = to_bytes24(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes24, but it did not";
        }

        rule assertBytes24() {
            bytes24 b = to_bytes24(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes24, but it did not";
        }

        rule requireBytes25() {
            bytes25 b = to_bytes25(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes25, but it did not";
        }

        rule assertBytes25() {
            bytes25 b = to_bytes25(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes25, but it did not";
        }

        rule requireBytes26() {
            bytes26 b = to_bytes26(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes26, but it did not";
        }

        rule assertBytes26() {
            bytes26 b = to_bytes26(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes26, but it did not";
        }

        rule requireBytes27() {
            bytes27 b = to_bytes27(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes27, but it did not";
        }

        rule assertBytes27() {
            bytes27 b = to_bytes27(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes27, but it did not";
        }

        rule requireBytes28() {
            bytes28 b = to_bytes28(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes28, but it did not";
        }

        rule assertBytes28() {
            bytes28 b = to_bytes28(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes28, but it did not";
        }

        rule requireBytes29() {
            bytes29 b = to_bytes29(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes29, but it did not";
        }

        rule assertBytes29() {
            bytes29 b = to_bytes29(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes29, but it did not";
        }

        rule requireBytes30() {
            bytes30 b = to_bytes30(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes30, but it did not";
        }

        rule assertBytes30() {
            bytes30 b = to_bytes30(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes30, but it did not";
        }

        rule requireBytes31() {
            bytes31 b = to_bytes31(0x10);
            address a = require_address(b);
            assert false, "Type checker should have prevented cast from bytes31, but it did not";
        }

        rule assertBytes31() {
            bytes31 b = to_bytes31(0x10);
            address a = assert_address(b);
            assert false, "Type checker should have prevented assert cast from bytes31, but it did not";
        }
        """.trimIndent()
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(confPath, cvlText, primaryContractName), listOf(
                ExpType("require"), ExpType("assert")
            )
        )
    }

    @Test
    fun testBytes32FromAddress() {
        val confPath = Path("src/test/resources/cvl/CVLSyntax/CastExp/BytesK/toBytes32/CastToBytes32.conf")
        val primaryContractName = "CastToBytes32"
        val cvlText = """
            rule addressToBytes32() {
                address theAddress = 0xa44f5d3d624DfD660ecc11FF777587AD0a19606d;
                bytes32 bytesValue = to_bytes32(theAddress);
                bytes32 expected = to_bytes32(0xa44f5d3d624DfD660ecc11FF777587AD0a19606d);
                assert bytesValue == expected;
            }
        """.trimIndent()
        testNoErrors(
            CVLFlow().getProverQuery(confPath, cvlText, primaryContractName)
        )
    }

    @Test
    fun testSmallAddressToBytes32() {
        val confPath = Path("src/test/resources/cvl/CVLSyntax/CastExp/BytesK/toBytes32/CastToBytes32.conf")
        val primaryContractName = "CastToBytes32"
        val cvlText = """
            rule smallAddressToBytes32() {
            	address theAddress = 0x123456;
            	bytes32 bytesValue = to_bytes32(theAddress);
                bytes32 expected = to_bytes32(0x123456);
            	assert bytesValue == expected;
            }
        """.trimIndent()
        testNoErrors(
            CVLFlow().getProverQuery(confPath, cvlText, primaryContractName)
        )
    }

    @Test
    fun testRequireCastToAddressCouldFail() {
        val confPath = Path("src/test/resources/cvl/CVLSyntax/CastExp/Address/CastToAddress.conf")
        val primaryContractName = "CastToAddress"
        val cvlText = """
            rule intRequireCastCanFail {
            	bytes32 ui = to_bytes32(0x10000000000000000000000000000000000000000);
            	address addr = require_address(ui);
            	assert true;
            }
        """.trimIndent()
        testNoErrors(
            CVLFlow().getProverQuery(confPath, cvlText, primaryContractName)
        )
    }

    @Test
    fun testSmallIntRequireCastToAddress() {
        val confPath = Path("src/test/resources/cvl/CVLSyntax/CastExp/Address/CastToAddress.conf")
        val primaryContractName = "CastToAddress"
        val cvlText = """
            rule smallIntRequireCast {
            	bytes32 ui = to_bytes32(0x12345);
            	address a = require_address(ui);
                address expected = 0x12345;
            	assert a == expected;
            }
        """.trimIndent()
        testNoErrors(
            CVLFlow().getProverQuery(confPath, cvlText, primaryContractName)
        )
    }

    @Test
    fun testRequireCastToAddressInRange() {
        val confPath = Path("src/test/resources/cvl/CVLSyntax/CastExp/Address/CastToAddress.conf")
        val primaryContractName = "CastToAddress"
        val cvlText = """
            rule intRequireCast {
            	bytes32 ui = to_bytes32(0xffffffffffffffffffffffffffffffffffff);
            	address addr = require_address(ui);
                address expected = 0xffffffffffffffffffffffffffffffffffff;
            	assert addr == expected;
            }
        """.trimIndent()
        testNoErrors(
            CVLFlow().getProverQuery(confPath, cvlText, primaryContractName)
        )
    }

    @Test
    fun testAssertCastToAddressInRange() {
        val confPath = Path("src/test/resources/cvl/CVLSyntax/CastExp/Address/CastToAddress.conf")
        val primaryContractName = "CastToAddress"
        val cvlText = """
            rule intAssertCast {
               bytes32 ui = to_bytes32(0xffffffffffffffffffffffffffffffffffff);
               address addr = assert_address(ui);
               address expected = 0xffffffffffffffffffffffffffffffffffff;
               assert addr == expected;
            }
        """.trimIndent()
        testNoErrors(
            CVLFlow().getProverQuery(confPath, cvlText, primaryContractName)
        )
    }

    @Test
    fun testCast() {
        val confPath = Path("src/test/resources/cvl/Quantifiers/badExample1/badExample1.conf")
        val primaryContractName = "test"
        val cvlText = """
            rule example(uint256 i) {
                mathint j = 2;
                assert i == assert_uint256(j);
            }
        """.trimIndent()
        testNoErrors(CVLFlow().getProverQuery(confPath, cvlText, primaryContractName))
    }

    @Test
    fun testCastNumberToBytes() {
        val confPath = Path("src/test/resources/cvl/Quantifiers/badExample1/badExample1.conf")
        val primaryContractName = "test"
        val cvlText = """
            rule example(bytes32 i) {
                bytes32 j = to_bytes32(2);
                assert i == j;
            }
        """.trimIndent()
        testNoErrors(CVLFlow().getProverQuery(confPath, cvlText, primaryContractName))
    }

}
