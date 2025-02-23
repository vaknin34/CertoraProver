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

package analysis

import analysis.pta.FlowPointsToInformation
import analysis.pta.IPointsToInformation
import annotation.ScopedVersions
import annotation.WithOptimizedFlag
import loaders.SingleMethodTest
import loaders.WithResourceFile
import loaders.runPTA
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import testing.wrapInTrivialContract

abstract class PointsToTest : SingleMethodTest, WithResourceFile {
    protected fun assertAnalysisSucceeds(solc: String, contract: String, optimize: Boolean) {
        val check = { pta: IPointsToInformation ->
            Assertions.assertTrue(pta is FlowPointsToInformation) {
                "Expected analysis to succeed with flow result on $solc with $optimize"
            }
        }
        assertAnalysisResult(contract, solc, optimize, check)
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    open fun testTryCatchWithDecode(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(solc, optimize) {
            """contract Test {
	function test(address o) external returns (bool, uint) {
		try Test(o).swap(33) returns (uint amt) {
			return (true, amt);
		} catch Error(string memory reason) {
			return (false, bytes(reason).length);
		} catch (bytes memory reason) {
			revert(string(reason));
		}
	}

	function swap(uint x) external returns (uint)  {
		return x * 2;
	}
}
"""
        }
    }

    private fun assertAnalysisResult(
        contract: String,
        solc: String,
        optimize: Boolean,
        check: (IPointsToInformation) -> Unit
    ) {
        this.loadTestMethod(contract, solc, optimize = optimize).let {
            val pta = runPTA(it)
            check(pta)
        }
    }

    private fun assertAnalysisSucceeds(solc: String, optimize: Boolean, contract: () -> String) {
        return this.assertAnalysisSucceeds(solc, contract(), optimize)
    }

    private fun assertAnalysisFails(solc: String, optimize: Boolean, contract: String) {
        this.assertAnalysisResult(contract = contract, solc = solc, optimize = optimize) {
            Assertions.assertTrue(it !is FlowPointsToInformation || !it.isCompleteSuccess) {
                "Surprising (unexpected) successful points to result"
            }
        }
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun arrayArgumentCopy(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(solc, optimize) {
            """contract Test {
                | function test(uint[] memory hello) public { }
                |}""".trimMargin()
        }
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun stringArgumentCopy(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(solc, optimize) {
            """contract Test {
                |  function test(string memory hello) public { }
                |}
            """.trimMargin()
        }
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun stringArgumentReturn(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(solc, optimize) {
            """contract Test {
                | function test(string memory hello) public returns (string memory) { return hello; }
                |}""".trimMargin()
        }
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun arrayArgumentReturn(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(solc, optimize) {
            """contract Test {
                | function test(uint[] memory hello) public returns (uint[] memory) { return hello; }
                |}""".trimMargin()
        }
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun arrayArgumentIterate(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(solc, optimize) {
            """contract Test {
                  function test(address[] memory compMarketsToAdd) public {
                    for (uint i = 0; i < compMarketsToAdd.length; i++) {
                      _addMarketInternal(address(compMarketsToAdd[i]));
                    }
                  }

                  function _addMarketInternal(address tok) internal {
                    // do nothing
                  }
                }
            """
        }
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testStorageCopy(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(solc, this.loadResourceFile("analysis/StorageArrayCopy.sol")!!, optimize)
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testInlineStaticScratch(solc: String, optimize: Boolean) {
        val target = if (solc.startsWith("solc5")) {
            "msg.sender"
        } else {
            "payable(msg.sender)"
        }
        this.assertAnalysisSucceeds(solc, optimize) {
            """$target.transfer(amount);

	bool success;
	assembly {
	  switch returndatasize()
							 case 0 {                      // This is a non-standard ERC-20
		success := not(0)          // set success to true
							   }
	  case 32 {                     // This is a complaint ERC-20
		returndatacopy(0, 0, 32)
		  success := mload(0)        // Set `success = returndata` of external call
		  }
	  default {                     // This is an excessively non-compliant ERC-20, revert.
		revert(0, 0)
		  }
	}
	""".wrapInTrivialContract(null, "amount")
        }
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testArrayAllocation(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(solc, optimize) {
            """
                uint[] memory hello = new uint[](world);
                uint x = 0;
                for(uint i = 0; i < hello.length; i++) {
                    x += hello[i];
                }
            """.trimIndent().wrapInTrivialContract(null, "world")
        }
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testPackedEncode(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(solc, optimize) {
            """
                bytes memory z = new bytes(hello);
                uint[] memory y = new uint[](world);
                return keccak256(abi.encodePacked(z, y));
            """.trimIndent().wrapInTrivialContract("bytes32", "hello", "world")
        }
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testStringSetter(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(solc, this.loadResourceFileOrCrash("analysis/SetString.sol"), optimize)
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    open fun testRawCallWithReturn(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(solc, this.loadResourceFileOrCrash("analysis/RawCallWithReturn.sol"), optimize)
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testEmptyArrayLoop(solc: String, optimize: Boolean) {
        val contract = """
            contract Test {
                function test(uint x) public returns (uint) {
                   uint[] memory toLoop;
                   if(x == 10) {
                      toLoop = new uint[](0);
                   } else {
                      toLoop = new uint[](x);
                   }
                   uint sum = 0;
                   for(uint i = 0; i < toLoop.length; i++) {
                      sum += toLoop[i];
                   }
                   return sum;
                }
            }
        """.trimIndent()
        this.assertAnalysisSucceeds(solc, contract, optimize)
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testConstantSizeArray(solc: String, optimize: Boolean) {
        val l = listOf(
            "bytes[]",
            "uint[]",
            "uint"
        )
        for (ty in l) {
            val contract = """
                pragma experimental ABIEncoderV2;

                contract Test {
                    function test() public returns ($ty[3] memory) {
                        $ty[3] memory yolo;
                        return yolo;
                    }
                }
            """.trimIndent()
            this.assertAnalysisSucceeds(solc, contract, optimize)
        }
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testBytesWrite(solc: String, optimize: Boolean) {
        val contract = """
            contract Test {
                function test(uint256 n) public pure returns (string memory) {
                    if (n == 0) {
                        return "0";
                    } else {
                        uint256 len = 0;
                        for (uint256 temp = n; temp > 0; temp /= 10) {
                            len++;
                        }
                        bytes memory str = new bytes(len);
                        for (uint256 i = len; i > 0; i--) {
                            str[i - 1] = bytes1(uint8(48 + (n % 10)));
                            n /= 10;
                        }
                        return string(str);
                    }
                }
            }
        """.trimIndent()
        this.assertAnalysisSucceeds(solc, contract, optimize)
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    open fun testTryCatch(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(solc, this.loadResourceFileOrCrash("analysis/TryCatch.sol"), optimize)
    }

    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testConstantSizedBytes(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            solc, """
                bytes memory x = new bytes(4);
                return x.length;
        """.trimIndent().wrapInTrivialContract("uint"), optimize
        );
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testMultipleStringReads(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(solc, optimize) {
            """contract Test {
	    uint256 t;
    mapping(address => uint256) b;
    mapping(address => mapping(address => uint256)) a;

    string public name;
    string public test;
    uint256 public decimals;
}
"""
        }
    }

    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testConstantSizedBytesWrite(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            solc, """
                        uint256 CODE_MAX_LENGTH = 82;
        bytes memory reversed = new bytes(CODE_MAX_LENGTH);        // Encode given error code to ascii
        uint256 i;
        for (i = 0; code != 0; i++) {
            uint256 remainder = code % 10;
            code = code / 10;
            reversed[i] = bytes1(uint8(48 + remainder));
        }        // Store identifier: "BAL#"
        reversed[i++] = bytes1(uint8(35)); // #
        reversed[i++] = bytes1(uint8(76)); // L
        reversed[i++] = bytes1(uint8(65)); // A
        reversed[i] = bytes1(uint8(66));   // B        // Reverse the bytes array
        return i + reversed.length;
        """.trimIndent().wrapInTrivialContract("uint", "code"), optimize
        );
    }

    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testComplexStructArgs(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            contract = this.loadResourceFileOrCrash("analysis/ComplexStruct.sol"),
            solc = solc,
            optimize = optimize
        )
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testInitReorderBasic(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            solc,
            """
                       contract Test {
                       struct Foo {
                       	uint a;
                       	uint b;
                       	uint c;
                       	uint d;
                       }
                       	Foo fooInStorage;
                       	function test() public {
                       		Foo memory foo = fooInStorage;
                       		foo.c = 100;
                       		foo.b = 120;
                       	}
                       }
        """.trimIndent(), optimize
        )
    }

    @ParameterizedTest
    @ScopedVersions
    @WithOptimizedFlag
    fun testInitReorderJump(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            solc, """
                       pragma experimental ABIEncoderV2;
                       contract Test {
                       struct Foo {
                       	uint a;
                       	uint b;
                       	uint c;
                       }


                       	Foo fooInStorage;

                       	function test1(Foo memory foo) public {
                       		foo.b = 100;
                       	}

                       	function test() public {
                       		Foo memory foo = fooInStorage;
                       		test1(foo);
                       	}
                       }

        """.trimIndent(), optimize
        )
    }

    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testInducedPointerArithmetic(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            contract = """
            contract Test {
            	function test(uint[] memory hilarious, uint a) public returns (uint) {
            		if(hilarious[a] != 0) {
            			uint b = a + 5;
            			hilarious[b] = 22;
            		}
            	}
            }
        """.trimIndent(), solc = solc, optimize = optimize
        )
    }

    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testInducedIndexInLoop(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            contract = """
            interface Factory {
                function getPairValue(address a) external returns (uint);
            }

            contract Test {
                function test(address[] memory path, address tgt) public returns (uint) {
                    uint accum = 0;
                    for(uint i = 0; i < path.length - 1; i++) {
                        accum += Factory(path[i]).getPairValue(path[i + 1]);
                        accum += Factory(path[i]).getPairValue(i < path.length - 2 ? path[i + 2] : tgt);
                    }
                    return accum;
                }
            }
        """.trimIndent(), solc = solc, optimize = optimize
        )
    }

    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testStorageToMemoryCopy(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            solc = solc,
            optimize = optimize,
            contract = this.loadResourceFileOrCrash("analysis/StorageToMemory.sol")
        )
    }

    // todo: use the matrix
    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testStorageToMemoryCopyComplex(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            solc = solc,
            optimize = optimize,
            contract = this.loadResourceFileOrCrash("analysis/StorageToMemoryComplexNesting.sol")
        )
    }

    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testCopyFromCall(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            solc = solc,
            optimize = optimize,
            contract = this.loadResourceFileOrCrash("analysis/ReturnArraysInStruct.sol")
        )

    }

    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testCopyAndCallInLoop(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            solc = solc,
            optimize = optimize,
            contract = this.loadResourceFileOrCrash("analysis/CallAndCopyInLoop.sol")
        )
    }

    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testArrayLengthEquality(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            solc = solc, optimize = optimize, contract = this.loadResourceFileOrCrash("analysis/ManualLengthCheck.sol")
        )
    }

    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testStaticArrayCopy(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            solc = solc,
            optimize = optimize,
            contract = this.loadResourceFileOrCrash("analysis/StaticCopy.sol")
        )
    }

    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testUselessBytesAlloc(solc: String, optimize: Boolean) {
        this.assertAnalysisSucceeds(
            solc = solc,
            optimize = optimize,
            contract = """
                contract MyLittleContract {
                    function yeet() public returns (uint) { return 4; }
                }

                contract Test {
                   function test() public returns (uint) {
                       bytes memory unused = type(MyLittleContract).creationCode;
                       return 4;
                   }
                }
            """.trimIndent()
        )
    }

    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testManualCopyToFieldsSuccess(solc: String, optimize: Boolean) {
        /*
          Size, offset, length
         */
        val config = listOf(
            Triple(1, 0, 32),
            Triple(2, 0, 32),
            Triple(2, 32, 32),
            Triple(2, 0, 64)
        )
        for ((sz, offset, len) in config) {
            this.assertAnalysisSucceeds(
                solc = solc, optimize = optimize, contract = getManualCopyContract(sz, offset, len)
            )
        }
    }

    @ParameterizedTest
    @WithOptimizedFlag
    @ScopedVersions
    fun testManualCopyToFieldsFailure(solc: String, optimize: Boolean) {
        val config = listOf(
            Triple(1, 1, 31), // misaligned output
            Triple(1, 0, 31), // misaligned (size)
            Triple(1, 0, 64), // too big
            Triple(2, 32, 64) // too big (redux)
        )
        for ((sz, offset, len) in config) {
            this.assertAnalysisFails(
                solc = solc,
                optimize = optimize,
                contract = getManualCopyContract(sz, offset, len)
            )
        }
    }

    private fun getManualCopyContract(sz: Int, offset: Int, len: Int) = """
                        contract Test {
                            function test() external returns (uint) {
                                address(msg.sender).call(abi.encodeWithSignature("yolo()"));
                                checkReturnCode();
                                return 0;
                            }


                            function checkReturnCode() private pure {
                                bool success;
                                uint256[$sz] memory result;
                                assembly {
                                    switch returndatasize()
                                                             case 0 {
                                            // This is a non-standard ERC-20
                                        success := 1 // set success to true
                                                                 }
                                    case 32 {
                                        // This is a compliant ERC-20
                                        returndatacopy(add(result, $offset), 0, $len)
                                            success := mload(result) // Set `success = returndata` of external call
                                            }
                                    default {
                                        // This is an excessively non-compliant ERC-20, revert.
                                        revert(0, 0)
                                            }
                                }

                                require(success, "ERC20");
                            }
                        }
                    """.trimIndent()


}
