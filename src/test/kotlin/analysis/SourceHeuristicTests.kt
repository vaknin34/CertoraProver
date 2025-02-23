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

import analysis.icfg.CallGraphBuilder
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

class SourceHeuristicTests {

    private fun compareExpectCorrect(expected: String, source: String) =
        Assertions.assertEquals(
            expected,
            CallGraphBuilder.sourceStringToPotentialMethodName(source)
        )

    // A test that's failing, but we currently expect it to be the case
    private fun compareExpectWrong(expectedRight: String, expectedWrong: String?, source: String) {
        val result = CallGraphBuilder.sourceStringToPotentialMethodName(source)
        // assert that what we really want is not happening
        Assertions.assertNotEquals(
            expectedRight,
            result
        )

        // assert what we expect to be really happening
        Assertions.assertEquals(
            expectedWrong,
            result
        )
    }

    @Test
    fun sourceHeuristicTest1() {
        compareExpectCorrect(
            "exists",
            "tbtcDepositToken.exists(_tdtId)"
        )

        compareExpectCorrect(
            "transferFrom",
            "tbtcDepositToken.transferFrom(msg.sender, address(this), _tdtId)"
        )

        compareExpectCorrect(
            "balanceOf",
            "tbtcToken.balanceOf(address(_tdtId))"
        )

        compareExpectCorrect(
            "mint",
            "tbtcToken.mint(msg.sender, depositValue.sub(signerFee))"
        )

        compareExpectCorrect(
            "mint",
            "tbtcToken.mint(address(_tdtId), signerFee)"
        )

        compareExpectCorrect(
            "mint",
            "tbtcToken.mint(msg.sender, depositValue)"
        )

        compareExpectCorrect(
            "totalSupply",
            "tbtcToken.totalSupply()"
        )

        compareExpectCorrect(
            "requireIssuanceActive",
            "systemStatus().requireIssuanceActive()"
        )

        // legacy source markup should not hurt - otherwise we should make sure to remove it
        compareExpectCorrect(
            "burn",
            "synthsETH()/* @certora Synth.burn(address,uint256) */.burn(account, synthLoan.loanAmount)"
        )

        compareExpectCorrect(
            "_emit",
            "proxy._emit(abi.encode(value), 3, TRANSFER_SIG, bytes32(from), bytes32(to), 0)"
        )

        compareExpectWrong(
            "exchangeEtherForSynths",
            null/*"exchangeEtherForSynths.value"*/,
            "depot().exchangeEtherForSynths.value(totalFees)()"
        )

        compareExpectWrong(
            "recipient",
            null/*"recipieint.call.value"*/,
            "p.recipient.call.value(p.amount)(p.data)"
        )

        compareExpectWrong(
            "f",
            null/*"f.gas"*/,
            "x.f.gas(2).value(20)()"
        )
    }

}