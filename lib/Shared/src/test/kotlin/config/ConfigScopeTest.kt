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

package config

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions.*

class ConfigScopeTest {

    @Test
    fun basicTest() {
        // make sure that ShowHelp is set as we expect
        assertNotNull(Config.ShowHelp.default)
        assertFalse(Config.ShowHelp.default!!)
        assertTrue(Config.ShowHelp.isDefault())
        assertFalse(Config.ShowHelp.get())
        // now do the actual test
        ConfigScope(Config.ShowHelp, true).use {
            assertFalse(Config.ShowHelp.isDefault())
            assertTrue(Config.ShowHelp.get())
        }
        assertTrue(Config.ShowHelp.isDefault())
        assertFalse(Config.ShowHelp.get())
    }
}
