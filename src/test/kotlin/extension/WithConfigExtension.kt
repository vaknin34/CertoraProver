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

package extension

import annotations.PollutesGlobalState
import org.junit.jupiter.api.extension.AfterAllCallback
import org.junit.jupiter.api.extension.BeforeAllCallback
import org.junit.jupiter.api.extension.ExtensionContext
import java.io.Serializable
import java.lang.reflect.Modifier

/**
 * specify a static object `certoraConfig` with the desired settings that will be applied only for the tests
 * defined in the class that has [WithConfigExtension] as an annotation
 */
class WithConfigExtension : BeforeAllCallback, AfterAllCallback {
    private val saved = mutableListOf<DependentPair<*>>()

    @PollutesGlobalState
    override fun beforeAll(context: ExtensionContext?) {
        check(context != null)
        val m = context.requiredTestClass.getMethod("certoraConfig")?.takeIf {
            (it.modifiers and Modifier.STATIC) != 0
        } ?: throw UnsupportedOperationException("Asked for Certora configuration, but no static certoraConfig method found")
        val l = m.invoke(null).let {
            it as? Collection<*>
        } ?: throw RuntimeException("certoraConfig returned an illegal type")
        for(t in l) {
            val down = t as? DependentPair<*> ?: throw IllegalArgumentException("Found non-dependent pair object in list")
            handleConfig(down)
        }
    }

    @PollutesGlobalState
    private fun <T: Serializable> handleConfig(configPair: DependentPair<T>) {
        saved.add(
            configPair.opt setTo configPair.opt.get()
        )
        setConfig(configPair)
    }

    @PollutesGlobalState
    private fun <T: Serializable> setConfig(configPair: DependentPair<T>) {
        configPair.opt.set(configPair.desired)
    }

    @PollutesGlobalState
    override fun afterAll(context: ExtensionContext?) {
        for(t in saved) {
            setConfig(t)
        }
    }
}
