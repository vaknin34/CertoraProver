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

import java.io.File

object DevMode {
    /**
     * CERTORA_DEV_MODE is an environment variable that controls the level of logging by CVT.
     * Devs get more verbose output of exceptions.
     */
    fun isDevMode() = System.getenv("CERTORA_DEV_MODE") != null

    /**
     * Check if we run CVT locally or not.
     * This is done by checking if $CERTORA exists and contains emv.jar.
     * CERTORA environment variable is storing relevant CVT artifacts.
     */
    fun isLocalDevRun() = System.getenv("CERTORA")?.let {
        File(it + File.separator + "emv.jar").exists()
    } ?: false
}
