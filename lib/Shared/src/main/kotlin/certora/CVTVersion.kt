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

package certora

import kotlinx.serialization.Serializable
import java.util.*

/*
			p.setProperty("certora.version", versionString)
			p.setProperty("git.branch.name", versionDetails.branchName)
			p.setProperty("git.hash", versionDetails.gitHash)
			p.setProperty("git.hash.full", versionDetails.gitHashFull)
			p.setProperty("git.last.tag", versionDetails.lastTag)
			p.setProperty("git.is.clean", if(versionDetails.isCleanTag) { "true" } else { "false" })
 */
@Serializable
data class CVTVersion(val certoraVersionString: String,
                      val gitBranchName: String,
                      val gitHashShort: String,
                      val gitHashFull: String,
                      val gitLastTag: String,
                      val gitIsClean: Boolean
) {
    companion object {
        /**
         * Get CVT version info for the current build.
         */
        fun getCurrentCVTVersion(): CVTVersion? {
            return this::class.java.classLoader.getResourceAsStream("certora-version.properties")?.use {
                try {
                    val p = Properties()
                    p.load(it)
                    CVTVersion(
                        certoraVersionString = p.getProperty("certora.version"),
                        gitBranchName = p.getProperty("git.branch.name"),
                        gitHashShort = p.getProperty("git.hash"),
                        gitHashFull = p.getProperty("git.hash.full"),
                        gitLastTag = p.getProperty("git.last.tag"),
                        gitIsClean = p.getProperty("git.is.clean") == "true"
                    )
                } catch (_: Throwable) {
                    null
                }
            }
        }


        fun getInternalVersionString(): String {
            return this::class.java.classLoader.getResourceAsStream("certora-version.properties")?.use {
                try {
                    val p = Properties()
                    p.load(it)
                    p.getProperty("certora.version")
                } catch (_: Throwable) {
                    "dev"
                }
            } ?: "dev"
        }
    }
}
