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

package log

import config.Config
import config.ConfigType
import utils.*
import java.io.File


/**
 * An interface representing the location of an artifact. It defines properties and functions to handle artifact paths.
 */
sealed interface ArtifactLocation {

    /**
     * The File object representing the location of the artifact.
     */
    val path: File

    /**
     * Determines whether the artifact is relative to the main output directory.
     */
    fun isRelativeToMainOutputDir(): Boolean

    /**
     * Resolves the actual path of the artifact based on its relative or absolute nature and the main output directory.
     * @param mainOutputDirPath The path of the main output directory.
     * @return The resolved File object representing the actual path of the artifact.
     * @throws IllegalStateException If artifacts are not enabled in the configuration.
     */
    fun getResolvedPath(mainOutputDirPath: String): File {
        check(ArtifactManagerFactory.isEnabled()) {
            "Cannot resolve the artifact location $this when artifacts are not enabled" }
        val resolvedPath: File = when {
            isRelativeToMainOutputDir() -> {
                File(mainOutputDirPath).resolve(this.path)
            }

            this.path.isAbsolute -> {
                this.path
            }

            else -> {
                StaticArtifactLocation.CWD.path.resolve(this.path)
            }
        }
        ArtifactFileUtils.createFolderIfNotExists(resolvedPath.path)
        return resolvedPath
    }
}

/**
 * An interface representing the location of a subdirectory artifact. It extends [ArtifactLocation] and provides
 * properties and functions to handle subdirectory paths.
 */
sealed interface SubdirArtifactLocation : ArtifactLocation {

    /**
     * The static parent location of the subdirectory artifact.
     */
    val staticParent: StaticArtifactLocation.StaticArtifactLocationFromConfig

    /**
     * The File object representing the subdirectory path.
     */
    val subdir: File

    /**
     * The resolved File object representing the actual path of the subdirectory artifact,
     * based on the static parent and the subdirectory path.
     */
    override val path: File
        get() = staticParent.path.resolve(subdir)

    /**
     * Determines whether the subdirectory artifact is relative to the main output directory,
     * delegating to the static parent's implementation.
     */
    override fun isRelativeToMainOutputDir(): Boolean = staticParent.isRelativeToMainOutputDir()

}

/**
 * An interface representing a static artifact location. It extends [ArtifactLocation] and serves as a marker interface
 * for different types of static artifact locations.
 */
sealed interface StaticArtifactLocation : ArtifactLocation {

    /**
     * An interface representing a static artifact location defined by a configuration flag. It extends [StaticArtifactLocation]
     * and provides properties and functions to handle configuration-based artifact paths.
     */
    sealed interface StaticArtifactLocationFromConfig : StaticArtifactLocation {

        /**
         * The configuration value specifying the path of the static artifact.
         */
        val configLocation: ConfigType.StringCmdLine

        /**
         * Determines whether the static artifact is relative to the main output directory, based on the configuration value.
         */
        override fun isRelativeToMainOutputDir(): Boolean = configLocation.isDefault()

        /**
         * The File object representing the path of the static artifact, obtained from the configuration value.
         */
        override val path: File
            get() = File(configLocation.get())
    }

    // Static artifact locations defined in the configuration:

    object Reports : StaticArtifactLocationFromConfig {
        override val configLocation: ConfigType.StringCmdLine
            get() = Config.ReportsDir
    }

    object Outputs : StaticArtifactLocationFromConfig {
        override val configLocation: ConfigType.StringCmdLine
            get() = Config.OutputsDir

    }

    object Debugs : StaticArtifactLocationFromConfig {
        override val configLocation: ConfigType.StringCmdLine
            get() = Config.DebugOutputsFolder

    }

    object Formulas : StaticArtifactLocationFromConfig {
        override val configLocation: ConfigType.StringCmdLine
            get() = Config.FormulasFolder
    }

    object Input : StaticArtifactLocationFromConfig {
        override val configLocation: ConfigType.StringCmdLine
            get() = Config.InputBackupFolder
    }

    // Other static artifact locations not defined by the configuration:
    /**
     * A static artifact location representing the current working directory.
     * The path is obtained from the system property "user.dir".
     */
    object CWD : StaticArtifactLocation {
        override fun isRelativeToMainOutputDir(): Boolean = false
        override val path: File
            get() = workingDirectory().toFile()

        override fun getResolvedPath(mainOutputDirPath: String): File = this.path
    }


    /**
     * An [ArtifactLocation] that is a subdirectory ([SubdirArtifactLocation]) set using a config flag ([StaticArtifactLocationFromConfig]).
     * It is assumed that [subdir] is relative to [staticParent].
     */
    sealed interface StaticSubdirArtifactLocationFromConfig : StaticArtifactLocationFromConfig, SubdirArtifactLocation {
        /**
         * The subdirectory set via the [configLocation].
         */
        override val subdir: File
            get() = super<StaticArtifactLocationFromConfig>.path

        /**
         *  The [subdir] concatenated to the [staticParent]'s path
         */
        override val path: File
            get() = super<SubdirArtifactLocation>.path

        override fun isRelativeToMainOutputDir(): Boolean = super<SubdirArtifactLocation>.isRelativeToMainOutputDir()
    }

    // Static subdirectory artifact locations defined in the configuration:

    object TreeViewReports : StaticSubdirArtifactLocationFromConfig {
        override val staticParent: StaticArtifactLocationFromConfig
            get() = Reports
        override val configLocation: ConfigType.StringCmdLine
            get() = Config.TreeViewReportsSubdir
    }

    object VerifierResults : StaticSubdirArtifactLocationFromConfig {
        override val staticParent: StaticArtifactLocationFromConfig
            get() = Reports

        override val configLocation: ConfigType.StringCmdLine
            get() = Config.VerifierResultsReportsSubdir
    }
}

/**
 * A data class representing a dynamic artifact location with both a static parent and a subdirectory.
 */
data class DynamicArtifactLocation(
    override val staticParent: StaticArtifactLocation.StaticArtifactLocationFromConfig,
    override val subdir: File
) : SubdirArtifactLocation
