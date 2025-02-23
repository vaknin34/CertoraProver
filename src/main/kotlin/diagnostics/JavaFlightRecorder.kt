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

package diagnostics

import config.*
import datastructures.stdcollections.*
import jdk.jfr.*
import loaders.WithResourceFile
import log.*
import utils.*
import java.io.InputStreamReader
import java.nio.file.Path

object JavaFlightRecorder : WithResourceFile {
    /**
        Starts the Java Flight Recorder (JFR) profiling tool.  This will record a profile of the program's execution,
        including stack traces, CPU usage, Heap size, and other information.  The profile will be saved to a file named
        "profile.jfr" in the Reports directory.

        JFR is enabled by default in production mode, but can be disabled by setting the `jfr` configuration option to
        `false`.  It is disabled by default in development mode, but can be enabled by setting the `jfr` configuration.

        The stack trace sample interval defaults to 1 second, which is good for a long run (which is typically what we
        need profile data for), and has very little overhead.  A typical trace for a long run will be on the low tens of
        MB.  For more detailed profiling, you you can set the `stackInterval` config to a lower value (it is in
        milliseconds).  This may be necessary if you are trying to profile a smaller scenario.

        The resulting file can be read using most Java profiler tools, including VisualVM, Java Mission Control,
        YourKit, JProfiler, etc.
     */
    fun start() {
        if (Config.JFR.get()) {
            val recordingFilename = "profile.jfr"
            ArtifactManagerFactory().registerArtifact(recordingFilename)
            ArtifactManagerFactory().useArtifact(recordingFilename) { recordingPath ->
                // Base settings are configured via this resource file
                val settings = Configuration.create(
                    InputStreamReader(loadResourceFileAsStream("prover_profile_default.jfc"))
                ).getSettings()

                // Override the sampling rate if configured
                val interval = Config.JFRStackSampleInterval.get().let { "$it ms" }
                settings["jdk.ExecutionSample#period"] = interval
                settings["jdk.NativeMethodSample#period"] = interval

                Recording(settings).apply {
                    setDestination(Path.of(recordingPath))
                    setToDisk(true)
                    setDumpOnExit(true)
                    start()
                }
            }
        }
    }
}
