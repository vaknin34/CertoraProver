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

package report

import config.Config
import log.Logger
import log.LoggerTypes
import java.awt.Image
import java.awt.SystemTray
import java.awt.Toolkit
import java.awt.TrayIcon

object Notifications {

    private val logger = Logger(LoggerTypes.COMMON)

    lateinit var tray : SystemTray
    lateinit var image : Image
    lateinit var trayIcon : TrayIcon

    init {

        if (SystemTray.isSupported() && System.getenv("CERTORA_DISABLE_NOTIFICATION") == null) {
            tray = SystemTray.getSystemTray()
            image = Toolkit.getDefaultToolkit().createImage(ClassLoader.getSystemResource("CertoraLogo16.png"))
            trayIcon= TrayIcon(image, "Certora")

            trayIcon.isImageAutoSize = true
            trayIcon.toolTip = "Certora Prover notification"
            tray.add(trayIcon)
            trayIcon.addActionListener { e ->
                logger.debug{"Caught $e"}
                HTMLReporter.open()
            }
        }
    }

    fun showNotification(title : String, msg : String, success : FinalResult) {
        if (!Config.DisablePopup.get() && SystemTray.isSupported() &&
            System.getenv("CERTORA_DISABLE_NOTIFICATION") == null && Config.isRunningInLocalEnv()) {
            trayIcon.displayMessage(title,msg,
                    when (success) {
                        FinalResult.NONE -> throw AssertionError("Invalid result NONE")
                        FinalResult.SUCCESS -> TrayIcon.MessageType.INFO
                        FinalResult.FAIL -> TrayIcon.MessageType.WARNING
                        FinalResult.ERROR -> TrayIcon.MessageType.ERROR
                        FinalResult.DIAGNOSTIC_ERROR -> TrayIcon.MessageType.WARNING
                    }
            )

        }
    }
}
enum class FinalResult {
    NONE, SUCCESS, FAIL, ERROR, DIAGNOSTIC_ERROR;

    fun getExitCode(): Int {
        return when (this) {
            NONE -> throw AssertionError("Invalid result NONE")
            SUCCESS -> 0
            FAIL -> 100
            ERROR -> 1
            DIAGNOSTIC_ERROR -> 10
        }
    }
}
