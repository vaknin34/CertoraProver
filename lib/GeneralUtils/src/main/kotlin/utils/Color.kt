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

package utils

/**
 * Printing colors in the terminal for easier print debugging. To color both the background and the forground use for
 * example:
 *
 *    "Sample Text".redBg().bYellow()
 *
 * `bYellow` stands for bright-yellow.
 *
 * Uses ansi escape codes. See [https://www.lihaoyi.com/post/BuildyourownCommandLinewithANSIescapecodes.html].
 */
@Suppress("unused")
enum class Color {
    // the order of colors corresponds to ANSI escape codes.
    BLACK, RED, GREEN, YELLOW, BLUE, MAGENTA, CYAN, WHITE;

    fun toCode(bright : Boolean, background: Boolean): String {
        val bgStr = if (background) "4" else "3"
        val brStr = if (bright) ";1" else ""
        return "\u001b[$bgStr${this.ordinal}${brStr}m"
    }

    fun color(text: Any?, bright: Boolean, background: Boolean) =
        "${toCode(bright, background)}$text${resetColor}"

    companion object {
        private const val resetColor = "\u001B[0m"

        private fun code256(code: Int) = "\u001b[38;5;${code}m"

        private fun Any?.color(c : Color) = c.color(this, bright = false, background = false)
        private fun Any?.brightColor(c : Color) = c.color(this, bright = true, background = false)
        private fun Any?.bgColor(c : Color) = c.color(this, bright = false, background = true)
        private fun Any?.brightBgColor(c : Color) = c.color(this, bright = true, background = true)

        val Any?.black get() = color(BLACK)
        val Any?.red get() = color(RED)
        val Any?.green get() = color(GREEN)
        val Any?.yellow get() = color(YELLOW)
        val Any?.blue get() = color(BLUE)
        val Any?.magenta get() = color(MAGENTA)
        val Any?.cyan get() = color(CYAN)
        val Any?.white get() = color(WHITE)

        val Any?.bBlack get() = brightColor(BLACK)
        val Any?.bRed get() = brightColor(RED)
        val Any?.bGreen get() = brightColor(GREEN)
        val Any?.bYellow get() = brightColor(YELLOW)
        val Any?.bBlue get() = brightColor(BLUE)
        val Any?.bMagenta get() = brightColor(MAGENTA)
        val Any?.bCyan get() = brightColor(CYAN)
        val Any?.bWhite get() = brightColor(WHITE)

        val Any?.blackBg get() = bgColor(BLACK)
        val Any?.redBg get() = bgColor(RED)
        val Any?.greenBg get() = bgColor(GREEN)
        val Any?.yellowBg get() = bgColor(YELLOW)
        val Any?.blueBg get() = bgColor(BLUE)
        val Any?.magentaBg get() = bgColor(MAGENTA)
        val Any?.cyanBg get() = bgColor(CYAN)
        val Any?.whiteBg get() = bgColor(WHITE)

        val Any?.bBlackBg get() = brightBgColor(BLACK)
        val Any?.bRedBg get() = brightBgColor(RED)
        val Any?.bGreenBg get() = brightBgColor(GREEN)
        val Any?.bYellowBg get() = brightBgColor(YELLOW)
        val Any?.bBlueBg get() = brightBgColor(BLUE)
        val Any?.bMagentaBg get() = brightBgColor(MAGENTA)
        val Any?.bCyanBg get() = brightBgColor(CYAN)
        val Any?.bWhiteBg get() = brightBgColor(WHITE)
    }
}
