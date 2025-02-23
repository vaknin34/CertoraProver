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

package sbf.inliner

import sbf.disassembler.SbfRegister
import sbf.domains.MemorySummaries
import sbf.support.CannotParseInliningFile
import sbf.support.SolanaError
import sbf.support.readLines
import config.Config
import utils.ArtifactFileUtils

interface InlinerConfig {
    /**
     * Return whether we should inline [fname]
     **/
    fun getInlineSpec(fname: String): InlineSpec
}

sealed class InlineSpec {
    /** Perform inlining */
    object DoInline : InlineSpec()

    /** Do not inline, assume function has arity [arity] */
    data class NeverInline(val arity: Int) : InlineSpec()
}

data class InlinerConfigFromFile(val inlinedFunctions: List<Regex>, val neverInlinedFunctions: List<Pair<Regex, Int>>): InlinerConfig {

    override fun getInlineSpec(fname: String): InlineSpec {
        return if (inlinedFunctions.any { it.containsMatchIn(fname) }) {
            InlineSpec.DoInline
        } else {
            neverInlinedFunctions.firstOrNull { (regex, _)  ->
                regex.containsMatchIn(fname)
            }?.let {
                InlineSpec.NeverInline(it.second)
            } ?: InlineSpec.DoInline
        }
    }

    companion object {
        private val grammar =
            """
   FILE ::= LINE*
   LINE ::= QUALIFIER FUNCTION_NAME
   N \in [0, 5]
   QUALIFIER ::=  #[inline(never, N) | #[inline(never)] | #[inline]
   FUNCTION_NAME ::= a regex
           """.trimIndent()

        @Suppress("ForbiddenMethodCall")
        private val neverInlineWithArity = """\s*\#\[inline\(never\s*,\s*([0-5])\s*\)\]\s*(.*)""".toRegex()
        @Suppress("ForbiddenMethodCall")
        private val neverInlineRegex = """\s*\#\[inline\(never\)\]\s*(.*)""".toRegex()
        @Suppress("ForbiddenMethodCall")
        private val inlineRegex = """\s*\#\[inline\]\s*(.*)""".toRegex()

        fun isInlineAnnotation(input: String): Boolean {
            return inlineRegex.matches(input) || neverInlineRegex.matches(input) || neverInlineWithArity.matches(input)
        }

        @Suppress("ForbiddenMethodCall")
        private fun looksLikeSummaryAnnotation(input:String): Boolean {
            return MemorySummaries.isSummaryAnnotation(input) ||
                  (input.startsWith("^") && input.endsWith("$"))
        }

        /**
         *  Read a specification file that follows this pretty simple grammar `FILE` defined in [grammar].
         *  Extract the functions that should never be inlined and those that should be always inlined.
         *  Since `FUNCTION_NAME` is a regex, a function can be marked as never inlined as well as inline.
         *  In this case, the function will be inlined. Thus, the qualifier `#[inline]` has higher priority in
         *  case of conflict. This is useful because we can have a regex that never inline many functions
         *  (e.g., all functions in an external library) but then inline few of them.
         */
        @Suppress("ForbiddenMethodCall")
        fun readSpecFile(filename: String): InlinerConfig {
            val filenameFromSourcesDir = ArtifactFileUtils.wrapPathWith(filename, Config.getSourcesSubdirInInternal())
            val lines = readLines(filenameFromSourcesDir) ?: readLines(filename) ?: throw SolanaError("cannot find $filenameFromSourcesDir or $filename")
            val inlineFunctions = mutableListOf<Regex> ()
            val neverInlineFunctions = mutableListOf<Pair<Regex, Int>>()
            for (line in lines) {
                if (line == "" || line.startsWith(";")) { // ; for comments
                    continue
                }

                var matched = false
                inlineRegex.find(line).let {
                    if (it != null) {
                        val matches = it.groupValues
                        inlineFunctions.add(matches[1].toRegex())
                        matched = true
                    }
                }

                if (!matched) {
                    neverInlineRegex.find(line).let {
                        if (it != null) {
                            val matches = it.groupValues
                            neverInlineFunctions.add(matches[1].toRegex() to SbfRegister.maxArgument.value.toInt())
                            matched = true
                        }
                    }
                }

                if (!matched) {
                    neverInlineWithArity.find(line).let {
                        if (it != null) {
                            val matches = it.groupValues
                            val arity = matches[1].toInt()
                            neverInlineFunctions.add(matches[2].toRegex() to arity)
                            matched = true
                        }
                    }

                }

                if (!matched) {
                    if (!looksLikeSummaryAnnotation(line)) {
                        throw CannotParseInliningFile(line, filename, grammar)
                    }
                }
            }
            return InlinerConfigFromFile(inlineFunctions, neverInlineFunctions)
        }
    }
}

object EmptyInlinerConfig : InlinerConfig {
    override fun getInlineSpec(fname: String): InlineSpec = InlineSpec.DoInline
}
