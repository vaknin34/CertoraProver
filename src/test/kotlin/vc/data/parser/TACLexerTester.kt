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

package vc.data.parser

import kotlinx.serialization.Serializable
import kotlinx.serialization.decodeFromString
import kotlinx.serialization.encodeToString
import kotlinx.serialization.json.Json
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import tac.MetaKey
import tac.TacLexer
import tac.TacLexer.S_Parse_Expression
import tac.sym.EOF
import utils.KSerializable
import vc.data.TACCmd

internal class TACLexerTester {

    fun primitiveTACJson(s: String) = "JSON{$s}"
    inline fun <reified T> toTACJson(t: T) = "JSON${inlinedTACJson.encodeToString<T>(t)}"
    fun deserializeStringLiteral(ser: String) : String? {
        val csf = java_cup.runtime.ComplexSymbolFactory()
        val lex = TacLexer(csf, ser.reader())
        lex.yybegin(S_Parse_Expression)
        var token = lex.next_token()?.value as? String
        assert(lex.next_token()?.sym == EOF)
        return token
    }

    fun deserializeJson(ser: String) : String? =
        deserializeStringLiteral(ser)?.let{Json.decodeFromString<String>(it)}

    @Test
    fun simpleStringLiteral() {
        val noQuoteInside = "simple string literal"
        val asStringLiteral = noQuoteInside.Quoted()
        Assertions.assertEquals(noQuoteInside,deserializeStringLiteral(asStringLiteral))
    }

    @KSerializable
    data class ContainsString(val s: String)

    fun roundTripWithJson(s: String) {
        val obj = ContainsString(s)
        val serNoQuote = toTACJson(obj)
        Assertions.assertEquals(obj, Json.decodeFromString<ContainsString>(deserializeStringLiteral(serNoQuote)!!))
    }


    @Test
    fun simpleStringInJson() {
        roundTripWithJson("simple string inside json")
    }

    @Test
    fun stringWithEvenQuotes() {
        roundTripWithJson("simple string \"with quotes\"")
    }

    @Test
    fun stringWithOddQuotes() {
        roundTripWithJson("simple string \"with single quotation sign")
    }

    @Test
    fun stringWithEscape() {
        roundTripWithJson("simple string \b\t\rwith escaped chars")
    }

    @Test
    fun stringWithBraces() {
        roundTripWithJson("simple string }with braces")
    }

    @Test
    fun testLexerWithEscapedChars() {
        val annot =
            TACCmd.Simple.AnnotationCmd.Annotation(MetaKey<String>("the string have quotes") ,"string with \"quotes\"")
        val annotationSer = toTACJson(annot)
        val de = deserializeStringLiteral(annotationSer)
        Assertions.assertEquals(annot, inlinedTACJson.decodeFromString<TACCmd.Simple.AnnotationCmd.Annotation<String>>(de as String))

    }
}
