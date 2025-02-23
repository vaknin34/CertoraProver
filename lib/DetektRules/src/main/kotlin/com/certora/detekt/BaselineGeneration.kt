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

package com.certora.detekt

import io.gitlab.arturbosch.detekt.api.*
import java.io.StringWriter
import javax.xml.parsers.*
import javax.xml.transform.*
import javax.xml.transform.dom.*
import javax.xml.transform.stream.*

/**
  Custom reporter to generate Detekt baseline files.  We need this because the Detekt Kotlin compiler plugin does not
  natively support baseline generation yet.
*/
@OptIn(UnstableApi::class)
class BaselineGeneration : OutputReport() {

    override val ending = "xml"
    override val id = "baseline"

    override fun render(detektion: Detektion): String? {
        val doc = DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument()
        val smells = doc.createElement("SmellBaseline")
        val issues = doc.createElement("CurrentIssues").also { smells.appendChild(it) }

        val ids = detektion.findings.flatMap { (_, findings) ->
            findings.map { "${it.id}:${it.signature}" }
        }.toSortedSet()

        ids.forEach { id ->
            doc.createElement("ID").also {
                it.appendChild(doc.createTextNode(id))
                issues.appendChild(it)
            }
        }

        val result = StringWriter()

        TransformerFactory.newInstance().newTransformer().apply {
            setOutputProperty(OutputKeys.INDENT, "yes")
            transform(DOMSource(smells), StreamResult(result))
        }

        return result.toString()
    }
}
