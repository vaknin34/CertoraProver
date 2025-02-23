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

package spec.errors

import datastructures.stdcollections.mapValues
import spec.cvlast.typechecker.*
import kotlin.reflect.KClass

/** Print all error types to standard out, formatted as markdown */
@Suppress("UnusedPrivateMember")
private fun main() {
    println(errorListText())
}

/**
 * @return the example CVL for [errorClass] and the expected error message (from the [CVLErrorExample] annotation),
 * formatted as markdown
 */
private fun errorExampleText(errorClass : KClass<*>) : String {
    val annotation   = CVLErrorExample.instances[errorClass]?.firstOrNull { it.exampleMessage != "" } ?: return "*No example provided*"
    val errorExample = ErrorExample("Example", annotation.exampleCVLWithRange)

    return """
        Example:
        ```{code-block} cvl
        :emphasize-lines: ${errorExample.range.start.line}-${errorExample.range.end.line}

${errorExample.text.trimIndent().prependIndent("        ")}
        ```
        ```
        ${errorExample.range}: ${annotation.exampleMessage}
        ```
        """.trimIndent()
}

/**
 * @return the list of all [CVLErrorType]s, formatted as markdown
 */
private fun errorListText() : String {
    val sortedErrorsByCategory = CVLErrorType.instances.entries
        .groupBy { (_, errorType) -> errorType.category }
        .mapValues { (_, entries) -> entries.sortedBy { (errorClass, _) -> errorClass.simpleName } }

    return """
% DO NOT EDIT; this file is automatically generated
% To change the documentation or examples, modify the [CVLErrorExample] annotation on the corresponding class.
% To regenerate, run the `main` method in `ErrorDocGenerator.kt`

List of CVL errors
==================

```{contents}
```

${
        CVLErrorCategory.values().joinToString("") { category ->
"""
## ${category.description} errors

${sortedErrorsByCategory[category].orEmpty().joinToString("") { (errorClass, errorType) -> """
### `${errorClass.simpleName}`

>
${errorType.description.trimIndent().prependIndent("> ")}
>
${errorExampleText(errorClass).prependIndent("> ")}

"""}}
"""}}
"""
}
