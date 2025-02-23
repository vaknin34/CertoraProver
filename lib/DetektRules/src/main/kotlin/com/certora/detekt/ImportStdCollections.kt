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

import com.certora.detekt.utils.*
import io.gitlab.arturbosch.detekt.api.*
import io.gitlab.arturbosch.detekt.api.internal.RequiresTypeResolution
import org.jetbrains.kotlin.descriptors.*
import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.resolve.*
import org.jetbrains.kotlin.resolve.descriptorUtil.fqNameSafe
import org.jetbrains.kotlin.resolve.scopes.receivers.PackageQualifier

// The signature of `Map<K, V>.forEach`, from kotlin.collections
private const val mapForEachSignature = "forEach@kotlin.collections.Map<out|0:0,0:1>(kotlin.Function1<kotlin.collections.Map.Entry<0:0,0:1>,kotlin.Unit>){0§<kotlin.Any?>;1§<kotlin.Any?>}"

@RequiresTypeResolution
class ImportStdCollections(config: Config) : Rule(config) {

    override val issue = Issue(
        javaClass.simpleName,
        Severity.Performance,
        "Detects uses of stdlib collections functions that have better implementations in datastructures.stdcollections",
        Debt.FIVE_MINS
    )

    override fun visitCallExpression(expression: KtCallExpression) {
        super.visitCallExpression(expression)
        checkCallee(expression.calleeExpression ?: return)
    }

    override fun visitBinaryExpression(expression: KtBinaryExpression) {
        super.visitBinaryExpression(expression)
        checkCallee(expression.operationReference)
    }

    private var stdCollectionsExports: PackageExports? = null

    private fun checkCallee(calleeRef: KtExpression) {
        // Find (and cache) the exports from datastructures.stdcollections.  If we don't have access to this package
        // (because it's not in this module's dependencies), we just don't apply this rule.
        val exports = stdCollectionsExports ?: (
            bindingContext.getPackageExports(calleeRef, "datastructures.stdcollections")
            ?.also { stdCollectionsExports = it }
        ) ?: return

        // Resolve the call target
        calleeRef as? KtReferenceExpression ?: return
        val callee = bindingContext[BindingContext.REFERENCE_TARGET, calleeRef] as? FunctionDescriptor ?: return

        // kotlin.collections.Map has a secret `forEach` member, because it implicitly implements java.util.Map.
        // You won't find this in the Kotlin docs, but it's there.
        // We would rather use our own forEachEntry.
        if (callee.fqNameSafe.asString() == "kotlin.collections.Map.forEach") {
            report(CodeSmell(
                issue,
                Entity.from(calleeRef),
                "${callee.fqNameSafe} has a better alternative: `forEachEntry`, from `datastructures.stdcollections`."
            ))
            return
        }

        // Everything else we're looking for is a top-level function in kotlin.collections.
        if (callee.containingDeclaration.fqNameSafe.asString() != "kotlin.collections") {
            return
        }

        // If the function is the `forEach` extension over `Map`, we need to give a message to use `forEachEntry`.  See
        // comments on `datastructures.stdcollections.forEachEntry` for why this is handled differently from everything
        // else.
        if (callee.jvmSignatureString == mapForEachSignature) {
            report(CodeSmell(
                issue,
                Entity.from(calleeRef),
                "${callee.fqNameSafe} has a better alternative: `forEachEntry`, from `datastructures.stdcollections`."
            ))
            return
        }

        // Is there an equivalent function in datastructures.stdcollections?
        if (!exports.containsEquivalent(callee.original)) {
            return
        }

        if (calleeRef is KtNameReferenceExpression) {
            // Did we resolve through an alias?  If so, assume the code knows what it's doing.
            if (callee.name != calleeRef.getReferencedNameAsName()) {
                return
            }

            // If the call is explicitly package-qualified, assume we really do want whatever package it is.
            if (bindingContext[BindingContext.CALL, calleeRef]?.explicitReceiver is PackageQualifier) {
                return
            }
        }

        report(CodeSmell(
            issue,
            Entity.from(calleeRef),
            "${callee.fqNameSafe} has a better alternative.  import datastructures.stdcollections.*"
        ))
    }
}
