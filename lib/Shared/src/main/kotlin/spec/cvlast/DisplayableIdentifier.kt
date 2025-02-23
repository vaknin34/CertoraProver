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

package spec.cvlast

import allocator.Allocator
import com.certora.collect.*
import kotlinx.serialization.Serializable
import utils.*


/**
 * This RuleIdentifier is used to uniquely identify a rule, used for instance in the [TreeViewReporter].
 *
 * [displayName] will be the name displayed in the rule report for that particular node.
 * [counter] is an Integer to avoid collisions based on the same [displayName]
 *
 * The [toString] generates a human-readable string that contains the path in the tree view as displayed in the rule report.
 *
 * Example:
 * * For an invariant run with sanity, this will look as follows
 *  <invariant_name>_Using general requirements_<method>_<sanity_rule_name>
 * * For a rule run with sanity it will look as follows
 *  <rule_name>_<sanity_rule_name>
 */
@KSerializable
data class RuleIdentifier private constructor(
    override val parentIdentifier: DisplayableIdentifier?,
    override val displayName: String,
    override val counter: Int
) : DisplayableIdentifier() {
    companion object {
        /**
         * Call this method to generate a new [RuleIdentifier] based on the [displayName].
         * This should typically be called for each invariant / rule in the spec.
         */
        fun freshIdentifier(displayName: String): RuleIdentifier{
            return RuleIdentifier(null, displayName, Allocator.getFreshId(Allocator.Id.RULE_ID))
        }
    }

    /**
     * From an existing [RuleIdentifier] this method derives a new [RuleIdentifier] that
     * references its parent. The [displayName] will be used to for rendering this [RuleIdentifier]
     * in the TreeView.json.
     *
     * This will create a hierarchy of identifiers.
     *
     * Example:
     *
     * rule parametricRuleName(method f){...}
     *
     * creates the following hierarchy of [IRule]:
     * [GroupRule] parametricRuleName
     *  |- [CVLSingleRule] foo()
     *  |- [CVLSingleRule] bar()
     *
     * which will correspond to the following [RuleIdentifier]
     *  parametricRuleName
     *  |- parametricRuleName_foo() (where [displayName] is only the last part "foo()".)
     *  |- parametricRuleName_bar()
     */
    fun freshDerivedIdentifier(displayName: String): RuleIdentifier{
        return RuleIdentifier(this, displayName, Allocator.getFreshId(Allocator.Id.RULE_ID))
    }

    /**
     * Derives a new [AssertIdentifier] from this [RuleIdentifier] the [id] parameter
     * is expected to be the unique [id] returned from Allocator.getFreshId for that particular
     * assert.
     */
    fun derivedAssertIdentifier(displayName: String, id: Int = Allocator.getFreshId(Allocator.Id.ASSERTS)): AssertIdentifier{
        return AssertIdentifier(this, displayName, id)
    }

    override fun toString(): String{
        return ite(parentIdentifier == null, "", parentIdentifier.toString() + "-" ) + displayName
    }
}


/**
 * An identifier for an [ViolatedAssert].
 * @param counter is expected to be the unique [id] returned from Allocator.getFreshId (which is
 * persisted in [TACMeta.ASSERT_ID] in the corresponding [LTACCmd].
 */
@KSerializable
data class AssertIdentifier(override val parentIdentifier: RuleIdentifier?, override val displayName: String, override val counter: Int): DisplayableIdentifier(){
    override fun toString(): String{
        return ite(parentIdentifier == null, "", parentIdentifier.toString() + "-" ) + displayName
    }
}


@Serializable
@Treapable
sealed class DisplayableIdentifier: AmbiSerializable {
    abstract val displayName: String
    abstract val counter: Int
    abstract val parentIdentifier: DisplayableIdentifier?

    /** Return the [DisplayableIdentifier] that is a transitive parent of this one and has no parent. */
    fun root(): DisplayableIdentifier = parentIdentifier?.root() ?: this

}
