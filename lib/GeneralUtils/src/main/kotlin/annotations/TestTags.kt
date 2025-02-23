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

package annotations

object TestTags {
    /**
      `@Tag(EXPENSIVE)` marks a test as using more resources than we are willing to spend in a normal PR CI run.

      Note that in order to run tests marked "expensive" locally, either
       - run using the appropriate filter, like this: `./gradlew test --tests <my.test.class> -Ptest.filter=expensive`
       - temporarily comment the annotation in the test file
    */
    const val EXPENSIVE = "expensive"

    /**
      `@Tag(annotations.TestTags.TEMPORARY_NO_CI)` marks a test as temporarily excluded from all CI runs.  This
      annotation must be accompanied by a Jira ticket!
    */
    const val TEMPORARY_NO_CI = "no_ci"
}
