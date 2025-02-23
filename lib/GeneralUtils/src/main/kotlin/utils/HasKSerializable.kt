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
 * Classes that implement [HasKSerializable] are required to have a [KSerializable]/[kotlinx.serialization.Serializable]
 * annotation.  This allows us to reason about the Kotlin-serializability of entire class hierarchies.  For example,
 * given:
 *      @KSerializable sealed class A : HasKSerializable
 *      @KSerializable class B : A()
 *
 * Then any object reference of type `A` is known at compile time to be serializable.
 *
 * We can use this in generic type parameter bounds, to ensure that generic types are serializable.  For example:
 *
 *      @KSerializable
 *      class Wrapper<T : MustHaveKSerializable>(val t: T)
 *
 * Instances of `Wrapper` are guaranteed at compile time to be fully serializable.  The validation logic that enforces
 * this guarantee is in [com.certora.detekt.MustHaveKSerializable]
 *
 * Note that sometimes we want a type that is constrained to serializable types that also include externally-defined
 * types like [Int] or [BigInteger].  Since these don't implement [HasKSerializable], we use do a straightforward
 * type constraint line above.  Instead, we have to use factory methods with the right type constraints.  For an
 * example of this, see [tac.MetaKey].
 */
interface HasKSerializable
