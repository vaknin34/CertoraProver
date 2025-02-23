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

package cache

import utils.SerializableWithAdapter
import java.io.InputStream
import java.io.ObjectInputStream
import java.lang.reflect.Modifier

private const val singletonFieldModifiers = (Modifier.STATIC or Modifier.PUBLIC or Modifier.FINAL)

private class InvalidSingletonSerializationError(message: String) : Error(message)

class SingletonCheckingStream(iStr: InputStream) : ObjectInputStream(iStr) {

    override fun resolveObject(obj: Any): Any {
        val klass = obj.javaClass
        val singleton = ((klass.modifiers and Modifier.FINAL) != 0) && klass.declaredFields.firstOrNull {
            it.type == klass && it.name == "INSTANCE" &&
                (it.modifiers and singletonFieldModifiers) == singletonFieldModifiers
        }?.let { _ ->
            val constr = klass.constructors
            constr.isEmpty()

        } ?: false
        // this class is final, has a public static final field named INSTANCE of type of the class,
        // and a single private constructor. This is probably a singleton. Does it implement readResolve?
        if(singleton) {
            val hasResolve = klass.declaredMethods.any {
                it.name == "readResolve" && it.parameterCount == 0 && it.returnType == Any::class.java
            }
            if(!hasResolve && !SerializableWithAdapter::class.java.isAssignableFrom(klass)) {
                throw InvalidSingletonSerializationError("Encountered an apparently singleton of " +
                        "$klass that did NOT implement readResolve()")
            }
        }
        return obj
    }

    init {
        enableResolveObject(true)
    }
}