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

package wasm.host.soroban.types

import analysis.CommandWithRequiredDecls.Companion.mergeMany
import datastructures.stdcollections.*
import tac.*
import utils.*
import vc.data.*
import wasm.host.soroban.*
import wasm.tacutils.*
import wasm.traps.*

/**
    A [MappingType] whose keys are contiguous integers starting from 0
 */
@KSerializable
abstract class ArrayType : MappingType() {

    /**
        Defines a new array whose contents are the values of the old array, but with [value] at index [key].
      */
    open fun put(newHandle: TACSymbol.Var, oldHandle: TACSymbol, key: TACSymbol, value: TACSymbol) =
        withSize(oldHandle) { size ->
            mergeMany(
                Trap.assert("Index out of bounds") {
                    (0.asTACExpr le key.asSym()) and (key.asSym() lt size.asSym())
                },
                new(newHandle) { size.asSym() },
                defineMapping(newHandle) { queryKey ->
                    ite(
                        queryKey eq key.asSym(),
                        value.asSym(),
                        selectFromPreviousMappings(oldHandle.asSym(), queryKey)
                    )
                }
            )
        }

    /**
        Gets the [key]'th value.
     */
    fun get(dest: TACSymbol.Var, handle: TACSymbol, key: TACSymbol) =
        withSize(handle) { size ->
            mergeMany(
                Trap.assert("Index out of bounds") {
                    (0.asTACExpr le key.asSym()) and (key.asSym() lt size.asSym())
                },
                assign(dest) {
                    select(mappings.asSym(), handle.asSym(), key.asSym())
                },
            )
        }

    /**
        Gets the first element of the array
     */
    fun front(retVar: TACSymbol.Var, handle: TACSymbol) =
        get(retVar, handle, TACSymbol.Zero)

    /**
        Gets the last element of the array
     */
    fun back(retVar: TACSymbol.Var, handle: TACSymbol) =
        withSize(handle) { size ->
            TACExprFactUntyped {
                size.asSym() sub 1.asTACExpr
            }.letVar("index") { index ->
                get(retVar, handle, index.s)
            }
        }

    /**
        Defines a new array whose contents are the values of the old array, with [value] added to the end.
     */
    open fun pushBack(newHandle: TACSymbol.Var, oldHandle: TACSymbol, value: TACSymbol) =
        withSize(oldHandle) { oldSize ->
            mergeMany(
                new(newHandle) { oldSize.asSym() add 1.asTACExpr },
                defineMapping(newHandle) { queryIndex ->
                    ite(
                        queryIndex eq oldSize.asSym(),
                        value.asSym(),
                        selectFromPreviousMappings(oldHandle.asSym(), queryIndex)
                    )
                }
            )
        }

    /**
        Defines a new array whose contents are the values of the old array, with [value] added to the start.
     */
    open fun pushFront(newHandle: TACSymbol.Var, oldHandle: TACSymbol, value: TACSymbol) =
        withSize(oldHandle) { oldSize ->
            mergeMany(
                new(newHandle) { oldSize.asSym() add 1.asTACExpr },
                defineMapping(newHandle) { queryIndex ->
                    ite(
                        queryIndex eq 0.asTACExpr,
                        value.asSym(),
                        selectFromPreviousMappings(oldHandle.asSym(), queryIndex sub 1.asTACExpr)
                    )
                }
            )
        }

    /**
        Defines a new array whose contents are the values of the old array, with the last value removed.
     */
    open fun popBack(newHandle: TACSymbol.Var, oldHandle: TACSymbol) =
        withSize(oldHandle) { oldSize ->
            mergeMany(
                Trap.assert("Cannot pop from an empty array") { oldSize.asSym() gt 0.asTACExpr },
                new(newHandle) { oldSize.asSym() sub 1.asTACExpr },
                defineMapping(newHandle) { queryIndex ->
                    selectFromPreviousMappings(oldHandle.asSym(), queryIndex)
                }
            )
        }

    /**
        Defines a new array whose contents are the values of the old array, with the first value removed.
     */
    open fun popFront(newHandle: TACSymbol.Var, oldHandle: TACSymbol) =
        withSize(oldHandle) { oldSize ->
            mergeMany(
                Trap.assert("Cannot pop from an empty array") { oldSize.asSym() gt 0.asTACExpr },
                new(newHandle) { oldSize.asSym() sub 1.asTACExpr },
                defineMapping(newHandle) { queryIndex ->
                    selectFromPreviousMappings(oldHandle.asSym(), queryIndex add 1.asTACExpr)
                }
            )
        }

    /**
        Defines a new array whose contents are the values of the old array, but with [value] inserted at [index]
     */
    open fun insert(newHandle: TACSymbol.Var, oldHandle: TACSymbol, index: TACSymbol, value: TACSymbol) =
        withSize(oldHandle) { oldSize ->
            mergeMany(
                Trap.assert("Index out of bounds") {
                    (0.asTACExpr le index.asSym()) and (index.asSym() lt oldSize.asSym())
                },
                new(newHandle) { oldSize.asSym() add 1.asTACExpr },
                defineMapping(newHandle) { queryIndex ->
                    ite(
                        queryIndex lt index.asSym(),
                        selectFromPreviousMappings(oldHandle.asSym(), queryIndex),
                        ite(
                            queryIndex gt index.asSym(),
                            selectFromPreviousMappings(oldHandle.asSym(), queryIndex sub 1.asTACExpr),
                            value.asSym()
                        )
                    )
                }
            )
        }

    /**
        Defines a new array whose contents are the values of the old array, but without the value previously at
        [index].  All subsequent values are shifted down by one.
     */
    open fun delete(newHandle: TACSymbol.Var, oldHandle: TACSymbol, index: TACSymbol) =
        withSize(oldHandle) { oldSize ->
            mergeMany(
                Trap.assert("Index out of bounds") {
                    (0.asTACExpr le index.asSym()) and (index.asSym() lt oldSize.asSym())
                },
                new(newHandle) { oldSize.asSym() sub 1.asTACExpr },
                defineMapping(newHandle) { queryIndex ->
                    ite(
                        queryIndex lt index.asSym(),
                        selectFromPreviousMappings(oldHandle.asSym(), queryIndex),
                        selectFromPreviousMappings(oldHandle.asSym(), queryIndex add 1.asTACExpr),
                    )
                }
            )
        }

    /**
        Defines a new array whose contents are the values two other arrays, appended.
     */
    open fun append(newHandle: TACSymbol.Var, leftHandle: TACSymbol, rightHandle: TACSymbol) =
        withSize(leftHandle) { leftSize ->
            withSize(rightHandle) { rightSize ->
                mergeMany(
                    new(newHandle) { leftSize.asSym() add rightSize.asSym() },
                    defineMapping(newHandle) { queryIndex ->
                        ite(
                            queryIndex lt leftSize.asSym(),
                            selectFromPreviousMappings(leftHandle.asSym(), queryIndex),
                            selectFromPreviousMappings(rightHandle.asSym(), queryIndex add leftSize.asSym()),
                        )
                    }
                )
            }
        }

    /**
        Defines a new array whose contents are the values of the old array from [start] to [end] (exclusive)
     */
    open fun slice(newHandle: TACSymbol.Var, oldHandle: TACSymbol, start: TACSymbol, end: TACSymbol) =
        withSize(oldHandle) { oldSize ->
            mergeMany(
                Trap.assert("Start index out of bounds") {
                    (0.asTACExpr le start.asSym()) and (start.asSym() le oldSize.asSym())
                },
                Trap.assert("End index out of bounds") {
                    (0.asTACExpr le end.asSym()) and (end.asSym() le oldSize.asSym())
                },
                Trap.assert("Start greater than end") {
                    start.asSym() le end.asSym()
                },
                new(newHandle) { end.asSym() sub start.asSym() },
                defineMapping(newHandle) { queryIndex ->
                    selectFromPreviousMappings(
                        oldHandle.asSym(),
                        queryIndex add start.asSym()
                    )
                }
            )
        }
}
