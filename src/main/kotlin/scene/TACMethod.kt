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

package scene

import bridge.EVMExternalMethodInfo
import config.ReportTypes
import datastructures.stdcollections.*
import evm.SighashInt
import instrumentation.calls.CalldataEncoding
import tac.DumpTime
import tac.ICoreTACProgram
import tac.MetaMap
import tac.TACFile
import utils.*
import vc.data.*
import java.math.BigInteger

class TACMethod(
    private var _code: CoreTACProgram,
    private val _containingContract: IContractClass,
    override val meta: MetaMap,
    override val attribute: MethodAttribute,
    override val evmExternalMethodInfo: EVMExternalMethodInfo?,
    override val sigHash: SighashInt?,
    override val name: String,
    override val soliditySignature: String?,
    override val calldataEncoding : ICalldataEncoding
) : ITACMethod {

    override fun hashCode() = hash {
        it + meta + attribute + evmExternalMethodInfo + sigHash + name + soliditySignature + calldataEncoding
    }

    constructor(
        _code: CoreTACProgram,
        _containingContract: IContractClass,
        _meta: MetaMap,
        _attrib: MethodAttribute,
        _evmMethodInfo: EVMExternalMethodInfo,
        _calldataEncoding : ICalldataEncoding = if (_attrib !is MethodAttribute.Unique.Fallback) {
            CalldataEncoding.calldataOf(_code, _evmMethodInfo)
        } else {
            CalldataEncoding.empty()
        }
    ) : this(
        _code,
        _containingContract,
        _meta,
        _attrib,
        _evmMethodInfo,
        _evmMethodInfo.sigHash?.let { SighashInt(it) },
        _evmMethodInfo.name,
        _evmMethodInfo.getPrettyName(),
        _calldataEncoding
    )

    constructor(
        _code: CoreTACProgram,
        _containingContract: IContractClass,
        _meta: MetaMap,
        _attrib: MethodAttribute,
        _sighash: BigInteger?,
        _name: String,
        _soliditySignature: String?,
        _calldataEncoding : ICalldataEncoding = CalldataEncoding.calldataOf(_code)
    ) : this(
        _code,
        _containingContract,
        _meta,
        _attrib,
        null,
        _sighash?.let { SighashInt(it) },
        _name,
        _soliditySignature,
        _calldataEncoding
    )

    constructor(
        _name: String,
        _code: CoreTACProgram,
        _containingContract: IContractClass,
        _meta: MetaMap,
        _attrib: MethodAttribute,
        _calldataEncoding : ICalldataEncoding = CalldataEncoding.calldataOf(_code)
    ) : this(
        _code,
        _containingContract,
        _meta,
        _attrib,
        null,
        null,
        _name,
        null,
        _calldataEncoding
    ) {
        check (_attrib is MethodAttribute.Unique) { "Must provide sighash for non-unique method attributes such as ${_attrib}" }
    }

    override var code: ICoreTACProgram
        get() = _code
        set(value) { _code = value as CoreTACProgram }

    override fun getContainingContract(): IContractClass = _containingContract
    override fun updateCode(p: PatchableProgram) {
        code = p.uncheckedAs<PatchingTACProgram<TACCmd.Simple>>().toCode(code)
    }

    override fun fork(): ITACMethod {
        val newCode = _code.copy(
            code = _code.code.toMap(),
            blockgraph = _code.blockgraph
        )
        // note that commands are not deeply copied

        return TACMethod(
            newCode,
            _containingContract,
            meta,
            attribute,
            evmExternalMethodInfo,
            sigHash,
            name,
            soliditySignature,
            calldataEncoding
        )
    }

    override fun shallowForkWithCodeAndCalldataEncoding(newCode: ICoreTACProgram, cdEncoding: ICalldataEncoding): ITACMethod =
        TACMethod(
            newCode as CoreTACProgram,
            _containingContract,
            meta,
            attribute,
            evmExternalMethodInfo,
            sigHash,
            name,
            soliditySignature,
            cdEncoding
        )

    override fun shallowForkWithCalldataEncoding(cdEncoding: ICalldataEncoding): TACMethod =
        TACMethod(
            _code,
            _containingContract,
            meta,
            attribute,
            evmExternalMethodInfo,
            sigHash,
            name,
            soliditySignature,
            cdEncoding
        )

    override fun toString(): String =
        soliditySignature ?: sigHash?.n?.toString(16) ?: "no signature"

    override fun dump(dumpType: ReportTypes, where: String, time: DumpTime) {
        _code.dump(dumpType, where, time)
    }

    override fun dumpBinary(where: String, label: String): TACFile {
        return _code.dumpBinary(where, label)
    }

    override val defaultType: ReportTypes
        get() = _code.defaultType
}
