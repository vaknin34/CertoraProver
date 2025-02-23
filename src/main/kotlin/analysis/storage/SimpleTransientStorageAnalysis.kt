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

package analysis.storage

import analysis.commands
import scene.IScene
import vc.data.StorageInfo
import vc.data.TACCmd

object SimpleTransientStorageAnalysis {
    fun usesTransientStorage(scene: IScene): Boolean{
        return scene.getContracts().any{
            contract -> contract.getMethods().any{
                m -> m.commands.any{
                    ltacmd ->
                        (ltacmd.cmd as? TACCmd.Simple.StorageAccessCmd)?.base in (contract.transientStorage as StorageInfo).storageVariables
                }
            }
        }
    }
}
