#     The Certora Prover
#     Copyright (C) 2025  Certora Ltd.
#
#     This program is free software: you can redistribute it and/or modify
#     it under the terms of the GNU General Public License as published by
#     the Free Software Foundation, version 3 of the License.
#
#     This program is distributed in the hope that it will be useful,
#     but WITHOUT ANY WARRANTY; without even the implied warranty of
#     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#     GNU General Public License for more details.
#
#     You should have received a copy of the GNU General Public License
#     along with this program.  If not, see <https://www.gnu.org/licenses/>.

import sys
from pathlib import Path

scripts_dir_path = Path(__file__).parent.parent
scripts_dir_path = scripts_dir_path.resolve()
sys.path.insert(0, str(scripts_dir_path))
import CertoraProver.certoraContextAttributes as Attrs
import Mutate.mutateAttributes as MutAttrs
import Shared.certoraUtils as Util

"""
This script checks that public Python flags are compliant with our help messages.
1. A short enough flag name so as not to be truncated by the help message table.
2. They include a default description.

It is okay if the default description is an empty string. The goal is to force the programmer who added the flag to
 think whether it needs a default description.
"""

all_errors = set()

# solana and wasm do not add for the time being more attributes to test
for attr in Attrs.EvmProverAttributes.attribute_list() + MutAttrs.MutateAttributes.attribute_list():
    flag = attr.get_flag()
    if attr.help_msg != Util.SUPPRESS_HELP_MSG:
        if len(flag) > Util.MAX_FLAG_LENGTH:
            all_errors.add(f"user-facing flag {flag} is above the maximum length of {Util.MAX_FLAG_LENGTH}")
        if attr.default_desc is None:
            all_errors.add(f"flag {flag} has a help message but no default description (can be an empty string)")

if all_errors:
    for error in all_errors:
        print(error)
    raise RuntimeError("Visible flags have errors")
