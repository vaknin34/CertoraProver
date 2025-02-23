#!/usr/bin/env python3
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

import os
import re
import sys
import json
import datetime
import argparse
import subprocess

from rich.console import Console
from pathlib import Path
from typing import Dict, List

scripts_dir_path = Path(__file__).parent.resolve()  # containing directory
sys.path.insert(0, str(scripts_dir_path))

from Shared import certoraValidateFuncs as Vf
from Shared import certoraUtils as Util
from Mutate import mutateConstants as MConstants


class MutantGenerator:

    def __init__(self) -> None:
        self.mutant_file = Path('')
        self.args = sys.argv[1:]
        self.conf = None
        self.description = None
        self.original_file = Path('')
        self.patch_directory = Path(MConstants.MUTATIONS)
        self.patch_filename = None

    def read_args(self) -> None:
        parser = argparse.ArgumentParser(description="*** Generate a manual mutation from git patch ***")
        parser.add_argument('original_file', type=Path, nargs=1, help='Generate a mutation for this file')
        parser.add_argument('--description', type=str, help='Add a comment to '
                                                            'the mutant file')
        parser.add_argument('--conf', type=Path, help='Add the mutant to this Prover configuration')
        parser.add_argument('--patch_directory', type=Path, help='target directory for the generated patch')
        parser.add_argument('--patch_filename', type=str, help='The file name of the created patch '
                                                               '(without the `.X.patch` extension)')

        args = parser.parse_args()

        try:
            self.original_file = Path(Vf.validate_readable_file(str(args.original_file[0]), '.sol')).resolve()
        except Util.CertoraUserInputError as orig_exception:
            raise Util.CertoraUserInputError("Error when reading <file>", orig_exception) from None

        self.description = args.description
        if args.patch_directory:
            self.patch_directory = Vf.validate_writable_dir(args.patch_directory)
        self.patch_filename = args.patch_filename

        self.conf = args.conf

        if self.conf:
            self.conf = Path(Vf.file_exists_and_readable(self.conf))
        self.validate_input()

    def validate_input(self) -> None:
        # make sure the original file is tracked by git
        try:
            subprocess.run(['git', 'ls-files', '--error-unmatch', self.original_file], check=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        except Exception as orig_exception:
            raise Util.CertoraUserInputError(f"Cannot find {self.original_file} in Git", orig_exception) from None
        # make sure the original file was modified
        try:
            git_command = ['git', 'status', '--porcelain', str(self.original_file)]
            result = subprocess.run(git_command, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        except Exception as orig_exception:
            raise Util.CertoraUserInputError(f"{' '.join(git_command)} failed", orig_exception) from None

        if not result.stdout:
            raise Util.CertoraUserInputError(f"Cannot create patch, {self.original_file} "
                                             f"was not modified !!") from None

    def collect_metadata(self) -> str:
        current_time = datetime.datetime.now().isoformat()
        cwd = os.getcwd()
        latest_commit = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
        user_name = subprocess.run(["git", "config", "user.name"], capture_output=True, text=True).stdout.strip()
        user_email = subprocess.run(["git", "config", "user.email"], capture_output=True, text=True).stdout.strip()

        metadata = ''
        if self.description:
            metadata += f"Description: {self.description}\n"
        if cwd:
            metadata += f"cwd: {cwd}\n"
        if self.original_file:
            metadata += f"Original File: {self.original_file}\n"
        if self.args:
            metadata += f"Script Args: {self.args}\n"
        if current_time:
            metadata += f"Current Time: {current_time}\n"
        if latest_commit:
            metadata += f"Latest Commit: {latest_commit}\n"
        if user_name:
            metadata += f"User Name: {user_name}\n"
        if user_email:
            metadata += f"User Email: {user_email}\n"

        return f"\n\n{metadata} \n\n"

    def set_mutant_file(self) -> None:
        patch_filename = self.patch_filename or self.original_file.name
        highest = 0
        pattern = re.compile(rf'{patch_filename}\.(\d+)\.patch')

        if self.patch_directory.exists():
            for filename in os.listdir(self.patch_directory):
                match = pattern.match(filename)
                if match:
                    integer_value = int(match.group(1))
                    if integer_value > highest:
                        highest = integer_value

        self.mutant_file = self.patch_directory / f"{patch_filename}.{highest + 1}.patch"
        print(f"mutant_file - {self.mutant_file}")

    def generate_mutant(self) -> None:
        assert self.original_file, "generate_mutant: self.original_file is None"
        Vf.validate_file_in_git(self.original_file)

        diff_result = subprocess.run(['git', 'diff', 'HEAD', '--', self.original_file], capture_output=True, text=True)
        if diff_result.returncode != 0:
            raise Util.CertoraUserInputError(f"failed to diff {self.original_file} with the latest Git committed "
                                             f"version")
        patch_content = diff_result.stdout
        self.set_mutant_file()
        self.mutant_file.parent.mkdir(parents=True, exist_ok=True)
        with self.mutant_file.open('w') as f:

            f.write(self.collect_metadata())
            f.write(patch_content)

    def save_mutant_to_conf(self) -> None:

        assert self.conf, "save_mutant_to_conf: self.conf not set"
        with self.conf.open() as f:
            conf_content = json.load(f)

        if MConstants.MUTATIONS not in conf_content:
            conf_content[MConstants.MUTATIONS] = {}

        if MConstants.MANUAL_MUTANTS not in conf_content[MConstants.MUTATIONS]:
            conf_content[MConstants.MUTATIONS][MConstants.MANUAL_MUTANTS] = []

        mutants_array = conf_content[MConstants.MUTATIONS][MConstants.MANUAL_MUTANTS]

        if not self.is_manual_mutant_in_array(mutants_array):
            mutant_object = {
                MConstants.FILE_TO_MUTATE: os.path.relpath(self.original_file, Path.cwd()),
                MConstants.MUTANTS_LOCATION: os.path.relpath(self.mutant_file, Path.cwd())
            }
            mutants_array.append(mutant_object)
            print(f"added {str(mutant_object)}")

            with self.conf.open('w') as json_file:
                json.dump(conf_content, json_file, indent=4)

    def is_manual_mutant_in_array(self, mutants_array: List[Dict[str, str]]) -> bool:
        for mutant in mutants_array:
            if Path(mutant[MConstants.FILE_TO_MUTATE]).resolve() == self.original_file:
                stored_mutant_location_path = Path(mutant[MConstants.MUTANTS_LOCATION]).resolve()
                if stored_mutant_location_path == self.mutant_file:  # location is a file
                    return True
                if stored_mutant_location_path == self.mutant_file.parent:  # location is a directory
                    return True
        return False


def generate_mutant() -> None:
    mutantGenerator = MutantGenerator()
    mutantGenerator.read_args()
    mutantGenerator.generate_mutant()
    if mutantGenerator.conf:
        mutantGenerator.save_mutant_to_conf()


if __name__ == "__main__":

    try:
        generate_mutant()
        sys.exit(0)

    except KeyboardInterrupt:
        Console().print("[bold red]\nInterrupted by user")
        sys.exit(1)

    except Util.CertoraUserInputError as e:
        if e.orig:
            print(f"\n{str(e.orig).strip()}")
        if e.more_info:
            print(f"\n{e.more_info.strip()}")
        Console().print(f"[bold red]\n{e}\n")
        sys.exit(1)
    except Exception as e:
        Console().print(f"[bold red]\n{e}\n")
        sys.exit(1)
