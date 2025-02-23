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

import argparse
from pathlib import Path
import os
import shutil
from glob import glob
from concurrent.futures import ProcessPoolExecutor


def remove_old_dirs(conf_path: Path) -> None:
    """
    Remove old directories like .certora_internal and emv* based on the provided conf_path.

    Args:
        conf_path (Path): The path to the configuration file.
    """
    certora_internal_path = conf_path.parent / ".certora_internal"
    if certora_internal_path.exists() and certora_internal_path.is_dir():
        shutil.rmtree(certora_internal_path)
    emv_directories = glob(str(conf_path.parent / "emv*"))
    for emv_dir in emv_directories:
        if os.path.isdir(emv_dir):
            shutil.rmtree(emv_dir)


def certora_run(conf_path: Path) -> None:
    """
    Run Certora with the provided configuration file and save verifier results.

    Args:
        conf_path (Path): The path to the configuration file.
    """
    cmd = f"certoraRun.py {conf_path.name} --save_verifier_results"
    os.system(cmd)


conversion = {
    "(": "LP",
    ")": "RP",
    ",": "C",
    "[": "LB",
    "]": "RB",
    "[]": "LBRB",
    "uint256": "U256",
    "address": "ADR",
    "bytes32": "B32"
}

def copy_files(conf_path: Path) -> None:
    """
    Copy verifierResults content to the parent directory and expected rule output JSON files.

    Args:
        conf_path (Path): The path to the configuration file.
    """
    # Copy verifierResults content
    verifier_results_paths = list(conf_path.parent.rglob("verifierResults"))
    if not verifier_results_paths:
        raise ValueError(f"no violations were found for {conf_path.parent}\n"
                         "call trace test infra expects violated rules, and so no verifierResults were created.")
    verifier_results_dir = verifier_results_paths[0]
    rules = []
    for item in verifier_results_dir.iterdir():
        # Copy each item to the parent directory and save rule name that has call trace
        rules.append(item.name)
        shutil.copytree(item, conf_path.parent / item.name, dirs_exist_ok=True)


def refresh_single(conf_path: Path) -> None:
    """
    Refresh the prerequisites for the callTrace unit test for a single configuration file.

    Args:
        conf_path (Path): The path to the configuration file.
    """
    if ".certora_internal" in conf_path.as_posix() or "emv-" in conf_path.as_posix():
        return
    print(f"Working on {conf_path}")
    current_path = os.getcwd()
    os.chdir(conf_path.parent)

    if (conf_path.parent / "CallTraceRefresherIgnore").is_file():
        print("file 'CallTraceRefresherIgnore' present, skipping directory")
        return

    remove_old_dirs(conf_path)

    certora_run(conf_path)

    copy_files(conf_path)

    remove_old_dirs(conf_path)

    os.chdir(current_path)


def main() -> None:
    parser = argparse.ArgumentParser(description="""Refresh the prerequisites for the callTrace unit test.
                                      Use only when you are sure you need it!""")
    parser.add_argument("conf_file_path", nargs='?', help="""Relative path to the conf file
                         for example: src/test/resources/solver/CallTraceTests/../example.conf,
                         if no corresponding command-line argument is present, refresh all of the CallTrace tests""")
    args = parser.parse_args()

    conf_file_path = Path(args.conf_file_path) if args.conf_file_path else None

    try:
        if conf_file_path:
            abs_path = conf_file_path.resolve()
            print("Configuration file path:", abs_path)
            refresh_single(abs_path)
        else:
            # Find all .conf files under "src/test/resources/solver/CallTraceTests"
            conf_files_path = list(Path("src/test/resources/solver/CallTraceTests").resolve().rglob("*.conf"))
            with ProcessPoolExecutor() as executor:
                # Refresh all configurations in parallel using ProcessPoolExecutor
                executor.map(refresh_single, conf_files_path)

    except Exception as e:
        print(f"Failed to refresh files \n {e}")
        exit(1)

    print("Success to refresh files")
    exit(0)


if __name__ == "__main__":
    main()
