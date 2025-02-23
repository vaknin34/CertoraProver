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
import unittest
import subprocess
from secrets import choice
import string
import shutil
from pathlib import Path
import json

scripts_dir_path = Path(__file__).parent.resolve()  # containing directory
sys.path.insert(0, str(scripts_dir_path))


def run_script(*args: str) -> subprocess.CompletedProcess:
    result = subprocess.run(['python', '../generateMutant.py'] + list(args), capture_output=True, text=True)
    return result


class TestArgparseExample(unittest.TestCase):
    branch_name = ''.join([choice(string.ascii_lowercase) for _ in range(5)])

    result = subprocess.run(['python', '../generateMutant.py'])

    def setUp(self) -> None:
        try:
            # Check the current git status to ensure we are in a git repository
            subprocess.run(['git', 'status'], check=True)
            subprocess.run(['git', 'stash'], check=True)

            # Create a new branch
            subprocess.run(['git', 'checkout', '-b', self.branch_name], check=True)
            print(f"Branch '{self.branch_name}' created successfully.")
        except subprocess.CalledProcessError as e:
            self.fail(f"Setup failed: {e}")

        with open('Bank.sol', 'a') as file:
            file.write('*** local_change2 ***')

    def tearDown(self) -> None:
        try:
            subprocess.run(['git', 'reset', '--hard'], check=True)
            subprocess.run(['git', 'checkout', '-'], check=True)
            print("Original branch was checked out successfully.")
            subprocess.run(['git', 'stash', 'pop'], check=True)
            result = subprocess.run(['git', 'branch', '-D', self.branch_name], capture_output=True, text=True)
            if result.returncode == 0:
                print(f"Branch '{self.branch_name}' force deleted successfully.")
            else:
                print(f"Failed to delete branch '{self.branch_name}': {result.stderr}")
        except subprocess.CalledProcessError as e:
            self.fail(f"tearDown failed: {e}")

    def test_no_args(self) -> None:
        result = run_script()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("the following arguments are required: original_file", result.stderr)

    def test_not_sol(self) -> None:
        result = run_script('Bank.conf')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Bank.conf does not end with .sol", result.stdout)

    def test_file_does_not_exist(self) -> None:
        result = run_script('does_not_exist.sol')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("does_not_exist.sol not found", result.stdout)

    def test_no_mutations_dir(self) -> None:
        shutil.rmtree('mutations', ignore_errors=True)
        run_script('Bank.sol')
        self.assertTrue(Path('mutations/Bank.sol.1.patch').exists())

    def test_user_mutations_dir(self) -> None:
        shutil.rmtree('my_mutations', ignore_errors=True)
        run_script('Bank.sol', '--patch_directory', 'my_mutations')
        self.assertTrue(Path('my_mutations/Bank.sol.1.patch').exists())
        shutil.rmtree('my_mutations', ignore_errors=True)

    def test_user_mutations_abs_dir(self) -> None:
        run_script('Bank.sol', '--patch_directory', str(Path.cwd().parent))
        patch_file = Path.cwd().parent / 'Bank.sol.1.patch'
        self.assertTrue(patch_file.exists())
        patch_file.unlink()

    def test_patch_name(self) -> None:
        shutil.rmtree('mutations', ignore_errors=True)
        run_script('Bank.sol', '--patch_filename', 'My_Bank.sol')
        self.assertTrue(Path('mutations/My_Bank.sol.1.patch').exists())
        shutil.rmtree('mutations', ignore_errors=True)

    def test_conf_file(self) -> None:
        def check_run(number: int) -> None:
            with conf_path.open() as f:
                conf_content = json.load(f)
                mutants_len = len(conf_content['mutations']['manual_mutants'])
                self.assertEqual(mutants_len, number, f"1st - mutants_len was {mutants_len} expected {number}")

        shutil.rmtree('mutations', ignore_errors=True)
        conf_path = Path('a.conf')
        conf_path.unlink(missing_ok=True)
        run_script('Bank.sol', '--conf', str(conf_path))
        check_run(1)
        run_script('Bank.sol', '--conf', str(conf_path))
        check_run(2)

if __name__ == '__main__':
    unittest.main()
