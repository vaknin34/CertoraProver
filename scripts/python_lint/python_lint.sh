#!/bin/bash
python3 -m flake8 --config scripts/python_lint/.flake8 scripts
status1=$?

python3 -m mypy --install-types --non-interactive --config-file scripts/python_lint/mypy.ini \
    $(ls scripts/*.py scripts/*/*.py Test/TestEVM/BuildCache/*.py | grep -v sunbeamRun.py | grep -v SendSlackMessage.py | grep -v RegTestDispatch.py | grep -v localRegtest.py) \
    1> /dev/null  # Suppress the success message
status2=$?

python3 scripts/python_lint/testPublicFlags.py  # checks that public flags have adequate name and default desc
status3=$?

if [ $status1 -eq 0 ] && [ $status2 -eq 0 ] && [ $status3 -eq 0 ]; then
    exit 0
else
    exit 1
fi
