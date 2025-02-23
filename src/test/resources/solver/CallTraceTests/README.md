# CallTrace Tests Readme

This `README.md` provides a clearer guide on adding new cases to the CallTrace tests, including a step-by-step process.

# Adding New Cases to CallTrace Tests

To add new cases to CallTrace tests, follow these steps:

1. Open a new directory under the `CallTraceTests` directory.

2. Move the configuration file and its sources (contracts + specs) to the newly created directory.

3. Run the `CallTraceRefresher.py` script located at `Test/CITests/CallTraceRefresher.py`, specifying the configuration file path. This step will generate the necessary artifacts for generating the call trace.

4. Add new test cases in the `kotlin/solver/CallTraceTest.kt` file.

## Step-by-Step Guide

### Step 1: Create a New Directory

Navigate to the `CallTraceTests` directory and create a new subdirectory. This directory will contain the files for your new test cases.

### Step 2: Move Files

Move the configuration file along with its associated sources (contracts and specifications) to the newly created directory. This is essential for running the tests accurately.

### Step 3: Generate Call Trace

Execute the `CallTraceRefresher.py` script located at `Test/CITests/CallTraceRefresher.py`. Provide the path to your configuration file. This script will generate the required artifacts to create the call trace for your test cases.

Example command:
```sh
python Test/CITests/CallTraceRefresher.py /path/to/your/conf/file
```