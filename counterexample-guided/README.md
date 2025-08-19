## CTX-Verify Experiment Runner Usage Guide

This file is not AI-generated. Please take a good look at it~

#### Configuration (config.py)

- Set experiment parameters, API keys, model names, timeouts, and file paths.
- **Important**: Change BASE_DIR to your actual dataset root path before running any experiments.

```
# DeepSeek Reasoner API Configuration
API_KEY = "your_deepseek_api"
API_BASE_URL = "https://api.deepseek.com"
MODEL_NAME = "deepseek-chat"

# Experiment Parameters
MAX_Z3_ATTEMPTS = 5
MAX_REPAIR_ATTEMPTS = 3
MAX_API_RETRIES = 3

# Timeouts (in seconds)
API_TIMEOUT = 300
VERUS_TIMEOUT = 120
PYTHON_EXECUTION_TIMEOUT = 30

# File Paths
BASE_DIR = "your_folder_path_here"  # Replace with your actual folder path
RESULTS_DIR_PREFIX = "results" 
```

#### Batch Experiment (experiment_runner.py)

Runs the full pipeline: Verus verification, Z3 counterexample generation, proof repair, and Excel report generation.

```
python experiment_runner.py
```
Results are saved in a new folder named results-<timestamp>.

#### Single File Test (run_single_test.py)

```
python run_single_test.py <dataset_name> <file_name>
```
**Example**
```
python run_single_test.py examples test
```
- This can test the ./examples/test/cal_div/autoverus_output.rs and output the results in ./results-<timestamp> with the detailed rust files and counterexample.txt
