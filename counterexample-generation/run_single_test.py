#!/usr/bin/env python3
"""
Single file test script for CTX-verify Experiment Runner
Tests the complete pipeline on a single file for debugging
"""

import sys
from pathlib import Path
from experiment_runner import ExperimentRunner
from config import API_KEY

def test_single_file(dataset_name, file_name):
    """Test the complete pipeline on a single file"""
    print(f"Testing single file: {dataset_name}/{file_name}")
    
    # Create runner
    runner = ExperimentRunner(API_KEY)
    
    # Construct file path
    file_path = Path("autoverus") / dataset_name / file_name / "autoverus_output.rs"
    
    if not file_path.exists():
        print(f"File not found: {file_path}")
        return False
    
    try:
        # Process the single file
        runner.process_file(file_path, dataset_name, file_name)
        
        # Generate reports for the single file
        runner.generate_excel_report()
        runner.generate_summary_tables()
        
        print(f"Single file test completed successfully!")
        print(f"Results saved to: {runner.results_dir}")
        return True
        
    except Exception as e:
        print(f"Single file test failed: {e}")
        import traceback
        traceback.print_exc()
        return False

def main():
    """Main function"""
    if len(sys.argv) != 3:
        print("Usage: python run_single_test.py <dataset_name> <file_name>")
        print("Example: python run_single_test.py cloverbench all_digits_strong")
        return 1
    
    dataset_name = sys.argv[1]
    file_name = sys.argv[2]
    
    success = test_single_file(dataset_name, file_name)
    return 0 if success else 1

if __name__ == "__main__":
    sys.exit(main())
