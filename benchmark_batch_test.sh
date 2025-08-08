#!/bin/bash

# Verus Auto Prover Benchmark Batch Testing Script (Shell Version)
# Batch testing Verus auto proof generation tool performance on benchmark datasets

set -e  # Exit on error

# Configuration
API_KEY="${1:-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}"
BENCHMARKS_DIR="benchmarks"
VERUS_PROVER="verus_auto_prover.py"
RESULTS_DIR="results"
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
LOG_FILE="$RESULTS_DIR/benchmark_test_${TIMESTAMP}.log"
RESULTS_FILE="$RESULTS_DIR/benchmark_results_${TIMESTAMP}.txt"

# Create results directory
mkdir -p "$RESULTS_DIR"

# Check required files
if [[ ! -f "$VERUS_PROVER" ]]; then
    echo "❌ Error: Cannot find $VERUS_PROVER script"
    exit 1
fi

if [[ ! -d "$BENCHMARKS_DIR" ]]; then
    echo "❌ Error: Cannot find $BENCHMARKS_DIR directory"
    exit 1
fi

# Initialize statistics variables
TOTAL_FILES=0
SUCCESSFUL_FILES=0
FAILED_FILES=0

# Create results file
echo "🚀 Verus Auto Prover Batch Testing Started" > "$RESULTS_FILE"
echo "📅 Test Time: $(date)" >> "$RESULTS_FILE"
echo "🔑 API Key: ${API_KEY:0:10}...${API_KEY: -4}" >> "$RESULTS_FILE"
echo "=" >> "$RESULTS_FILE"

echo "🚀 Starting Verus Auto Prover Batch Testing"
echo "📅 Test Time: $(date)"
echo "🔑 API Key: ${API_KEY:0:10}...${API_KEY: -4}"
echo "📄 Results will be saved to: $RESULTS_FILE"
echo "📋 Detailed log: $LOG_FILE"
echo "=" 

# Note: History folders are preserved for analysis

# macOS compatible timeout function
run_with_timeout() {
    local timeout_duration=$1
    shift
    local cmd=("$@")
    
    # Run command in background
    "${cmd[@]}" &
    local cmd_pid=$!
    
    # Create timeout monitoring process
    (
        sleep "$timeout_duration"
        kill -9 "$cmd_pid" 2>/dev/null
    ) &
    local timeout_pid=$!
    
    # Wait for command completion
    if wait "$cmd_pid" 2>/dev/null; then
        # Command completed successfully, kill timeout process
        kill -9 "$timeout_pid" 2>/dev/null
        return 0
    else
        # Command failed or was killed by timeout
        kill -9 "$timeout_pid" 2>/dev/null
        return 1
    fi
}

# Test single file function with detailed statistics
test_file() {
    local file_path="$1"
    local relative_path="${file_path#$BENCHMARKS_DIR/}"
    
    echo -n "[$(printf "%3d" $((TOTAL_FILES + 1)))] Testing: $relative_path ... "
    
    # Record start time
    local start_time=$(date +%s)
    
    # Create temporary file to capture output
    local temp_output=$(mktemp)
    
    # Run verus prover with 300s timeout and capture output
    if run_with_timeout 300 python3 "$VERUS_PROVER" "$file_path" --api-key "$API_KEY" > "$temp_output" 2>&1; then
        local end_time=$(date +%s)
        local duration=$((end_time - start_time))
        
        # Extract detailed statistics from output
        local iterations=$(grep "🔄 总迭代次数:" "$temp_output" | sed 's/.*总迭代次数: //')
        local final_state=$(grep "📝 最终状态:" "$temp_output" | sed 's/.*最终状态: //')
        local z3_attempted=$(grep "🧮 Z3反例生成尝试:" "$temp_output" | sed 's/.*Z3反例生成尝试: //')
        local z3_successful=$(grep "✅ Z3反例生成成功:" "$temp_output" | sed 's/.*Z3反例生成成功: //')
        
        echo "✅ Success (${duration}s, iter:${iterations:-0}, z3:${z3_attempted:-否}/${z3_successful:-否})"
        echo "✅ $relative_path - Success (${duration}s) - Iterations:${iterations:-0} Z3_Attempted:${z3_attempted:-否} Z3_Success:${z3_successful:-否}" >> "$RESULTS_FILE"
        
        # Append detailed output to log
        cat "$temp_output" >> "$LOG_FILE"
        
        SUCCESSFUL_FILES=$((SUCCESSFUL_FILES + 1))
        rm -f "$temp_output"
        return 0
    else
        local end_time=$(date +%s)
        local duration=$((end_time - start_time))
        
        # Extract detailed statistics from failed output
        local iterations=$(grep "🔄 总迭代次数:" "$temp_output" | sed 's/.*总迭代次数: //')
        local final_state=$(grep "📝 最终状态:" "$temp_output" | sed 's/.*最终状态: //')
        local z3_attempted=$(grep "🧮 Z3反例生成尝试:" "$temp_output" | sed 's/.*Z3反例生成尝试: //')
        local z3_successful=$(grep "✅ Z3反例生成成功:" "$temp_output" | sed 's/.*Z3反例生成成功: //')
        
        if (( duration >= 300 )); then
            echo "⏰ Timeout (${duration}s)"
            echo "⏰ $relative_path - Timeout (${duration}s)" >> "$RESULTS_FILE"
        else
            local error_type="${final_state:-unknown}"
            echo "❌ Failed (${duration}s, type:${error_type}, iter:${iterations:-0}, z3:${z3_attempted:-否}/${z3_successful:-否})"
            echo "❌ $relative_path - Failed (${duration}s) - Type:${error_type} Iterations:${iterations:-0} Z3_Attempted:${z3_attempted:-否} Z3_Success:${z3_successful:-否}" >> "$RESULTS_FILE"
        fi
        
        # Append detailed output to log
        cat "$temp_output" >> "$LOG_FILE"
        
        FAILED_FILES=$((FAILED_FILES + 1))
        rm -f "$temp_output"
        return 1
    fi
}

# Main testing loop
main_test() {
    # Test standard structure datasets
    for dataset in "CloverBench" "MBPP" "Diffy" "Misc" "SVComp-Array-fpi"; do
        unverified_dir="$BENCHMARKS_DIR/$dataset/unverified"
        
        if [[ -d "$unverified_dir" ]]; then
            echo ""
            echo "📂 Testing dataset: $dataset"
            echo "-"
            
            dataset_total=0
            dataset_success=0
            
            # Iterate through all .rs files in this dataset (exclude -verified files and history folders)
            while IFS= read -r -d '' file; do
                # Test file and capture exit status without exiting script
                if test_file "$file"; then
                    dataset_success=$((dataset_success + 1))
                fi
                TOTAL_FILES=$((TOTAL_FILES + 1))
                dataset_total=$((dataset_total + 1))
                
                # Progress indicator every 10 files
                if (( TOTAL_FILES % 10 == 0 )); then
                    echo "📊 Progress: $TOTAL_FILES files tested so far..."
                fi
                
            done < <(find "$unverified_dir" -name "*.rs" ! -name "*-verified.rs" ! -path "*/history-*/*" -print0 2>/dev/null)
            
            if (( dataset_total > 0 )); then
                local success_rate=$((dataset_success * 100 / dataset_total))
                echo "📊 $dataset: $dataset_success/$dataset_total (${success_rate}%)"
                echo "📊 $dataset: $dataset_success/$dataset_total (${success_rate}%)" >> "$RESULTS_FILE"
            fi
        else
            echo "⚠️  Skipping $dataset (unverified directory not found)"
        fi
    done
    
    # Test interprocedural special structure
    interprocedural_dir="$BENCHMARKS_DIR/interprocedural"
    if [[ -d "$interprocedural_dir" ]]; then
        echo ""
        echo "📂 Testing dataset: interprocedural"
        echo "-"
        
        for subdir in "$interprocedural_dir"/*; do
            if [[ -d "$subdir/unverified" ]]; then
                subdir_name=$(basename "$subdir")
                echo "  📁 Subdirectory: $subdir_name"
                
                while IFS= read -r -d '' file; do
                    test_file "$file" || true  # Don't exit on test failure
                    TOTAL_FILES=$((TOTAL_FILES + 1))
                    
                    # Progress indicator every 10 files
                    if (( TOTAL_FILES % 10 == 0 )); then
                        echo "📊 Progress: $TOTAL_FILES files tested so far..."
                    fi
                    
                done < <(find "$subdir/unverified" -name "*.rs" ! -name "*-verified.rs" ! -path "*/history-*/*" -print0 2>/dev/null)
            fi
        done
    fi
}

# Signal handling
trap 'echo ""; echo "⏹️  Testing interrupted"; exit 130' INT TERM

# Run main testing
echo "🔍 Scanning test files..."
main_test

# Generate final report
echo ""
echo "=" 
echo "🎯 Testing completed!"
echo "📊 Total files: $TOTAL_FILES"
echo "✅ Successful: $SUCCESSFUL_FILES"
echo "❌ Failed: $FAILED_FILES"

if (( TOTAL_FILES > 0 )); then
    SUCCESS_RATE=$((SUCCESSFUL_FILES * 100 / TOTAL_FILES))
    echo "📈 Success rate: ${SUCCESS_RATE}%"
    
    # Save final statistics to results file
    echo "" >> "$RESULTS_FILE"
    echo "=" >> "$RESULTS_FILE"
    echo "🎯 Final Statistics" >> "$RESULTS_FILE"
    echo "📊 Total files: $TOTAL_FILES" >> "$RESULTS_FILE"
    echo "✅ Successful: $SUCCESSFUL_FILES" >> "$RESULTS_FILE"
    echo "❌ Failed: $FAILED_FILES" >> "$RESULTS_FILE"
    echo "📈 Success rate: ${SUCCESS_RATE}%" >> "$RESULTS_FILE"
else
    echo "⚠️  No test files found"
fi

echo "📄 Detailed results saved to: $RESULTS_FILE"
echo "📋 Complete log available at: $LOG_FILE"
echo "=" 