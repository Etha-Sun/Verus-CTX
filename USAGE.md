conda activate marker 

run:
python3 verus_auto_prover.py examples/test.rs --api-key sk-your-openai-api-key

run all:
./benchmark_batch_test.sh sk-your-openai-api-key
or
python3 benchmark_batch_test.py --api-key sk-your-openai-api-key