## CTX-Verification

This is a Non-LLM method to extract while loops in programs.

#### Some thoughts

Actually use two important insights:

1. Invariants cannot use variables whose lifecycle is confined to the loop's body (Loop-local variables).

    As a consequence, all variables that appear in an `invariant` must be declared before the `while` loop. We just need to find the `let` for each variable and record whether it is mutable, and whether it is a scalar variable or a vector.

2. The invariant proving can be isolated!

#### How to do testing in Verus

Try to do testing in the very beginning of the program. 

Non-LLM method: 

1. adding assertion in the main function. Like `assert!(all_sequence_equal_length(&(vec![vec![11, 22, 33], vec![55, 66]]) ));`

2. Use `verus --no-verify --compile main.rs`

   (Mark all the functions as \#[verifier::external_body] and `verus --compile main.rs`.)

#### How to use this program?

The core is `convert.py`. It can convert one program to the whileloop-isolated program. 

If you want do batch tests. 

First Config your ROOT and folders in `batch_convert.py`

```
ROOT = Path(__file__).resolve().parent.parent
CONVERTER = ROOT / 'code' / 'convert.py'
BENCHMARKS = ROOT / 'benchmarks'
```
Then 

```
python path/to/batch_convert.py | cat
```

