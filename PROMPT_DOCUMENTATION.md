# Verus Auto Prover - Prompt Documentation

## Overview

This document provides a comprehensive overview of all prompts used in the Verus Auto Prover system. The system uses three main types of prompts for different stages of the verification process.

## Prompt Files

### Primary Configuration: `prompts.json`

The main prompt configuration file containing all prompt templates and model configurations.

## Prompt Types

### 1. Initial Proof Generation Prompt

**Purpose**: Generate the first version of formal proofs for Rust/Verus code
**Key**: `initial_proof_generation.template`
**Usage**: When processing a new unverified file

**Template Structure**:
```
You are a professional Verus formal verification expert. Your task is to generate correct proofs for the given Rust verus program.

Please carefully analyze the following Rust/Verus code, understand its requires and ensures specifications, then generate complete proof that can pass Verus verification.

**CRITICAL REQUIREMENT - NEVER MODIFY THE ORIGINAL CODE LOGIC**
**ABSOLUTELY FORBIDDEN - VIOLATING THESE WILL RESULT IN FAILURE**
**DO NOT UNDER ANY CIRCUMSTANCES:**
1. **NEVER EVER modify, change, alter, or delete ANY original code content**
2. **NEVER modify the original requires/ensures specifications**
3. **NEVER change function signatures, parameters, names, or return types**
4. **NEVER alter existing code logic, control flow, or program structure**
5. **NEVER modify, delete, or change existing variable declarations or assignments**
6. **NEVER change existing expressions, statements, or return values**
7. **NEVER remove any existing code lines**
8. **NEVER change the order of existing statements**
9. **NEVER modify comments that are part of the original code**
10. **NEVER change ANY character of the original code structure**
11. **NEVER replace the original implementation with a different one**
12. **NEVER change the algorithm or logic of the function**

**CRITICAL RULE: PRESERVE EVERY SINGLE CHARACTER OF ORIGINAL CODE**
**You can ONLY ADD proof annotations. You CANNOT modify, delete, or change anything that exists in the original code. Think of the original code as READ-ONLY - you can only supplement it with additional proof content.**

**WHAT YOU ARE ALLOWED TO ADD (AND ONLY THIS):**
- Loop invariants: `invariant {{ condition }}`
- Assertions: `assert(condition);`
- Proof blocks: `proof {{ /* proof code */ }}`
- Helper lemmas as separate functions
- Comments explaining proof strategy
- Decreases clauses for recursive functions

**ABSOLUTELY FORBIDDEN PROOF METHODS:**
- NEVER use `assume(false)` or any contradictory assumptions
- NEVER use `#[verifier(external_body)]` or similar verification-skipping attributes
- NEVER use `assume()` to bypass proof obligations
- You MUST provide genuine proofs that work with the given implementation

**CRITICAL: NEVER DELETE RETURN STATEMENTS!**
**If the original code returns `sum`, you MUST keep `sum` as the return value!**
**If the original code returns `a + b`, you MUST keep `a + b` as the return value!**
**Always preserve ALL return statements and expressions EXACTLY as they appear!**

**Original Code:**
```rust
{code}
```

**CRITICAL OUTPUT REQUIREMENT: Your response must contain ONLY the complete Rust/Verus code, starting with 'use vstd::prelude::*;' and ending with '}} // verus!'. Do not include any explanatory text, markdown formatting, code blocks, or other content before or after the code. The output must be immediately executable by Verus.**

Please generate the complete Verus code with proofs:
```

**Variables**:
- `{code}`: The original Rust/Verus code to be proven

### 2. Iterative Fix Prompt

**Purpose**: Fix verification failures based on error messages and historical attempts
**Key**: `iterative_fix.template`
**Usage**: When previous verification attempts fail and need to be corrected

**Template Structure**:
```
You are a professional Verus formal verification expert. The previously generated proof failed verification, and now you need to fix it based on the error information.

**Historical Fix Information:**
{history}

**Current Code:**
```rust
{current_code}
```

**Verus Verification Error Message:**
```
{error_message}
```

{counterexample_section}

Please carefully analyze the error message, understand the problem, and generate the fixed complete code.

**CRITICAL REQUIREMENT - NEVER MODIFY THE ORIGINAL CODE LOGIC**
**ABSOLUTELY FORBIDDEN DURING FIXES - VIOLATING THESE WILL RESULT IN FAILURE**
**DO NOT UNDER ANY CIRCUMSTANCES:**
1. **NEVER EVER modify, change, alter, or delete ANY original code content**
2. **NEVER modify the original requires/ensures specifications**
3. **NEVER change function signatures, parameters, names, or return types**
4. **NEVER alter existing code logic, control flow, or program structure**
5. **NEVER modify, delete, or change existing variable declarations or assignments**
6. **NEVER change existing expressions, statements, or return values**
7. **NEVER remove any existing code lines**
8. **NEVER change the order of existing statements**
9. **NEVER modify comments that are part of the original code**
10. **NEVER change ANY character of the original code structure**
11. **NEVER replace the original implementation with a different one**
12. **NEVER change the algorithm or logic of the function**

**WHAT YOU CAN DO TO FIX (AND ONLY THIS):**
- ADD loop invariants: `invariant {{ condition }}`
- ADD assertions: `assert(condition);`
- ADD proof blocks: `proof {{ /* proof code */ }}`
- ADD helper lemmas as completely separate functions
- ADD comments explaining proof strategy
- ADD decreases clauses for recursive functions
- ADD type annotations where needed for proof

**ABSOLUTELY FORBIDDEN PROOF METHODS:**
- NEVER use `assume(false)` or any contradictory assumptions
- NEVER use `#[verifier(external_body)]` or similar verification-skipping attributes
- NEVER use `assume()` to bypass proof obligations
- You MUST provide genuine proofs that work with the given implementation

**CRITICAL RULE FOR FIXES: PRESERVE EVERY SINGLE CHARACTER OF ORIGINAL CODE**
You can ONLY ADD proof annotations to fix errors. You CANNOT modify, delete, or change anything that exists in the original code. The original code is read-only!

**CRITICAL OUTPUT REQUIREMENT: Your response must contain ONLY the complete fixed Rust/Verus code, starting with 'use vstd::prelude::*;' and ending with '}} // verus!'. Do not include any explanatory text, markdown formatting, or code blocks. The output must be immediately executable by Verus.**

Please generate the fixed complete Verus code:
```

**Variables**:
- `{history}`: Historical information about previous fix attempts
- `{current_code}`: The current version of the code that failed verification
- `{error_message}`: The Verus verification error message
- `{counterexample_section}`: Optional counterexample information section

### 3. Z3 Counterexample Generation Prompt

**Purpose**: Generate Z3 solver code to find counterexamples for verification failures
**Key**: `z3_counterexample_generation.template`
**Usage**: When verification fails and we need concrete examples of failure cases

**Template Structure**:
```
You are an expert in formal verification and SMT solvers. Generate a Python program using the z3-solver library to find specific variable assignments that trigger the following Verus verification failure.

**Original Rust/Verus Code:**
```rust
{current_code}
```

**Verus Verification Error:**
```
{error_message}
```

**Task:** Generate a complete Python program using z3-solver that finds concrete variable assignments that cause the verification failure. The goal is to identify specific input values or intermediate variable states that trigger the error, regardless of whether they violate preconditions or postconditions.

**Key Objectives:**
1. Model the function's execution logic step by step
2. Identify the specific point where verification fails
3. Find concrete variable assignments that lead to this failure
4. Consider all possible failure scenarios: loop invariant violations, assertion failures, postcondition violations, etc.
5. Generate multiple counterexamples showing different failure paths
6. Provide clear explanations of why each assignment triggers the error

**Requirements:**
- Use `from z3 import *` for imports
- Create Z3 variables for all relevant function parameters and intermediate variables
- Model the execution flow accurately, including loops and conditional branches
- Handle integer types appropriately (use BitVec for u32, etc.)
- For loop-related errors, model the loop state before and after iterations
- For invariant violations, show the state that initially satisfies but later violates the invariant
- Print results in a clear format: "Counterexample X: variable assignments -> failure reason"
- If no counterexamples found, print "No counterexamples found"
- Make the code robust and handle edge cases

**CRITICAL OUTPUT REQUIREMENT:** Your response must contain ONLY the complete Python code, no explanatory text, markdown formatting, or code blocks. The output must be immediately executable.

Generate the Z3 solver code:
```

**Variables**:
- `{current_code}`: The Rust/Verus code that failed verification
- `{error_message}`: The Verus verification error message

## Prompt Strategies

### Common Proof Strategies (from `proof_strategies` section):

1. **For loops**: Ensure correct invariants and decreases functions
2. **For recursive functions**: Ensure appropriate decreasing measures
3. **Use assert! macro**: Mark key properties of intermediate steps
4. **For array and vector operations**: Ensure bounds checking
5. **For integer operations**: Consider overflow issues
6. **Use proof blocks**: Contain pure proof code
7. **Leverage Verus built-in lemmas**: Use existing specifications
8. **Use assume! appropriately**: Simplify complex proofs (but be cautious)

## Model Configuration

### Default Settings (from `model_config`):
- **Model**: `gpt-4o`
- **Temperature**: `0.1` (low randomness for consistent proof generation)
- **Max Tokens**: `4000`

## Retry Mechanism

The system includes a sophisticated retry mechanism with prompt simplification:

### Simplified Prompts for Retries:

When the LLM refuses a request or returns unsatisfactory results, the system automatically generates simplified versions of the prompts by:

1. **Removing complex formatting**
2. **Reducing strict requirements**
3. **Focusing on core functionality**
4. **Shortening overall length**

### Implementation in `verus_auto_prover.py`:

```python
def simplify_prompt_for_retry(self, original_prompt: str, step_type: str) -> str:
    """Generate simplified prompt for retry attempts"""
    
    if step_type == "INITIAL_PROOF_GENERATION":
        return f"""Generate Verus proofs for this code. Add only proof annotations like invariants and assertions. Do not modify the original code.

Code:
{self.extract_code_from_prompt(original_prompt)}

Output only the complete Rust code with proofs."""
    
    elif step_type == "ITERATIVE_FIX":
        return f"""Fix the Verus verification error. Add proof annotations only.

{self.extract_relevant_sections(original_prompt)}

Output only the fixed complete Rust code."""
    
    elif step_type == "Z3_COUNTEREXAMPLE_GENERATION":
        return f"""Generate Python Z3 code to find counterexamples for this verification error.

{self.extract_relevant_sections(original_prompt)}

Output only executable Python code using z3-solver."""
    
    return original_prompt
```

## Usage in Code

### Loading Prompts:
```python
def load_prompts(self) -> dict:
    """Load prompt templates from prompts.json"""
    try:
        with open('prompts.json', 'r', encoding='utf-8') as f:
            return json.load(f)
    except FileNotFoundError:
        self.logger.error("prompts.json not found")
        return {}
```

### Using Templates:
```python
# Initial proof generation
prompts = self.load_prompts()
prompt_template = prompts.get("initial_proof_generation", {}).get("template", "")
prompt = prompt_template.format(code=code)

# Iterative fix
prompt_template = prompts.get("iterative_fix", {}).get("template", "")
prompt = prompt_template.format(
    history=history_text,
    current_code=current_code,
    error_message=error_message,
    counterexample_section=counterexample_section
)

# Z3 counterexample generation
prompt_template = prompts.get("z3_counterexample_generation", {}).get("template", "")
prompt = prompt_template.format(
    current_code=code,
    error_message=error_message
)
```

## Key Design Principles

1. **Code Preservation**: All prompts emphasize never modifying original code
2. **Additive Approach**: Only add proof annotations, never remove or change
3. **Comprehensive Error Handling**: Detailed instructions for different failure scenarios
4. **Executable Output**: All prompts require immediately executable code
5. **Iterative Improvement**: Support for multiple fix attempts with historical context
6. **Robust Retry Logic**: Automatic prompt simplification for failed attempts

## Customization

To customize prompts:

1. **Edit `prompts.json`**: Modify existing templates
2. **Add new prompt types**: Extend the JSON structure
3. **Adjust model settings**: Update `model_config` section
4. **Modify retry logic**: Update `simplify_prompt_for_retry` method

## Best Practices

1. **Keep prompts focused**: Each prompt should have a single clear purpose
2. **Maintain consistency**: Use similar formatting across all prompts
3. **Include examples**: Provide concrete examples of expected behavior
4. **Test thoroughly**: Verify prompts work with various code types
5. **Monitor performance**: Track success rates and adjust as needed
