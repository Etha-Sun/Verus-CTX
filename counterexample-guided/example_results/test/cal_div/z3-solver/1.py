from z3 import *

def generate_counterexamples():
    try:
        # Initialize Z3 solver
        s = Solver()
        
        # Variables representing the state during loop execution
        x = Int('x')
        y = Int('y')
        
        # Initial conditions
        s.add(x == 0)
        s.add(y == 191)
        
        # Loop invariant conditions (to be violated)
        s.add(Not(And(7 <= y, 191 >= 7 * x)))
        
        # Counter for examples
        counter = 0
        max_examples = 5
        
        print("Generating counterexamples for loop invariant violation...")
        print("Looking for cases where either 7 <= y or 191 >= 7*x fails")
        
        while counter < max_examples and s.check() == sat:
            m = s.model()
            x_val = m.eval(x).as_long()
            y_val = m.eval(y).as_long()
            
            print(f"\nCounterexample {counter + 1}:")
            print(f"x = {x_val}, y = {y_val}")
            
            # Check which part of the invariant fails
            if not (7 <= y_val):
                print("Violation: 7 <= y is false")
            if not (191 >= 7 * x_val):
                print("Violation: 191 >= 7*x is false")
            
            # Add constraint to find new solutions
            s.add(Or(x != x_val, y != y_val))
            counter += 1
        
        # Now check for assertion failure cases
        s = Solver()
        x_assert = Int('x_assert')
        
        # Condition for assertion failure: 191 < 7*(x + 1)
        s.add(191 < 7 * (x_assert + 1))
        
        print("\nGenerating counterexamples for assertion failure...")
        print("Looking for cases where 191 >= 7*(x + 1) fails")
        
        counter = 0
        while counter < max_examples and s.check() == sat:
            m = s.model()
            x_val = m.eval(x_assert).as_long()
            
            print(f"\nCounterexample {counter + 1}:")
            print(f"x = {x_val}")
            print(f"Violation: 191 >= 7*({x_val} + 1) is false (7*({x_val}+1) = {7*(x_val+1)})")
            
            s.add(x_assert != x_val)
            counter += 1
            
    except Exception as e:
        print(f"Error occurred while using Z3: {e}")
        print("Please ensure Z3 is properly installed (pip install z3-solver)")

if __name__ == "__main__":
    generate_counterexamples()