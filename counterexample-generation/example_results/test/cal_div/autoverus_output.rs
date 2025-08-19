
use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]

fn cal_div() -> (r: (u32, u32))
    ensures
        r.0 == 27,
        r.1 == 2,
{
    let mut x: u32 = 0;
    let mut y: u32 = 191;
    while 7 <= y
    invariant
        7 <= y,
        191 >= 7 * x,
    decreases y
    {
        assert(x < 28); // Ensure x doesn't go beyond 27

        // Assert the bound before updating y
        // This prevents underflow by ensuring that the result is always non-negative
        assert(191 >= 7 * (x + 1));

        x = x + 1;
        y = 191 - 7 * x;
    }
    (x, y)
}

} // verus!

fn main() {}

// Score: (0, 2)
// Safe: True