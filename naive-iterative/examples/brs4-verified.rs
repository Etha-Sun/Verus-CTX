use vstd::prelude::*;
fn main() {}
verus!{

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
    requires 
    ensures
{
    let mut i: usize = 0;
    {
        if (i % 4 == 0) {
        } else {
        }
    }

    
    {
        if (i == 0) {
        } else {
            let temp = sum[0];
        }
    }
}
} // verus!