use vstd::prelude::*;
fn main() {}
verus!{

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
    requires 
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
    ensures
        sum[0] == 0,
{
    let mut i: usize = 0;
    while (i < N as usize)
    invariant 
        (a.len() == N,
        sum.len() == 1,
        i <= N,
        forall |j: usize| 0 <= j && j < i ==> a[j] == j % 1)
    {
        a.set(i, i % 1 );
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
    invariant 
        (a.len() == N,
        sum.len() == 1,
        i <= N,
        forall |j: usize| 0 <= j && j < i ==> sum[0] == (if j == 0 { 0 } else { sum[0] + a[j] }))
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            let temp = sum[0];
            sum.set(0, temp + a[i]);
        }
        i = i + 1;
    }
    assert(sum[0] == 0);
}
}