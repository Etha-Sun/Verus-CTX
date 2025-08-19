use vstd::prelude::*;
fn main() {}
verus!{

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	ensures
		sum[0] <= 4 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
	invariant 
		0 <= i <= N as usize,
		forall |j: usize| 0 <= j < i ==> (a[j] == 4 || a[j] == 0),
		forall |j: usize| 0 <= j < i && j % 4 == 0 ==> a[j] == 4,
		forall |j: usize| 0 <= j < i && j % 4 != 0 ==> a[j] == 0,
	{
		if (i % 4 == 0) {
			a.set(i, 4);
		} else {
			a.set(i, 0);
		}
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
	invariant 
		0 <= i <= N as usize,
		0 <= sum[0] <= 4 * i,
		forall |j: usize| 0 <= j < i ==> (a[j] == 4 || a[j] == 0),
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			let temp = sum[0];
			sum.set(0, temp + a[i]);
		}
		i = i + 1;
	}
}
} // verus!