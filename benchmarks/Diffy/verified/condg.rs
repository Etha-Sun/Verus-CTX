use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == 0,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
		invariant 
			forall |k:int| 0 <= k < i ==> a[k] == 1,
			a.len() == N,
		decreases N - i,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0 <= k < N ==> a[k] == 1,
			a.len() == N,
			sum[0] == i,
			sum.len() == 1,
		decreases N - i,
	{
		let temp = sum[0];
		sum.set(0, temp + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			forall |k:int| 0 <= k < i ==> a[k] == 0,
			forall |k:int| i <= k < N ==> a[k] == 1,
			a.len() == N,
			sum.len() == 1,
			sum[0] == N,
		decreases N - i,
	{
		if (sum[0] == N) {
			let temp = a[i];
			a.set(i, temp - 1);
		} else {
			let temp = a[i];
			a.set(i, temp + 1);
		}
		i = i + 1;
	}
}
}