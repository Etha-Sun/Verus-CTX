use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 3 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			forall |j: int| 0<= j < i ==> a[j] == 1,
			a.len() == N,
		decreases N - i,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			forall |j: int| 0<= j < i ==> a[j] == 3,
			forall |j: int| i <= j < N ==> a[j] == 1,
			a.len() == N,
		decreases N - i,
	{
		if (a[i] == 1) {
			let temp = a[i];
			a.set(i, temp + 2);
		} else {
			let temp = a[i];
			a.set(i, temp - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			forall |j: int| 0<= j < N ==> a[j] == 3,
			sum.len() == 1,
			sum[0] == 3 * i,
			N <= 1000,
			a.len() == N,
		decreases N - i,
	{
		let temp = sum[0];
		sum.set(0, temp + a[i]);
		i = i + 1;
	}
}
}