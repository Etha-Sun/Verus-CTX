use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 5 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N)
		invariant
			forall |k:int| 0<= k < i ==> a[k] == 1,
			a.len() == N,
		decreases N - i,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N)
		invariant
			forall |k:int| 0<= k < i ==> a[k] == 5,
			forall |k:int| i<= k < N ==> a[k] == 1,
			a.len() == N,
		decreases N - i,
	{
		if (a[i] == 1) {
			let temp = a[i];
			a.set(i, temp + 4);
		} else {
			let temp = a[i];
			a.set(i, temp - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N)
		invariant
			i <= N,
			forall |k:int| 0<= k < N ==> a[k] == 5,
			a.len() == N,
			sum[0] == 5 * i,
			sum.len() == 1,
			N < 1000,
		decreases N - i,
	{
		if (a[i] == 5)
		{
			let temp = sum[0];
			sum.set(0, temp + a[i]);
		} else {
			let temp = sum[0];
			sum.set(0, temp * a[i]);
		}
		i = i + 1;
	}
}
}