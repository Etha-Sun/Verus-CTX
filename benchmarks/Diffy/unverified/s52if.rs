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
		sum[0] == 6 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N)
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N)
	{
		if (a[i] == 1) {
			let temp = a[i];
			a.set(i, temp + 5);
		} else {
			let temp = a[i];
			a.set(i, temp - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N)
	{
		if (a[i] == 6)
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