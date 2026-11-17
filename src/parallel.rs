//! Parallel arithmetic is deterministic over Fr; transcript ordering and all
//! private-coin sampling remain sequential. Small jobs avoid pool overhead.
use ark_bls12_381::Fr;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub fn sum_indices<F>(len: usize, f: F) -> Fr
where
    F: Fn(usize) -> Fr + Sync + Send,
{
    #[cfg(feature = "parallel")]
    if len >= 1024 && rayon::current_num_threads() > 1 {
        return (0..len).into_par_iter().map(f).sum();
    }
    (0..len).map(f).sum()
}

pub fn fold_pairs(values: &mut [Fr], coordinate: Fr, difference: Option<&mut [Fr]>) {
    let half = values.len() / 2;
    let (lower, upper) = values.split_at_mut(half);
    if let Some(difference) = difference {
        assert_eq!(difference.len(), half);
        #[cfg(feature = "parallel")]
        if half >= 4096 && rayon::current_num_threads() > 1 {
            lower
                .par_iter_mut()
                .zip(upper.par_iter())
                .zip(difference.par_iter_mut())
                .for_each(|((a, b), d)| {
                    *d = *b - *a;
                    *a += coordinate * *d;
                });
            return;
        }
        for ((a, b), d) in lower.iter_mut().zip(upper).zip(difference) {
            *d = *b - *a;
            *a += coordinate * *d;
        }
    } else {
        #[cfg(feature = "parallel")]
        if half >= 4096 && rayon::current_num_threads() > 1 {
            lower
                .par_iter_mut()
                .zip(upper.par_iter())
                .for_each(|(a, b)| *a += coordinate * (*b - *a));
            return;
        }
        for (a, b) in lower.iter_mut().zip(upper) {
            *a += coordinate * (*b - *a);
        }
    }
}
