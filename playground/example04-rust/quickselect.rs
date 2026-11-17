#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]

// Check both indices before modifying either slot.
fn exchange(xs: &mut [i64], i: usize, j: usize) -> Option<()> {
    let left = *xs.get(i)?;
    let right = *xs.get(j)?;
    *xs.get_mut(i)? = right;
    *xs.get_mut(j)? = left;
    Some(())
}

fn median3(xs: &[i64], a: usize, b: usize, c: usize) -> Option<usize> {
    let ab = xs.get(a)? < xs.get(b)?;
    let ac = xs.get(a)? < xs.get(c)?;
    if ab != ac {
        return Some(a);
    }
    let bc = xs.get(b)? < xs.get(c)?;
    Some(if bc == ab { b } else { c })
}

// Each start denotes a nonempty block of len elements within xs.
fn pseudo_median3(xs: &[i64], a: usize, b: usize, c: usize, len: usize) -> Option<usize> {
    if len < 9 {
        return median3(xs, a, b, c);
    }
    let sub_len = len / 9;
    // Each child block fits because 9 * sub_len <= len.
    let a = pseudo_median3(xs, a, a + 4 * sub_len, a + 8 * sub_len, sub_len)?;
    let b = pseudo_median3(xs, b, b + 4 * sub_len, b + 8 * sub_len, sub_len)?;
    let c = pseudo_median3(xs, c, c + 4 * sub_len, c + 8 * sub_len, sub_len)?;
    median3(xs, a, b, c)
}

fn choose_pivot(xs: &[i64]) -> Option<usize> {
    let len = xs.len();
    if len < 9 {
        return Some(0);
    }
    let sub_len = len / 9;
    pseudo_median3(xs, 0, 4 * sub_len, 8 * sub_len, sub_len)
}

fn partition_hoare(xs: &mut [i64], p: usize) -> Option<usize> {
    exchange(xs, 0, p)?;
    let (pivot, rest) = xs.split_first_mut()?;
    let mut i = 0;
    let mut j = rest.len();
    loop {
        while i < j && *rest.get(i)? < *pivot {
            i += 1;
        }
        while i < j && *pivot < *rest.get(j - 1)? {
            j -= 1;
        }
        if i >= j {
            break;
        }
        j -= 1;
        exchange(rest, i, j)?;
        i += 1;
    }
    exchange(xs, 0, i)?;
    Some(i)
}

fn select(mut xs: &mut [i64], mut idx: usize) -> Option<()> {
    if idx >= xs.len() {
        return None;
    }
    loop {
        // The active slice stays nonempty and idx stays within it.
        let p = choose_pivot(xs)?;
        let p = partition_hoare(xs, p)?;
        if idx < p {
            xs = xs.get_mut(..p)?;
        } else if idx == p {
            return Some(());
        } else {
            xs = xs.get_mut(p + 1..)?;
            idx -= p + 1;
        }
    }
}

/// Perform Hoare Quickselect on a valid i64 array with signed comparison.
///
/// # Safety
///
/// data must point to len initialized, aligned i64 values in a single
/// allocation, exclusively accessible for the duration of the call. The
/// byte length must fit in isize. The Quickselect contract requires idx < len.
#[no_mangle]
pub unsafe extern "C" fn quickselect_hoare_i64(data: *mut i64, len: usize, idx: usize) {
    // SAFETY: the caller supplies the buffer described above.
    let xs = unsafe { core::slice::from_raw_parts_mut(data, len) };
    let _ = select(xs, idx);
}
