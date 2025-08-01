pub type Bignum = Vec<u32>;

/// Add a bignum in place, and return the carry.
///
/// We assume the bignums have the same length
pub fn add_with_carry(x: &mut Bignum, y: &Bignum) -> u8 {
    let mut c0 = 0u8;
    let mut i = 0;
    // Remark: we have (and need) the invariant that: c0 <= 1
    while i < x.len() {
        let (sum, c1) = x[i].overflowing_add(c0 as u32);
        let (sum, c2) = sum.overflowing_add(y[i]);
        // We have: c1 as u8 + c2 as u8 <= 1
        c0 = (c1 as u8 + c2 as u8) as u8;
        x[i] = sum;
        i += 1;
    }
    c0
}
