pub type Bignum = Vec<u32>;

/// Add a bignum (`Vec<u32>`) in place, and return the carry.
///
/// We consider the bignum to be a little endian representation,
/// i.e., the first element is the least significant.
/// For adding we assume the bignums have the same length
///
/// ## Spec:
///
/// If we define:
/// ```lean
/// def toInt (l : List U32) : Int :=
///  match l with
///  | [] => 0
///  | x :: l =>
///    x + 2 ^ 32 * toInt l
///```
/// Then the function satisfies:
///
/// ```lean
/// example (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (hLength : x.length = y.length) :
///     ∃ x' c, add_with_carry x y = ok (c, x') ∧
///     x'.length = x.length ∧
///     c.val ≤ 1 ∧
///     toInt x' + c.val * 2 ^ (32 * x'.length) = toInt x + toInt y :=
///   add_with_carry_spec
///  ```
///
/// I.e.,
/// Assume that:
/// - `x` has the same length as `y`
///   Then:
/// - `add_with_carry x y` returns ok with result `c` and `x'`, updated value of `x`
/// - `x'` has the same length as `x`
/// - `c.val ≤ 1`
/// - `toInt x' + c.val * 2 ^ (32 * x'.length) = toInt x + toInt y`.  
///
pub fn add_with_carry(x: &mut Bignum, y: &Bignum) -> u8 {
    let mut c0 = 0u8;
    let mut i = 0;
    // Remark: we have (and need) the invariant that: c0 <= 1
    while i < x.len() {
        let (sum, c1) = x[i].overflowing_add(c0 as u32);
        let (sum, c2) = sum.overflowing_add(y[i]);
        // We have: c1 as u8 + c2 as u8 <= 1
        c0 = c1 as u8 + c2 as u8;
        x[i] = sum;
        i += 1;
    }
    c0
}
