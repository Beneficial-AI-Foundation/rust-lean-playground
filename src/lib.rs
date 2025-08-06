// From: https://github.com/AeneasVerif/aeneas/blob/3bf9aeecddb2600d788435bc83a6b84c6bdf054f/tests/src/tutorial/src/lib.rs#L186
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
/// 
/// Then the function satisfies:
/// ```lean
/// example (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (hLength : x.length = y.length) :
///     ∃ x' c, add_with_carry x y = ok (c, x') ∧
///     x'.length = x.length ∧
///     c.val ≤ 1 ∧
///     toInt x' + c.val * 2 ^ (32 * x'.length) = toInt x + toInt y :=
///   add_with_carry_spec
/// ```
///
/// I.e., if:
/// - `x` has the same length as `y`
///
/// Then:
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

// -----------------------------------------------------------------------//
// Source:
// [curve25519-dalek](https://docs.rs/curve25519-dalek/latest/src/curve25519_dalek/backend/serial/u64/field.rs.html#288)

// pub const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1;
pub const LOW_51_BIT_MASK: u64 = 2251799813685247u64; // 2^51  -1
pub struct FieldElement51 {
    pub limbs: [u64; 5],
}

// curve25519-dalek/src/backend/serial/u64/field.rs
impl FieldElement51 {
    /// Given 64-bit input limbs, reduce to enforce the bound 2^(51 + epsilon).
    /// 
    /// ## Spec:
    /// 
    /// If we define:
    /// ```lean
    /// def ArrayU645_to_Nat (limbs : Array U64 5#usize) : Nat :=
    ///   ∑ i ∈ Finset.range 5, 2^(51 * i) * (limbs[i]!).val
    /// 
    /// def p : Nat := 2^255 - 19
    /// ```
    /// 
    /// Then the function satisfies:
    /// ```lean
    /// example (limbs : Array U64 5#usize) :
    ///     ∃ r, FieldElement51.reduce limbs = ok (r) ∧
    ///     (∀ i, i < 5 → (r.limbs[i]!).val ≤ 2^51 + (2^13 - 1) * 19) ∧
    ///     ArrayU645_to_Nat limbs ≡ ArrayU645_to_Nat r.limbs [MOD p] := 
    ///   FieldElement51.reduce_spec limbs
    /// ```
    /// 
    /// I.e.,
    /// - The function does not overflow and hence returns a result
    /// - All the limbs of the result are small, ≤ 2^(51 + ε)
    /// - The result is equal to the input mod p.
    /// 
    #[inline(always)]
    pub fn reduce(mut limbs: [u64; 5]) -> FieldElement51 {
        // Since the input limbs are bounded by 2^64, the biggest
        // carry-out is bounded by 2^13.
        //
        // The biggest carry-in is c4 * 19, resulting in
        //
        // 2^51 + 19*2^13 < 2^51.0000000001
        //
        // Because we don't need to canonicalize, only to reduce the
        // limb sizes, it's OK to do a "weak reduction", where we
        // compute the carry-outs in parallel.

        let c0 = limbs[0] >> 51;
        let c1 = limbs[1] >> 51;
        let c2 = limbs[2] >> 51;
        let c3 = limbs[3] >> 51;
        let c4 = limbs[4] >> 51;

        limbs[0] &= LOW_51_BIT_MASK;
        limbs[1] &= LOW_51_BIT_MASK;
        limbs[2] &= LOW_51_BIT_MASK;
        limbs[3] &= LOW_51_BIT_MASK;
        limbs[4] &= LOW_51_BIT_MASK;

        limbs[0] += c4 * 19;
        limbs[1] += c0;
        limbs[2] += c1;
        limbs[3] += c2;
        limbs[4] += c3;

        FieldElement51 { limbs }
    }
}
