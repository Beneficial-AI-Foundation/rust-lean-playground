// Source:
// [curve25519-dalek](https://docs.rs/curve25519-dalek/latest/src/curve25519_dalek/backend/serial/u64/field.rs.html#288)
// modified to remove `struct` use

pub const LOW_51_BIT_MASK: u64 = 2251799813685247u64; // 2^51  -1

// curve25519-dalek/src/backend/serial/u64/field.rs

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
///     ∃ r, reduce limbs = ok (r) ∧
///     (∀ i, i < 5 → (r[i]!).val ≤ 2^51 + (2^13 - 1) * 19) ∧
///     ArrayU645_to_Nat limbs ≡ ArrayU645_to_Nat r [MOD p] := by
///   FieldElement51.reduce_spec limbs
/// ```
///
/// I.e.,
/// - The function does not overflow and hence returns a result
/// - All the limbs of the result are small, ≤ 2^(51 + ε)
/// - The result is equal to the input mod p.
///
#[inline(always)]
pub fn reduce(mut limbs: [u64; 5]) -> [u64; 5] {
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

    limbs
}
