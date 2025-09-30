// Source:
// [curve25519-dalek](https://docs.rs/curve25519-dalek/latest/src/curve25519_dalek/backend/serial/u64/field.rs.html#288)

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


/// _Clamps_ the given little-endian representation of a 32-byte integer. Clamping the value puts
/// it in the range:
///
/// **n ∈ 2^254 + 8\*{0, 1, 2, 3, . . ., 2^251 − 1}**
///
/// # Explanation of clamping
///
/// For Curve25519, h = 8, and multiplying by 8 is the same as a binary left-shift by 3 bits.
/// If you take a secret scalar value between 2^251 and 2^252 – 1 and left-shift by 3 bits
/// then you end up with a 255-bit number with the most significant bit set to 1 and
/// the least-significant three bits set to 0.
///
/// The Curve25519 clamping operation takes **an arbitrary 256-bit random value** and
/// clears the most-significant bit (making it a 255-bit number), sets the next bit, and then
/// clears the 3 least-significant bits. In other words, it directly creates a scalar value that is
/// in the right form and pre-multiplied by the cofactor.
///
/// See [here](https://neilmadden.blog/2020/05/28/whats-the-curve25519-clamping-all-about/) for
/// more details.
#[must_use]
pub const fn clamp_integer(mut bytes: [u8; 32]) -> [u8; 32] {
    bytes[0] &= 0b1111_1000;
    bytes[31] &= 0b0111_1111;
    bytes[31] |= 0b0100_0000;
    bytes
}