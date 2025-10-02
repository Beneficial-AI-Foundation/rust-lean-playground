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

/// The scalar \\( 0 \\).
pub const ZERO: [u64; 5] = [0, 0, 0, 0, 0];

/// Pack the limbs into 32 bytes
#[rustfmt::skip] // keep alignment of s[*] calculations
#[allow(clippy::identity_op)]
pub fn to_bytes(limbs: [u64; 5]) -> [u8; 32] {
    let mut s = [0u8; 32];

    s[ 0] =  (limbs[ 0] >>  0)                      as u8;
    s[ 1] =  (limbs[ 0] >>  8)                      as u8;
    s[ 2] =  (limbs[ 0] >> 16)                      as u8;
    s[ 3] =  (limbs[ 0] >> 24)                      as u8;
    s[ 4] =  (limbs[ 0] >> 32)                      as u8;
    s[ 5] =  (limbs[ 0] >> 40)                      as u8;
    s[ 6] = ((limbs[ 0] >> 48) | (limbs[ 1] << 4)) as u8;
    s[ 7] =  (limbs[ 1] >>  4)                      as u8;
    s[ 8] =  (limbs[ 1] >> 12)                      as u8;
    s[ 9] =  (limbs[ 1] >> 20)                      as u8;
    s[10] =  (limbs[ 1] >> 28)                      as u8;
    s[11] =  (limbs[ 1] >> 36)                      as u8;
    s[12] =  (limbs[ 1] >> 44)                      as u8;
    s[13] =  (limbs[ 2] >>  0)                      as u8;
    s[14] =  (limbs[ 2] >>  8)                      as u8;
    s[15] =  (limbs[ 2] >> 16)                      as u8;
    s[16] =  (limbs[ 2] >> 24)                      as u8;
    s[17] =  (limbs[ 2] >> 32)                      as u8;
    s[18] =  (limbs[ 2] >> 40)                      as u8;
    s[19] = ((limbs[ 2] >> 48) | (limbs[ 3] << 4)) as u8;
    s[20] =  (limbs[ 3] >>  4)                      as u8;
    s[21] =  (limbs[ 3] >> 12)                      as u8;
    s[22] =  (limbs[ 3] >> 20)                      as u8;
    s[23] =  (limbs[ 3] >> 28)                      as u8;
    s[24] =  (limbs[ 3] >> 36)                      as u8;
    s[25] =  (limbs[ 3] >> 44)                      as u8;
    s[26] =  (limbs[ 4] >>  0)                      as u8;
    s[27] =  (limbs[ 4] >>  8)                      as u8;
    s[28] =  (limbs[ 4] >> 16)                      as u8;
    s[29] =  (limbs[ 4] >> 24)                      as u8;
    s[30] =  (limbs[ 4] >> 32)                      as u8;
    s[31] =  (limbs[ 4] >> 40)                      as u8;

    s
}

/// u64 * u64 = u128 multiply helper
#[inline(always)]
fn m(x: u64, y: u64) -> u128 {
    (x as u128) * (y as u128)
}

/// Compute `a * b`
#[inline(always)]
#[rustfmt::skip] // keep alignment of z[*] calculations
pub fn mul_internal(a: &[u64; 5], b: &[u64; 5]) -> [u128; 9] {
    let mut z = [0u128; 9];

    z[0] = m(a[0], b[0]);
    z[1] = m(a[0], b[1]) + m(a[1], b[0]);
    z[2] = m(a[0], b[2]) + m(a[1], b[1]) + m(a[2], b[0]);
    z[3] = m(a[0], b[3]) + m(a[1], b[2]) + m(a[2], b[1]) + m(a[3], b[0]);
    z[4] = m(a[0], b[4]) + m(a[1], b[3]) + m(a[2], b[2]) + m(a[3], b[1]) + m(a[4], b[0]);
    z[5] =                 m(a[1], b[4]) + m(a[2], b[3]) + m(a[3], b[2]) + m(a[4], b[1]);
    z[6] =                                 m(a[2], b[4]) + m(a[3], b[3]) + m(a[4], b[2]);
    z[7] =                                                 m(a[3], b[4]) + m(a[4], b[3]);
    z[8] =                                                                 m(a[4], b[4]);

    z
}

/// Compute `a^2`
#[inline(always)]
#[rustfmt::skip] // keep alignment of return calculations
pub fn square_internal(a: &[u64; 5]) -> [u128; 9] {
    let aa = [
        a[0] * 2,
        a[1] * 2,
        a[2] * 2,
        a[3] * 2,
    ];

    [
        m( a[0], a[0]),
        m(aa[0], a[1]),
        m(aa[0], a[2]) + m( a[1], a[1]),
        m(aa[0], a[3]) + m(aa[1], a[2]),
        m(aa[0], a[4]) + m(aa[1], a[3]) + m( a[2], a[2]),
                            m(aa[1], a[4]) + m(aa[2], a[3]),
                                            m(aa[2], a[4]) + m( a[3], a[3]),
                                                            m(aa[3], a[4]),
                                                                            m(a[4], a[4])
    ]
}


// from: curve25519-dalek/src/field.rs
//    /// Determine if this `FieldElement` is negative, in the sense
//     /// used in the ed25519 paper: `x` is negative if the low bit is
//     /// set.
//     ///
//     /// # Return
//     ///
//     /// If negative, return `Choice(1)`.  Otherwise, return `Choice(0)`.
//     pub(crate) fn is_negative(&self) -> Choice {
//         let bytes = self.to_bytes();
//         (bytes[0] & 1).into()
//     }


// impl<'a> Sub<&'a FieldElement51> for &FieldElement51 {
//     type Output = FieldElement51;
//     fn sub(self, _rhs: &'a FieldElement51) -> FieldElement51 {
//         // To avoid underflow, first add a multiple of p.
//         // Choose 16*p = p << 4 to be larger than 54-bit _rhs.
//         //
//         // If we could statically track the bitlengths of the limbs
//         // of every FieldElement51, we could choose a multiple of p
//         // just bigger than _rhs and avoid having to do a reduction.
//         //
//         // Since we don't yet have type-level integers to do this, we
//         // have to add an explicit reduction call here.
//         FieldElement51::reduce([
//             (self.0[0] + 36028797018963664u64) - _rhs.0[0],
//             (self.0[1] + 36028797018963952u64) - _rhs.0[1],
//             (self.0[2] + 36028797018963952u64) - _rhs.0[2],
//             (self.0[3] + 36028797018963952u64) - _rhs.0[3],
//             (self.0[4] + 36028797018963952u64) - _rhs.0[4],
//         ])
//     }
// }

// /// Load a `FieldElement51` from the low 255 bits of a 256-bit
// /// input.
// ///
// /// # Warning
// ///
// /// This function does not check that the input used the canonical
// /// representative.  It masks the high bit, but it will happily
// /// decode 2^255 - 18 to 1.  Applications that require a canonical
// /// encoding of every field element should decode, re-encode to
// /// the canonical encoding, and check that the input was
// /// canonical.
// ///
// #[rustfmt::skip] // keep alignment of bit shifts
// pub const fn from_bytes(bytes: &[u8; 32]) -> FieldElement51 {
//     const fn load8_at(input: &[u8], i: usize) -> u64 {
//            (input[i] as u64)
//         | ((input[i + 1] as u64) << 8)
//         | ((input[i + 2] as u64) << 16)
//         | ((input[i + 3] as u64) << 24)
//         | ((input[i + 4] as u64) << 32)
//         | ((input[i + 5] as u64) << 40)
//         | ((input[i + 6] as u64) << 48)
//         | ((input[i + 7] as u64) << 56)
//     }

//     let low_51_bit_mask = (1u64 << 51) - 1;
//     FieldElement51(
//     // load bits [  0, 64), no shift
//     [  load8_at(bytes,  0)        & low_51_bit_mask
//     // load bits [ 48,112), shift to [ 51,112)
//     , (load8_at(bytes,  6) >>  3) & low_51_bit_mask
//     // load bits [ 96,160), shift to [102,160)
//     , (load8_at(bytes, 12) >>  6) & low_51_bit_mask
//     // load bits [152,216), shift to [153,216)
//     , (load8_at(bytes, 19) >>  1) & low_51_bit_mask
//     // load bits [192,256), shift to [204,112)
//     , (load8_at(bytes, 24) >> 12) & low_51_bit_mask
//     ])
// }
