import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib
import Verify.Proofs.Aux
import Verify.Proofs.Defs

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

/-! # ToBytes

Much of the proof and aux lemmas due to Son Ho.

The main statement concerning `to_bytes` is `to_bytes_spec` (below).
-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `to_bytes` -/

/- Using the specs with bit-vectors -/
--attribute [-progress] U64.add_spec U64.mul_spec U8.add_spec U8.mul_spec
--attribute [local progress] U64.add_bv_spec U64.mul_bv_spec U8.add_bv_spec U8.mul_bv_spec

-- TODO: generalize and add to the standard library
@[local simp]
theorem U64_cast_U8 (x : U64) : (UScalar.cast UScalarTy.U8 x).val = x.val % 2^8 := by
  simp only [UScalar.cast, UScalarTy.U64_numBits_eq, UScalarTy.U8_numBits_eq,
    Aeneas.Bvify.U64.UScalar_bv, BitVec.truncate_eq_setWidth]
  simp only [UScalar.val]
  simp only [UScalarTy.U8_numBits_eq, BitVec.toNat_setWidth, UScalar.bv_toNat,
    UScalarTy.U64_numBits_eq, Aeneas.Bvify.U64.UScalar_bv]

-- This is specific to the problem below
theorem recompose_decomposed_limb (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val =
  limb.val % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 8 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 16 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 24 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 32 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 40 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 48 % 2 ^ 8)
  := by
  bvify 64 at *
  bv_decide

-- TODO: move to standard library
attribute [simp_scalar_simps] BitVec.toNat_shiftLeft

-- We also need something like this
theorem recompose_decomposed_limb_split (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 4 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 4 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 12 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 20 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 28 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 36 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 44 % 2 ^ 8) =
  2 ^ 4 * limb.val
  := by
  bvify 64 at *
  /- Small trick when bvify doesn't work: we can prove the property we
     want about bit-vectors, then convert it back to natural numbers with
     `natify` and `simp_scalar`. In particular, `simp_scalar` is good at simplifying
     things like `x % 2 ^ 32` when `x < 2^32`, etc. -/
  have : BitVec.ofNat 64 (limb.val <<< 4) = limb.bv <<< 4 := by
    natify
    simp_scalar
  simp [this]
  bv_decide

-- This is specific to the problem below
theorem decompose_or_limbs (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 48 ||| limb1.val <<< 4 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 48 % 2 ^ 8) +
  ((limb1.val <<< 4) % 2 ^ 8) := by
  bvify 64 at *
  -- The idea is to do something similar to the proof above

  sorry

/-- **Spec for `to_bytes`**:
- Does not overflow and hence returns a result
- The result byte array represents the same natural number as the input limbs -/
theorem to_bytes_spec (limbs : Array U64 5#usize)
    (h : ∀ i, (h : i < 5) → (getElem limbs.val i (by scalar_tac)).val < 2 ^ 51) :
    ∃ result, to_bytes limbs = ok (result) ∧
    U8x32_as_Nat result = U64x5_as_Nat limbs := by
  unfold to_bytes
  progress*
  -- remains to show that `U8x32_as_Nat result = U64x5_as_Nat limbs`
  simp [Finset.sum_range_succ, Nat.ModEq, *]
  -- We need those
  have h0 := h 0 (by simp)
  have h1 := h 1 (by simp)
  have h2 := h 2 (by simp)
  have h3 := h 3 (by simp)
  have h4 := h 4 (by simp)
  -- Decompose the rhs (we also need to decompose limbs[1], etc.)
  conv =>
    rhs;
    rw [recompose_decomposed_limb (limbs.val[0]) (h0)];
    -- rw [recompose_decomposed_limb (limbs.val[1]) (h1)];
    -- rw [recompose_decomposed_limb (limbs.val[2]) (h2)];
    -- rw [recompose_decomposed_limb (limbs.val[3]) (h3)];
    -- rw [recompose_decomposed_limb (limbs.val[4]) (h4)];



  -- Simplify the lhs with the rhs
  simp [add_assoc, mul_add, decompose_or_limbs (limbs.val[0]) (limbs.val[1]) (h0)]




  -- rw [← recompose_decomposed_limb_split]

  -- I think the spec is wrong: on the RHS we have 2^51 * limbs[1] while
  -- we should have 2^52
  sorry
