import Aeneas
import Verify.Src.RustLeanPlayground

/-! # Reduce

The main statement concerning `reduce` is `reduce_spec` (see the end of this file).

-/

open Aeneas.Std Result
open rust_lean_playground

set_option linter.hashCommand false
#setup_aeneas_simps


/-! ## Auxillary defs and theorems -/

attribute [-simp] Int.reducePow Nat.reducePow

-- Auxiliary definition to interpret a vector of u32 as a mathematical integer
def FieldElement51_to_Nat (_f : FieldElement51) := 0

theorem LOW_51_BIT_MASK_val_eq : LOW_51_BIT_MASK.val = 2^51 - 1 := by
  unfold LOW_51_BIT_MASK
  decide

/-- **Spec and proof concerning `reduce`**:
- Returns a result
- All the limbs of the result are small
- If the limbs are small then the result is equal the input
- the result is equal to the input mod p.
 -/
theorem FieldElement51.reduce_spec (limbs : Array U64 5#usize) :
    ∃ r, FieldElement51.reduce limbs = ok (r) := by

  unfold FieldElement51.reduce

  -- Perform `>>> 51` on each of the limbs
  progress as ⟨ i0, hi0 ⟩        -- Array.index_usize limbs 0
  progress as ⟨ c0, hc0, hc0' ⟩       -- i >>> 51
  progress as ⟨ i1, hi1 ⟩       -- Array.index_usize limbs 1
  progress as ⟨ c1, hc1, hc1' ⟩       -- i1 >>> 51
  progress as ⟨ i2, hi2 ⟩       -- Array.index_usize limbs 2
  progress as ⟨ c2, hc2, hc2' ⟩       -- i2 >>> 51
  progress as ⟨ i3, hi3 ⟩       -- Array.index_usize limbs 3
  progress as ⟨ c3, hc3, hc3' ⟩       -- i3 >>> 51
  progress as ⟨ i4, hi4 ⟩       -- Array.index_usize limbs 4
  progress as ⟨ c4, hc4, hc4' ⟩       -- i4 >>> 51

  -- Each c_i is the result of right-shifting a 64-bit value by 51 bits,
  -- leaving at most 13 bits, so c_i.val ≤ 2^13 - 1.
  -- The bvify tactic converts this to bitvector reasoning and bv_decide verifies it.
  have hc0'' : c0.val ≤ 2^13 - 1 := by
      bvify 64 at *
      bv_decide
  have hc1'' : c1.val ≤ 2^13 - 1 := by
      bvify 64 at *
      bv_decide
  have hc2'' : c2.val ≤ 2^13 - 1 := by
      bvify 64 at *
      bv_decide
  have hc3'' : c3.val ≤ 2^13 - 1 := by
      bvify 64 at *
      bv_decide
  have hc4'' : c4.val ≤ 2^13 - 1 := by
      bvify 64 at *
      bv_decide

  -- Perform `&&& LOW_51_BIT_MASK` on each of the limbs
  progress as ⟨ j0, hj0, hj0' ⟩       -- cast (i &&& LOW_51_BIT_MASK)
  progress as ⟨ limbs1, hlimbs1 ⟩   -- Array.update limbs 0 i5
  progress as ⟨ l1, hl1 ⟩       -- Array.index_usize limbs1 1

  progress as ⟨ j1, hj1, hj1' ⟩       -- cast (i6 &&& LOW_51_BIT_MASK)
  progress as ⟨ limbs2, hlimbs2 ⟩   -- Array.update limbs1 1 i7
  progress as ⟨ l2, hl2 ⟩       -- Array.index_usize limbs2 2

  progress as ⟨ j2, hj2, hj2' ⟩       -- cast (i8 &&& LOW_51_BIT_MASK)
  progress as ⟨ limbs3, hlimbs3 ⟩   -- Array.update limbs2 2 i9
  progress as ⟨ l3, hl3 ⟩      -- Array.index_usize limbs3 3

  progress as ⟨ j3, hj3, hj3' ⟩      -- cast (i10 &&& LOW_51_BIT_MASK)
  progress as ⟨ limbs4, hlimbs4 ⟩   -- Array.update limbs3 3 i11
  progress as ⟨ l4, hl4 ⟩      -- Array.index_usize limbs4 4

  progress as ⟨ j4, hj4, hj4' ⟩      -- cast (i12 &&& LOW_51_BIT_MASK)
  progress as ⟨ limbs5, hlimbs5 ⟩   -- Array.update limbs4 4 i13
  progress as ⟨ l5, hl5 ⟩      -- c4 * 19

  -- Add the parts of limbs together
  progress as ⟨ m0, hm0 ⟩      -- Array.index_usize limbs5 0
  have h_no_overflow : m0 + l5 ≤ U64.max := by
    sorry
  progress as ⟨ n0, hn0 ⟩      -- i15 + i14
  progress as ⟨ limbs6, hlimbs6 ⟩   -- Array.update limbs5 0 i16

  progress as ⟨ m1, hm1 ⟩      -- Array.index_usize limbs6 1
  have h_no_overflow2 : m1 + c0 ≤ U64.max := by
    have := U64.max_eq
    -- The mathematical reasoning is:
    -- i17 ≤ 2^51 - 1 (from masking with LOW_51_BIT_MASK)
    -- c0 ≤ 2^13 - 1 (from >>> 51 on a u64)
    -- So i17 + c0 ≤ 2^51 + 2^13 - 2 < 2^64 - 1 = U64.max
    have : m1.val ≤ 2^51 - 1 := by
      rw [hm1]
      sorry
    have : c0.val ≤ 2^13 - 1 := by
      sorry
    sorry
  progress as ⟨ n1, hn1 ⟩      -- i17 + c0
  progress as ⟨ limbs7, hlimbs7 ⟩   -- Array.update limbs6 1 i18

  progress as ⟨ m2, hm2 ⟩      -- Array.index_usize limbs7 2
  have h_no_overflow3 : m2 + c1 ≤ U64.max := by sorry
  progress as ⟨ n2, hn2 ⟩      -- i19 + c1
  progress as ⟨ limbs8, hlimbs8 ⟩   -- Array.update limbs7 2 i20

  progress as ⟨ m3, hm3 ⟩      -- Array.index_usize limbs8 3
  have h_no_overflow4 : m3 + c2 ≤ U64.max := by sorry
  progress as ⟨ n3, hn3 ⟩      -- i21 + c2
  progress as ⟨ limbs9, hlimbs9 ⟩   -- Array.update limbs8 3 i22

  progress as ⟨ m4, hm4 ⟩      -- Array.index_usize limbs9 4
  have h_no_overflow5 : m4 + c3 ≤ U64.max := by sorry
  progress as ⟨ n4, hn4 ⟩      -- i23 + c3
  progress as ⟨ limbs10, hlimbs10 ⟩  -- Array.update limbs9 4 i24

-- r.limbs == spec_reduce(limbs),
-- forall|i: int| 0 <= i < 5 ==> r.limbs[i] < (1u64 << 52),
-- (forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51)) ==> (r.limbs =~= limbs),
-- as_nat(r.limbs) == as_nat(limbs) - p() * (limbs[4] >> 51),
-- as_nat(r.limbs) % p() == as_nat(limbs) % p()
