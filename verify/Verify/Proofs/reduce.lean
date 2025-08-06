import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib

/-! # Reduce

The main statement concerning `FieldElement51.reduce` is `FieldElement51.reduce_spec` (below).

-/

open Aeneas.Std Result
open rust_lean_playground

-- set_option linter.hashCommand false
-- #setup_aeneas_simps
attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Auxillary defs and theorems -/

-- Auxiliary definition to interpret a vector of u32 as a mathematical integer
def ArrayU645_to_Nat (limbs : Array U64 5#usize) : Nat :=
  ∑ i : Fin 5, 2^(51 * i.val) * (limbs[i.val]!).val

-- Auxiliary definition to interpret a `FieldElement51` as a mathematical integer
def rust_lean_playground.FieldElement51.to_Nat (f : FieldElement51) := ArrayU645_to_Nat f.limbs

-- curve25519 is the elliptic curve over the prime field with order p
def p : Nat := 2^255 - 19

theorem LOW_51_BIT_MASK_val_eq : LOW_51_BIT_MASK.val = 2^51 - 1 := by
  unfold LOW_51_BIT_MASK
  decide

theorem LOW_51_BIT_MASK_bv_eq : LOW_51_BIT_MASK.bv = 2251799813685247#64 := by
  unfold LOW_51_BIT_MASK
  decide

-- Bitwise AND with (2^51 - 1) keeps only the lower 51 bits so bounded ≤ 2^51 - 1 < 2^51
theorem and_LOW_51_BIT_MASK_le (a : U64) : (a &&& LOW_51_BIT_MASK).val ≤ LOW_51_BIT_MASK.val := by
  -- Bitwise AND with a mask is always ≤ the mask
  bvify 64 at *
  bv_decide

-- Bitwise AND with (2^51 - 1) keeps only the lower 51 bits so bounded ≤ 2^51 - 1 < 2^51
theorem and_LOW_51_BIT_MASK_lt (a : U64) : (a &&& LOW_51_BIT_MASK).val < 2^51 := by
  have h1 := and_LOW_51_BIT_MASK_le a
  rw [LOW_51_BIT_MASK_val_eq] at h1
  omega

-- right-shifting a 64-bit value by 51 bits leaves at most 13 bits so bounded by 2^13 - 1.
theorem U64_shiftRight_le (a : U64) : a.val >>> 51 ≤ 2 ^ 13 - 1 := by
  bvify 64 at *
  bv_decide

-- @[simp]
-- theorem Array.set_apply (bs : Array U64 5#usize) (a : U64) (i : Nat) (h : i < 5) :
--     (bs.set i#usize a)[i]! = a := by
--   rw [Array.getElem!_Nat_eq, Array.set_val_eq]
--   simp_lists

theorem Array.val_getElem!_eq' (bs : Array U64 5#usize) (i : Nat) (h : i < bs.length) :
    (bs.val)[i]! = bs[i] := by
  simpa [Subtype.val] using getElem!_pos bs.val i _

@[simp]
theorem Array.set_of_ne (bs : Array U64 5#usize) (a : U64) (i j : Nat) (hi : i < bs.length)
    (hj : j < bs.length) (h : i ≠ j) :
    (bs.set j#usize a)[i]! = bs[i] := by
  rw [Array.getElem!_Nat_eq, Array.set_val_eq, ← Array.val_getElem!_eq' bs i hi]
  exact List.getElem!_set_ne bs j i a (by omega)

/-! ## Spec for `FieldElement51.reduce` -/

/-- **Spec and proof concerning `reduce`**:
- Does not overflow and hence returns a result
- All the limbs of the result are small, < (1u64 << 52)
- the result is equal to the input mod p. -/
theorem FieldElement51.reduce_spec (limbs : Array U64 5#usize) :
    ∃ r, FieldElement51.reduce limbs = ok (r) ∧
    (∀ i, i < 5 → (r.limbs[i]!).val ≤ 2^51 + (2^13 - 1) * 19) ∧
    ArrayU645_to_Nat limbs ≡ ArrayU645_to_Nat r.limbs [MOD p] := by
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

  -- Right-shifting a 64-bit value by 51 bits leaves at most 13 bits so bounded by 2^13 - 1.
  have hc0'' : c0.val ≤ 2^13 - 1 := by simp [hc0, U64_shiftRight_le]
  have hc1'' : c1.val ≤ 2^13 - 1 := by simp [hc1, U64_shiftRight_le]
  have hc2'' : c2.val ≤ 2^13 - 1 := by simp [hc2, U64_shiftRight_le]
  have hc3'' : c3.val ≤ 2^13 - 1 := by simp [hc3, U64_shiftRight_le]
  have hc4'' : c4.val ≤ 2^13 - 1 := by simp [hc4, U64_shiftRight_le]

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

  -- Bitwise AND with (2^51 - 1) keeps only the lower 51 bits
  -- So j_i.val ≤ 2^51 - 1 < 2^51 for all i
  have hj0'' : j0.val < 2^51 := by
    simpa [hj0] using and_LOW_51_BIT_MASK_lt i0

  have hj1'' : j1.val < 2^51 := by
    simpa [hj1] using and_LOW_51_BIT_MASK_lt l1

  have hj2'' : j2.val < 2^51 := by
    simpa [hj2] using and_LOW_51_BIT_MASK_lt l2

  have hj3'' : j3.val < 2^51 := by
    simpa [hj3] using and_LOW_51_BIT_MASK_lt l3

  have hj4'' : j4.val < 2^51 := by
    simpa [hj4] using and_LOW_51_BIT_MASK_lt l4

  -- Check for no overflow prior to adding
  have h_no_overflow0 : j0 + l5 ≤ U64.max := by
    rw [U64.max_eq, hl5]
    -- have : j0.val + c4.val * 19 ≤ 2^51 + (2^13 - 1) * 19 := by omega
    omega

  have h_no_overflow1 : j1 + c0 ≤ U64.max := by
    rw [U64.max_eq]
    -- have : j1.val + c0.val ≤ 2^51 + 2^13 - 1 := by omega
    omega

  have h_no_overflow2 : j2 + c1 ≤ U64.max := by
    rw [U64.max_eq]
    -- have : j2.val + c1.val ≤ 2^51 + 2^13 - 1 := by omega
    omega

  have h_no_overflow3 : j3 + c2 ≤ U64.max := by
    rw [U64.max_eq]
    -- have : j3.val + c2.val ≤ 2^51 + 2^13 - 1 := by omega
    omega

  have h_no_overflow4 : j4 + c3 ≤ U64.max := by
    rw [U64.max_eq]
    -- have : j4.val + c3.val ≤ 2^51 + 2^13 - 1 := by omega
    omega

  -- Add the parts of limbs together
  progress as ⟨ m0, hm0 ⟩      -- Array.index_usize limbs5 0
  have hm0' : m0 = j0 := by -- tracking through array updates
    simp [hm0, hlimbs5, hlimbs4, hlimbs3, hlimbs2, hlimbs1]
  have : m0 + l5 ≤ U64.max := by simpa [hm0']
  progress as ⟨ n0, hn0 ⟩      -- i15 + i14
  progress as ⟨ limbs6, hlimbs6 ⟩   -- Array.update limbs5 0 i16

  progress as ⟨ m1, hm1 ⟩      -- Array.index_usize limbs6 1
  have hm1' : m1 = j1 := by -- tracking through array updates
    simp [hm1, hlimbs6, hlimbs5, hlimbs4, hlimbs3, hlimbs2, hlimbs1]
  have : m1 + c0 ≤ U64.max := by simpa [hm1']
  progress as ⟨ n1, hn1 ⟩      -- i17 + c0
  progress as ⟨ limbs7, hlimbs7 ⟩   -- Array.update limbs6 1 i18

  progress as ⟨ m2, hm2 ⟩      -- Array.index_usize limbs7 2
  have hm2' : m2 = j2 := by -- tracking through array updates
    simp [hm2, hlimbs7, hlimbs6, hlimbs5, hlimbs4, hlimbs3, hlimbs2]
  have : m2 + c1 ≤ U64.max := by simpa [hm2']
  progress as ⟨ n2, hn2 ⟩      -- i19 + c1
  progress as ⟨ limbs8, hlimbs8 ⟩   -- Array.update limbs7 2 i20

  progress as ⟨ m3, hm3 ⟩      -- Array.index_usize limbs8 3
  have hm3' : m3 = j3 := by -- tracking through array updates
    simp [hm3, hlimbs8, hlimbs7, hlimbs6, hlimbs5, hlimbs4, hlimbs3]
  have : m3 + c2 ≤ U64.max := by simpa [hm3']
  progress as ⟨ n3, hn3 ⟩      -- i21 + c2
  progress as ⟨ limbs9, hlimbs9 ⟩   -- Array.update limbs8 3 i22

  progress as ⟨ m4, hm4 ⟩      -- Array.index_usize limbs9 4
  have hm4' : m4 = j4 := by -- tracking through array updates
    simp [hm4, hlimbs9, hlimbs8, hlimbs7, hlimbs6, hlimbs5, hlimbs4]
  have : m4 + c3 ≤ U64.max := by simpa [hm4']
  progress as ⟨ n4, hn4 ⟩      -- i23 + c3
  progress as ⟨ limbs10, hlimbs10 ⟩  -- Array.update limbs9 4 i24

  refine ⟨fun i hi ↦ ?_, ?_⟩

  -- Prove upper bounds on each limb of the result
  · interval_cases i
    · -- Case i = 0
      have : j0.val + c4.val * 19 ≤ 2^51 + (2^13 - 1) * 19 := by omega
      simpa [hlimbs10, hlimbs9, hlimbs8, hlimbs7, hlimbs6, hn0, hm0', hl5]
    · -- Case i = 1
      have : j1.val + c0.val ≤ 2^51 + (2^13 - 1) * 19 := by omega
      simpa [hlimbs10, hlimbs9, hlimbs8, hlimbs7, hn1, hm1']
    · -- Case i = 2
      have : j2.val + c1.val ≤ 2^51 + (2^13 - 1) * 19 := by omega
      simpa [hlimbs10, hlimbs9, hlimbs8, hn2, hm2']
    · -- Case i = 3
      have : j3.val + c2.val ≤ 2^51 + (2^13 - 1) * 19 := by omega
      simpa [hlimbs10, hlimbs9, hn3, hm3']
    · -- Case i = 4
      have : j4.val + c3.val ≤ 2^51 + (2^13 - 1) * 19 := by omega
      simpa [hlimbs10, hn4, hm4']

  -- Prove equality of the result and the input `[MOD p]`
  · -- Crux: `reduce` computes `ArrayU645_to_Nat limbs - p * (limbs[4] >> 51)`
    have h : ArrayU645_to_Nat limbs10 + p * (limbs[4].val >>> 51) = ArrayU645_to_Nat limbs := by
      unfold ArrayU645_to_Nat
      -- TO DO: complete this using the specifics of the calculation
      sorry
    -- TO DO: the following calculation could be slicker?
    rw [← h, Nat.ModEq]
    calc (ArrayU645_to_Nat limbs10 + p * (limbs[4].val >>> 51)) % p
      = (ArrayU645_to_Nat limbs10 % p + (p * (limbs[4].val >>> 51)) % p) % p := by rw [Nat.add_mod]
      _ = (ArrayU645_to_Nat limbs10 % p + 0) % p := by
        have : p * (limbs[4].val >>> 51) % p = 0 := Nat.mod_eq_zero_of_dvd <| dvd_mul_right p _
        rw [this]
      _ = ArrayU645_to_Nat limbs10 % p := by simp
