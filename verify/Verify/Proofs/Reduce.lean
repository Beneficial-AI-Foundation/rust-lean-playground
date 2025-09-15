import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib
import Verify.Proofs.Aux

set_option linter.style.longLine false

/-! # Reduce

The main statement concerning `reduce` is `reduce_spec` (below).
-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Auxillary defs required for specs -/

/-- Auxiliary definition to interpret a vector of u32 as an integer -/
@[simp]
def ArrayU645_to_Nat (limbs : Array U64 5#usize) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(51 * i) * (limbs[i]!).val

/-- Curve25519 is the elliptic curve over the prime field with order p -/
def p : Nat := 2^255 - 19

/-! ## Spec for `reduce` -/

/-- **Spec and proof concerning `reduce`**:
- Does not overflow and hence returns a result
- All the limbs of the result are small, ≤ 2^(51 + ε)
- The result is equal to the input mod p. -/
theorem reduce_spec (limbs : Array U64 5#usize) :
    ∃ r, reduce limbs = ok (r) ∧
    (∀ i, i < 5 → (r[i]!).val ≤ 2^51 + (2^13 - 1) * 19) ∧
    ArrayU645_to_Nat limbs ≡ ArrayU645_to_Nat r [MOD p] := by

  unfold reduce

  -- Perform `>>> 51` on each of the limbs
  progress as ⟨ i0, hi0 ⟩; progress as ⟨ c0, hc0, hc0' ⟩
  progress as ⟨ i1, hi1 ⟩; progress as ⟨ c1, hc1, hc1' ⟩
  progress as ⟨ i2, hi2 ⟩; progress as ⟨ c2, hc2, hc2' ⟩
  progress as ⟨ i3, hi3 ⟩; progress as ⟨ c3, hc3, hc3' ⟩
  progress as ⟨ i4, hi4 ⟩; progress as ⟨ c4, hc4, hc4' ⟩

  -- Right-shifting a 64-bit value by 51 bits leaves at most 13 bits so bounded by 2^13 - 1.
  have hc0'' : c0.val ≤ 2^13 - 1 := by simp [hc0, U64_shiftRight_le]
  have hc1'' : c1.val ≤ 2^13 - 1 := by simp [hc1, U64_shiftRight_le]
  have hc2'' : c2.val ≤ 2^13 - 1 := by simp [hc2, U64_shiftRight_le]
  have hc3'' : c3.val ≤ 2^13 - 1 := by simp [hc3, U64_shiftRight_le]
  have hc4'' : c4.val ≤ 2^13 - 1 := by simp [hc4, U64_shiftRight_le]

  -- Perform `&&& LOW_51_BIT_MASK` on each of the limbs
  progress as ⟨ j0, hj0, hj0' ⟩; progress as ⟨ limbs1, hlimbs1 ⟩; progress as ⟨ l1, hl1 ⟩
  progress as ⟨ j1, hj1, hj1' ⟩; progress as ⟨ limbs2, hlimbs2 ⟩; progress as ⟨ l2, hl2 ⟩
  progress as ⟨ j2, hj2, hj2' ⟩; progress as ⟨ limbs3, hlimbs3 ⟩; progress as ⟨ l3, hl3 ⟩
  progress as ⟨ j3, hj3, hj3' ⟩; progress as ⟨ limbs4, hlimbs4 ⟩; progress as ⟨ l4, hl4 ⟩
  progress as ⟨ j4, hj4, hj4' ⟩; progress as ⟨ limbs5, hlimbs5 ⟩; progress as ⟨ l5, hl5 ⟩

  -- Bitwise `&&& LOW_51_BIT_MASK` keeps only the lower 51 bits so j_i.val ≤ 2^51 - 1 < 2^51
  have hj0'' : j0.val < 2^51 := by simpa [hj0] using and_LOW_51_BIT_MASK_lt i0
  have hj1'' : j1.val < 2^51 := by simpa [hj1] using and_LOW_51_BIT_MASK_lt l1
  have hj2'' : j2.val < 2^51 := by simpa [hj2] using and_LOW_51_BIT_MASK_lt l2
  have hj3'' : j3.val < 2^51 := by simpa [hj3] using and_LOW_51_BIT_MASK_lt l3
  have hj4'' : j4.val < 2^51 := by simpa [hj4] using and_LOW_51_BIT_MASK_lt l4

  -- Upper bounds on each limb of the result, shows no overflow and gives the bound required later
  have : j0.val + c4.val * 19 ≤ 2^51 + (2^13 - 1) * 19 := by omega
  have : j1.val + c0.val ≤ 2^51 + (2^13 - 1) * 19 := by omega
  have : j2.val + c1.val ≤ 2^51 + (2^13 - 1) * 19 := by omega
  have : j3.val + c2.val ≤ 2^51 + (2^13 - 1) * 19 := by omega
  have : j4.val + c3.val ≤ 2^51 + (2^13 - 1) * 19 := by omega

  -- Add the parts of limbs together
  progress as ⟨ m0, hm0 ⟩
  have hm0' : m0 = j0 := by simp [hm0, hlimbs5, hlimbs4, hlimbs3, hlimbs2, hlimbs1]
  have : m0 + l5 ≤ U64.max := by simp [U64.max_eq, hm0']; omega
  progress as ⟨ n0, hn0 ⟩; progress as ⟨ limbs6, hlimbs6 ⟩

  progress as ⟨ m1, hm1 ⟩
  have hm1' : m1 = j1 := by simp [hm1, hlimbs6, hlimbs5, hlimbs4, hlimbs3, hlimbs2, hlimbs1]
  have : m1 + c0 ≤ U64.max := by rw [U64.max_eq, hm1']; omega
  progress as ⟨ n1, hn1 ⟩; progress as ⟨ limbs7, hlimbs7 ⟩

  progress as ⟨ m2, hm2 ⟩
  have hm2' : m2 = j2 := by simp [hm2, hlimbs7, hlimbs6, hlimbs5, hlimbs4, hlimbs3, hlimbs2]
  have : m2 + c1 ≤ U64.max := by rw [U64.max_eq, hm2']; omega
  progress as ⟨ n2, hn2 ⟩; progress as ⟨ limbs8, hlimbs8 ⟩

  progress as ⟨ m3, hm3 ⟩
  have hm3' : m3 = j3 := by simp [hm3, hlimbs8, hlimbs7, hlimbs6, hlimbs5, hlimbs4, hlimbs3]
  have : m3 + c2 ≤ U64.max := by rw [U64.max_eq, hm3']; omega
  progress as ⟨ n3, hn3 ⟩; progress as ⟨ limbs9, hlimbs9 ⟩

  progress as ⟨ m4, hm4 ⟩
  have hm4' : m4 = j4 := by simp [hm4, hlimbs9, hlimbs8, hlimbs7, hlimbs6, hlimbs5, hlimbs4]
  have : m4 + c3 ≤ U64.max := by rw [U64.max_eq, hm4']; omega
  progress as ⟨ n4, hn4 ⟩; progress as ⟨ limbs10, hlimbs10 ⟩

  refine ⟨fun i hi ↦ ?_, ?_⟩

  -- Prove upper bounds on each limb of the result
  · interval_cases i
    · simpa [hlimbs10, hlimbs9, hlimbs8, hlimbs7, hlimbs6, hn0, hm0', hl5]
    · simpa [hlimbs10, hlimbs9, hlimbs8, hlimbs7, hn1, hm1']
    · simpa [hlimbs10, hlimbs9, hlimbs8, hn2, hm2']
    · simpa [hlimbs10, hlimbs9, hn3, hm3']
    · simpa [hlimbs10, hn4, hm4']

  -- Remains to prove equality of the result and the input `[MOD p]`
  · have h : ArrayU645_to_Nat limbs10 + p * (limbs[4].val >>> 51) = ArrayU645_to_Nat limbs := by

      -- x = (x & mask) + (x >> 51) * 2^51
      have hlimbs_0 : (limbs.val)[0].val = j0 + c0 * 2^51 := by simpa [hc0, hi0, hj0, hi0] using U64.split_51 limbs[0]
      have hlimbs_1 : (limbs.val)[1].val = j1 + c1 * 2^51 := by simpa [hc1, hi1, hj1, hl1, hlimbs1] using U64.split_51 limbs[1]
      have hlimbs_2 : (limbs.val)[2].val = j2 + c2 * 2^51 := by simpa [hc2, hi2, hj2, hl2, hlimbs2, hlimbs1] using U64.split_51 limbs[2]
      have hlimbs_3 : (limbs.val)[3].val = j3 + c3 * 2^51 := by simpa [hc3, hi3, hj3, hl3, hlimbs3, hlimbs2, hlimbs1] using U64.split_51 limbs[3]
      have hlimbs_4 : (limbs.val)[4].val = j4 + c4 * 2^51 := by simpa [hc4, hi4, hj4, hl4, hlimbs4, hlimbs3, hlimbs2, hlimbs1] using U64.split_51 limbs[4]

      -- formulae from the construction of `reduce`
      have hlimbs10_0 : (limbs10.val)[0].val = j0 + c4 * 19 := by simp [hlimbs10, hlimbs9, hlimbs8, hlimbs7, hlimbs6, hn0, hm0', hl5]
      have hlimbs10_1 : (limbs10.val)[1].val = j1 + c0 := by simp [hlimbs10, hlimbs9, hlimbs8, hlimbs7, hn1, hm1']
      have hlimbs10_2 : (limbs10.val)[2].val = j2 + c1 := by simp [hlimbs10, hlimbs9, hlimbs8, hn2, hm2']
      have hlimbs10_3 : (limbs10.val)[3].val = j3 + c2 := by simp [hlimbs10, hlimbs9, hn3, hm3']
      have hlimbs10_4 : (limbs10.val)[4].val = j4 + c3 := by simp [hlimbs10, hn4, hm4']

      simp [p, show c4 = (limbs[4].val >>> 51) by simp [hc4, hi4]; rfl, Finset.sum_range_succ, hlimbs_0, hlimbs_1, hlimbs_2, hlimbs_3, hlimbs_4, hlimbs10_0, hlimbs10_1, hlimbs10_2, hlimbs10_3, hlimbs10_4]
      ring

    rw [← h, Nat.ModEq]
    simp
