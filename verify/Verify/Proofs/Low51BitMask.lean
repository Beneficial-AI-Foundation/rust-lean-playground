import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib

set_option linter.style.longLine false

/-! # LOW_51_BIT_MASK

Theorems about the LOW_51_BIT_MASK constant.
-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for LOW_51_BIT_MASK -/

theorem LOW_51_BIT_MASK_val_eq : LOW_51_BIT_MASK.val = 2^51 - 1 := by
  unfold LOW_51_BIT_MASK; decide

/-- Bitwise AND with (2^51 - 1) keeps only the lower 51 bits so bounded ≤ 2^51 - 1 < 2^51. -/
theorem and_LOW_51_BIT_MASK_lt (a : U64) : (a &&& LOW_51_BIT_MASK).val < 2^51 := by
  simp [LOW_51_BIT_MASK_val_eq]; omega
