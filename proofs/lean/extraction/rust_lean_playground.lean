
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false



def LOW_51_BIT_MASK : UInt64 := 2251799813685247
TODO_LINE_422
def impl_reduce (limbs : (RustArray UInt64 5)) : Result FieldElement51 := do
  let (c0 : UInt64) ← pure
    (← hax_machine_int_shr (← ops_index_Index_index limbs 0) 51);
  let (c1 : UInt64) ← pure
    (← hax_machine_int_shr (← ops_index_Index_index limbs 1) 51);
  let (c2 : UInt64) ← pure
    (← hax_machine_int_shr (← ops_index_Index_index limbs 2) 51);
  let (c3 : UInt64) ← pure
    (← hax_machine_int_shr (← ops_index_Index_index limbs 3) 51);
  let (c4 : UInt64) ← pure
    (← hax_machine_int_shr (← ops_index_Index_index limbs 4) 51);
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      0
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 0)
        LOW_51_BIT_MASK));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      1
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 1)
        LOW_51_BIT_MASK));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      2
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 2)
        LOW_51_BIT_MASK));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      3
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 3)
        LOW_51_BIT_MASK));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      4
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 4)
        LOW_51_BIT_MASK));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      0
      (← hax_machine_int_add
      (← ops_index_Index_index limbs 0)
        (← hax_machine_int_mul c4 19)));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      1
      (← hax_machine_int_add (← ops_index_Index_index limbs 1) c0));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      2
      (← hax_machine_int_add (← ops_index_Index_index limbs 2) c1));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      3
      (← hax_machine_int_add (← ops_index_Index_index limbs 3) c2));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      4
      (← hax_machine_int_add (← ops_index_Index_index limbs 4) c3));
  (constr_FieldElement51 (FieldElement51_limbs := limbs))
