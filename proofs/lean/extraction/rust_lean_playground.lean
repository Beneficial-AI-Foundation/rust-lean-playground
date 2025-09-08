
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


def field_add_assign (lhs : (RustArray UInt64 5)) (rhs : (RustArray UInt64 5))
  : Result (RustArray UInt64 5) := do
  let (lhs : (RustArray UInt64 5)) ← pure
    (← hax_folds_fold_range
    0
      5
      (fun (lhs : (RustArray UInt64 5)) (_ : USize) => do true)
      lhs
      (fun (lhs : (RustArray UInt64 5)) (i : USize) => do
        (← hax_monomorphized_update_at_update_at_usize
        lhs
          i
          (← (← ops_index_Index_index lhs i) +? (← ops_index_Index_index
          rhs
            i)))));
  lhs

def field_add (lhs : (RustArray UInt64 5)) (rhs : (RustArray UInt64 5))
  : Result (RustArray UInt64 5) := do
  let (output : (RustArray UInt64 5)) ← pure lhs;
  let (output : (RustArray UInt64 5)) ← pure (← field_add_assign output rhs);
  output

def field_mul_m (x : UInt64) (y : UInt64) : Result TODO_LINE_385 := do
  (← (← hax_cast_op x) *? (← hax_cast_op y))

def field_mul_LOW_51_BIT_MASK : Result UInt64 := do
  (← (← hax_machine_int_shl 1 51) -? 1)

def field_mul (lhs : (RustArray UInt64 5)) (rhs : (RustArray UInt64 5))
  : Result (RustArray UInt64 5) := do
  let ((a : (RustArray UInt64 5)) : (RustArray UInt64 5)) ← pure lhs;
  let ((b : (RustArray UInt64 5)) : (RustArray UInt64 5)) ← pure rhs;
  let (b1_19 : UInt64) ← pure (← (← ops_index_Index_index b 1) *? 19);
  let (b2_19 : UInt64) ← pure (← (← ops_index_Index_index b 2) *? 19);
  let (b3_19 : UInt64) ← pure (← (← ops_index_Index_index b 3) *? 19);
  let (b4_19 : UInt64) ← pure (← (← ops_index_Index_index b 4) *? 19);
  let ((c0 : TODO_LINE_385) : TODO_LINE_385) ← pure
    (← (← (← (← (← field_mul_m
    (← ops_index_Index_index a 0)
      (← ops_index_Index_index b 0)) +? (← field_mul_m
    (← ops_index_Index_index a 4)
      b1_19)) +? (← field_mul_m (← ops_index_Index_index a 3) b2_19)) +?
    (← field_mul_m (← ops_index_Index_index a 2) b3_19)) +? (← field_mul_m
    (← ops_index_Index_index a 1)
      b4_19));
  let ((c1 : TODO_LINE_385) : TODO_LINE_385) ← pure
    (← (← (← (← (← field_mul_m
    (← ops_index_Index_index a 1)
      (← ops_index_Index_index b 0)) +? (← field_mul_m
    (← ops_index_Index_index a 0)
      (← ops_index_Index_index b 1))) +? (← field_mul_m
    (← ops_index_Index_index a 4)
      b2_19)) +? (← field_mul_m (← ops_index_Index_index a 3) b3_19)) +?
    (← field_mul_m (← ops_index_Index_index a 2) b4_19));
  let ((c2 : TODO_LINE_385) : TODO_LINE_385) ← pure
    (← (← (← (← (← field_mul_m
    (← ops_index_Index_index a 2)
      (← ops_index_Index_index b 0)) +? (← field_mul_m
    (← ops_index_Index_index a 1)
      (← ops_index_Index_index b 1))) +? (← field_mul_m
    (← ops_index_Index_index a 0)
      (← ops_index_Index_index b 2))) +? (← field_mul_m
    (← ops_index_Index_index a 4)
      b3_19)) +? (← field_mul_m (← ops_index_Index_index a 3) b4_19));
  let ((c3 : TODO_LINE_385) : TODO_LINE_385) ← pure
    (← (← (← (← (← field_mul_m
    (← ops_index_Index_index a 3)
      (← ops_index_Index_index b 0)) +? (← field_mul_m
    (← ops_index_Index_index a 2)
      (← ops_index_Index_index b 1))) +? (← field_mul_m
    (← ops_index_Index_index a 1)
      (← ops_index_Index_index b 2))) +? (← field_mul_m
    (← ops_index_Index_index a 0)
      (← ops_index_Index_index b 3))) +? (← field_mul_m
    (← ops_index_Index_index a 4)
      b4_19));
  let ((c4 : TODO_LINE_385) : TODO_LINE_385) ← pure
    (← (← (← (← (← field_mul_m
    (← ops_index_Index_index a 4)
      (← ops_index_Index_index b 0)) +? (← field_mul_m
    (← ops_index_Index_index a 3)
      (← ops_index_Index_index b 1))) +? (← field_mul_m
    (← ops_index_Index_index a 2)
      (← ops_index_Index_index b 2))) +? (← field_mul_m
    (← ops_index_Index_index a 1)
      (← ops_index_Index_index b 3))) +? (← field_mul_m
    (← ops_index_Index_index a 0)
      (← ops_index_Index_index b 4)));
  let (_ : hax_Tuple0) ← pure
    if true
    then
      let (_ : hax_Tuple0) ← pure
        (← assert
        (← hax_machine_int_lt
          (← ops_index_Index_index a 0)
            (← hax_machine_int_shl 1 54)));
      hax_Tuple0
    else hax_Tuple0;
  let (_ : hax_Tuple0) ← pure
    if true
    then
      let (_ : hax_Tuple0) ← pure
        (← assert
        (← hax_machine_int_lt
          (← ops_index_Index_index b 0)
            (← hax_machine_int_shl 1 54)));
      hax_Tuple0
    else hax_Tuple0;
  let (_ : hax_Tuple0) ← pure
    if true
    then
      let (_ : hax_Tuple0) ← pure
        (← assert
        (← hax_machine_int_lt
          (← ops_index_Index_index a 1)
            (← hax_machine_int_shl 1 54)));
      hax_Tuple0
    else hax_Tuple0;
  let (_ : hax_Tuple0) ← pure
    if true
    then
      let (_ : hax_Tuple0) ← pure
        (← assert
        (← hax_machine_int_lt
          (← ops_index_Index_index b 1)
            (← hax_machine_int_shl 1 54)));
      hax_Tuple0
    else hax_Tuple0;
  let (_ : hax_Tuple0) ← pure
    if true
    then
      let (_ : hax_Tuple0) ← pure
        (← assert
        (← hax_machine_int_lt
          (← ops_index_Index_index a 2)
            (← hax_machine_int_shl 1 54)));
      hax_Tuple0
    else hax_Tuple0;
  let (_ : hax_Tuple0) ← pure
    if true
    then
      let (_ : hax_Tuple0) ← pure
        (← assert
        (← hax_machine_int_lt
          (← ops_index_Index_index b 2)
            (← hax_machine_int_shl 1 54)));
      hax_Tuple0
    else hax_Tuple0;
  let (_ : hax_Tuple0) ← pure
    if true
    then
      let (_ : hax_Tuple0) ← pure
        (← assert
        (← hax_machine_int_lt
          (← ops_index_Index_index a 3)
            (← hax_machine_int_shl 1 54)));
      hax_Tuple0
    else hax_Tuple0;
  let (_ : hax_Tuple0) ← pure
    if true
    then
      let (_ : hax_Tuple0) ← pure
        (← assert
        (← hax_machine_int_lt
          (← ops_index_Index_index b 3)
            (← hax_machine_int_shl 1 54)));
      hax_Tuple0
    else hax_Tuple0;
  let (_ : hax_Tuple0) ← pure
    if true
    then
      let (_ : hax_Tuple0) ← pure
        (← assert
        (← hax_machine_int_lt
          (← ops_index_Index_index a 4)
            (← hax_machine_int_shl 1 54)));
      hax_Tuple0
    else hax_Tuple0;
  let (_ : hax_Tuple0) ← pure
    if true
    then
      let (_ : hax_Tuple0) ← pure
        (← assert
        (← hax_machine_int_lt
          (← ops_index_Index_index b 4)
            (← hax_machine_int_shl 1 54)));
      hax_Tuple0
    else hax_Tuple0;
  let (out : (RustArray UInt64 5)) ← pure (← hax_repeat 0 5);
  let (c1 : TODO_LINE_385) ← pure
    (← c1 +? (← hax_cast_op (← hax_cast_op (← c0 >>>? 51))));
  let (out : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    out
      0
      (← hax_machine_int_bitand (← hax_cast_op c0) field_mul_LOW_51_BIT_MASK));
  let (c2 : TODO_LINE_385) ← pure
    (← c2 +? (← hax_cast_op (← hax_cast_op (← c1 >>>? 51))));
  let (out : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    out
      1
      (← hax_machine_int_bitand (← hax_cast_op c1) field_mul_LOW_51_BIT_MASK));
  let (c3 : TODO_LINE_385) ← pure
    (← c3 +? (← hax_cast_op (← hax_cast_op (← c2 >>>? 51))));
  let (out : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    out
      2
      (← hax_machine_int_bitand (← hax_cast_op c2) field_mul_LOW_51_BIT_MASK));
  let (c4 : TODO_LINE_385) ← pure
    (← c4 +? (← hax_cast_op (← hax_cast_op (← c3 >>>? 51))));
  let (out : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    out
      3
      (← hax_machine_int_bitand (← hax_cast_op c3) field_mul_LOW_51_BIT_MASK));
  let ((carry : UInt64) : UInt64) ← pure (← hax_cast_op (← c4 >>>? 51));
  let (out : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    out
      4
      (← hax_machine_int_bitand (← hax_cast_op c4) field_mul_LOW_51_BIT_MASK));
  let (out : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    out
      0
      (← (← ops_index_Index_index out 0) +? (← carry *? 19)));
  let (out : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    out
      1
      (← (← ops_index_Index_index out 1) +? (← (← ops_index_Index_index out 0)
      >>>? 51)));
  let (out : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    out
      0
      (← hax_machine_int_bitand
      (← ops_index_Index_index out 0)
        field_mul_LOW_51_BIT_MASK));
  out

def field_mul_assign (lhs : (RustArray UInt64 5)) (rhs : (RustArray UInt64 5))
  : Result (RustArray UInt64 5) := do
  let (result : (RustArray UInt64 5)) ← pure (← field_mul lhs rhs);
  let (lhs : (RustArray UInt64 5)) ← pure result;
  lhs

def field_from_limbs (limbs : (RustArray UInt64 5))
  : Result (RustArray UInt64 5) := do
  limbs

def field_ZERO : Result (RustArray UInt64 5) := do #v[0, 0, 0, 0, 0

def field_ONE : Result (RustArray UInt64 5) := do
  (← field_from_limbs #v[1, 0, 0, 0, 0)

def field_MINUS_ONE : Result (RustArray UInt64 5) := do
  (← field_from_limbs
  #v[2251799813685228, 2251799813685247, 2251799813685247, 2251799813685247,
      2251799813685247)

def field_reduce_LOW_51_BIT_MASK : Result UInt64 := do
  (← (← hax_machine_int_shl 1 51) -? 1)

def field_reduce (limbs : (RustArray UInt64 5))
  : Result (RustArray UInt64 5) := do
  let (c0 : UInt64) ← pure (← (← ops_index_Index_index limbs 0) >>>? 51);
  let (c1 : UInt64) ← pure (← (← ops_index_Index_index limbs 1) >>>? 51);
  let (c2 : UInt64) ← pure (← (← ops_index_Index_index limbs 2) >>>? 51);
  let (c3 : UInt64) ← pure (← (← ops_index_Index_index limbs 3) >>>? 51);
  let (c4 : UInt64) ← pure (← (← ops_index_Index_index limbs 4) >>>? 51);
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      0
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 0)
        field_reduce_LOW_51_BIT_MASK));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      1
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 1)
        field_reduce_LOW_51_BIT_MASK));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      2
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 2)
        field_reduce_LOW_51_BIT_MASK));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      3
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 3)
        field_reduce_LOW_51_BIT_MASK));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      4
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 4)
        field_reduce_LOW_51_BIT_MASK));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      0
      (← (← ops_index_Index_index limbs 0) +? (← c4 *? 19)));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      1
      (← (← ops_index_Index_index limbs 1) +? c0));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      2
      (← (← ops_index_Index_index limbs 2) +? c1));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      3
      (← (← ops_index_Index_index limbs 3) +? c2));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      4
      (← (← ops_index_Index_index limbs 4) +? c3));
  limbs

def field_sub (lhs : (RustArray UInt64 5)) (rhs : (RustArray UInt64 5))
  : Result (RustArray UInt64 5) := do
  (← field_reduce
  #v[(← (← (← ops_index_Index_index lhs 0) +? 36028797018963664) -?
      (← ops_index_Index_index rhs 0)), (← (← (← ops_index_Index_index lhs 1) +?
      36028797018963952) -? (← ops_index_Index_index rhs 1)),
      (← (← (← ops_index_Index_index lhs 2) +? 36028797018963952) -?
      (← ops_index_Index_index rhs 2)), (← (← (← ops_index_Index_index lhs 3) +?
      36028797018963952) -? (← ops_index_Index_index rhs 3)),
      (← (← (← ops_index_Index_index lhs 4) +? 36028797018963952) -?
      (← ops_index_Index_index rhs 4)))

def field_sub_assign (lhs : (RustArray UInt64 5)) (rhs : (RustArray UInt64 5))
  : Result (RustArray UInt64 5) := do
  let (result : (RustArray UInt64 5)) ← pure (← field_sub lhs rhs);
  let (lhs : (RustArray UInt64 5)) ← pure result;
  lhs

def field_negate (input : (RustArray UInt64 5))
  : Result (RustArray UInt64 5) := do
  let (neg : (RustArray UInt64 5)) ← pure
    (← field_reduce
    #v[(← 36028797018963664 -? (← ops_index_Index_index input 0)),
        (← 36028797018963952 -? (← ops_index_Index_index input 1)),
        (← 36028797018963952 -? (← ops_index_Index_index input 2)),
        (← 36028797018963952 -? (← ops_index_Index_index input 3)),
        (← 36028797018963952 -? (← ops_index_Index_index input 4)));
  let (input : (RustArray UInt64 5)) ← pure neg;
  input

def field_neg (input : (RustArray UInt64 5)) : Result (RustArray UInt64 5) := do
  let (output : (RustArray UInt64 5)) ← pure input;
  let (output : (RustArray UInt64 5)) ← pure (← field_negate output);
  output

def field_from_bytes_load8_at (input : (RustSlice UInt8)) (i : USize)
  : Result UInt64 := do
  (← hax_machine_int_bitor
  (← hax_machine_int_bitor
    (← hax_machine_int_bitor
      (← hax_machine_int_bitor
        (← hax_machine_int_bitor
          (← hax_machine_int_bitor
            (← hax_machine_int_bitor
              (← hax_cast_op (← ops_index_Index_index input i))
                (← hax_machine_int_shl
                (← hax_cast_op (← ops_index_Index_index input (← i +? 1)))
                  8))
              (← hax_machine_int_shl
              (← hax_cast_op (← ops_index_Index_index input (← i +? 2)))
                16))
            (← hax_machine_int_shl
            (← hax_cast_op (← ops_index_Index_index input (← i +? 3)))
              24))
          (← hax_machine_int_shl
          (← hax_cast_op (← ops_index_Index_index input (← i +? 4)))
            32))
        (← hax_machine_int_shl
        (← hax_cast_op (← ops_index_Index_index input (← i +? 5)))
          40))
      (← hax_machine_int_shl
      (← hax_cast_op (← ops_index_Index_index input (← i +? 6)))
        48))
    (← hax_machine_int_shl
    (← hax_cast_op (← ops_index_Index_index input (← i +? 7)))
      56))

def field_from_bytes (bytes : (RustArray UInt8 32))
  : Result (RustArray UInt64 5) := do
  let (low_51_bit_mask : UInt64) ← pure (← (← hax_machine_int_shl 1 51) -? 1);
  #v[(← hax_machine_int_bitand
    (← field_from_bytes_load8_at (← unsize bytes) 0)
      low_51_bit_mask), (← hax_machine_int_bitand
    (← (← field_from_bytes_load8_at (← unsize bytes) 6) >>>? 3)
      low_51_bit_mask), (← hax_machine_int_bitand
    (← (← field_from_bytes_load8_at (← unsize bytes) 12) >>>? 6)
      low_51_bit_mask), (← hax_machine_int_bitand
    (← (← field_from_bytes_load8_at (← unsize bytes) 19) >>>? 1)
      low_51_bit_mask), (← hax_machine_int_bitand
    (← (← field_from_bytes_load8_at (← unsize bytes) 24) >>>? 12)
      low_51_bit_mask)

def field_to_bytes (input : (RustArray UInt64 5))
  : Result (RustArray UInt8 32) := do
  let (limbs : (RustArray UInt64 5)) ← pure (← field_reduce input);
  let (q : UInt64) ← pure
    (← (← (← ops_index_Index_index limbs 0) +? 19) >>>? 51);
  let (q : UInt64) ← pure
    (← (← (← ops_index_Index_index limbs 1) +? q) >>>? 51);
  let (q : UInt64) ← pure
    (← (← (← ops_index_Index_index limbs 2) +? q) >>>? 51);
  let (q : UInt64) ← pure
    (← (← (← ops_index_Index_index limbs 3) +? q) >>>? 51);
  let (q : UInt64) ← pure
    (← (← (← ops_index_Index_index limbs 4) +? q) >>>? 51);
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      0
      (← (← ops_index_Index_index limbs 0) +? (← 19 *? q)));
  let (low_51_bit_mask : UInt64) ← pure (← (← hax_machine_int_shl 1 51) -? 1);
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      1
      (← (← ops_index_Index_index limbs 1) +? (← (← ops_index_Index_index
      limbs
        0) >>>? 51)));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      0
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 0)
        low_51_bit_mask));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      2
      (← (← ops_index_Index_index limbs 2) +? (← (← ops_index_Index_index
      limbs
        1) >>>? 51)));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      1
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 1)
        low_51_bit_mask));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      3
      (← (← ops_index_Index_index limbs 3) +? (← (← ops_index_Index_index
      limbs
        2) >>>? 51)));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      2
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 2)
        low_51_bit_mask));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      4
      (← (← ops_index_Index_index limbs 4) +? (← (← ops_index_Index_index
      limbs
        3) >>>? 51)));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      3
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 3)
        low_51_bit_mask));
  let (limbs : (RustArray UInt64 5)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    limbs
      4
      (← hax_machine_int_bitand
      (← ops_index_Index_index limbs 4)
        low_51_bit_mask));
  let (s : (RustArray UInt8 32)) ← pure (← hax_repeat 0 32);
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      0
      (← hax_cast_op (← ops_index_Index_index limbs 0)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      1
      (← hax_cast_op (← (← ops_index_Index_index limbs 0) >>>? 8)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      2
      (← hax_cast_op (← (← ops_index_Index_index limbs 0) >>>? 16)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      3
      (← hax_cast_op (← (← ops_index_Index_index limbs 0) >>>? 24)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      4
      (← hax_cast_op (← (← ops_index_Index_index limbs 0) >>>? 32)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      5
      (← hax_cast_op (← (← ops_index_Index_index limbs 0) >>>? 40)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      6
      (← hax_cast_op
      (← hax_machine_int_bitor
        (← (← ops_index_Index_index limbs 0) >>>? 48)
          (← hax_machine_int_shl (← ops_index_Index_index limbs 1) 3))));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      7
      (← hax_cast_op (← (← ops_index_Index_index limbs 1) >>>? 5)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      8
      (← hax_cast_op (← (← ops_index_Index_index limbs 1) >>>? 13)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      9
      (← hax_cast_op (← (← ops_index_Index_index limbs 1) >>>? 21)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      10
      (← hax_cast_op (← (← ops_index_Index_index limbs 1) >>>? 29)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      11
      (← hax_cast_op (← (← ops_index_Index_index limbs 1) >>>? 37)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      12
      (← hax_cast_op
      (← hax_machine_int_bitor
        (← (← ops_index_Index_index limbs 1) >>>? 45)
          (← hax_machine_int_shl (← ops_index_Index_index limbs 2) 6))));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      13
      (← hax_cast_op (← (← ops_index_Index_index limbs 2) >>>? 2)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      14
      (← hax_cast_op (← (← ops_index_Index_index limbs 2) >>>? 10)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      15
      (← hax_cast_op (← (← ops_index_Index_index limbs 2) >>>? 18)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      16
      (← hax_cast_op (← (← ops_index_Index_index limbs 2) >>>? 26)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      17
      (← hax_cast_op (← (← ops_index_Index_index limbs 2) >>>? 34)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      18
      (← hax_cast_op (← (← ops_index_Index_index limbs 2) >>>? 42)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      19
      (← hax_cast_op
      (← hax_machine_int_bitor
        (← (← ops_index_Index_index limbs 2) >>>? 50)
          (← hax_machine_int_shl (← ops_index_Index_index limbs 3) 1))));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      20
      (← hax_cast_op (← (← ops_index_Index_index limbs 3) >>>? 7)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      21
      (← hax_cast_op (← (← ops_index_Index_index limbs 3) >>>? 15)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      22
      (← hax_cast_op (← (← ops_index_Index_index limbs 3) >>>? 23)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      23
      (← hax_cast_op (← (← ops_index_Index_index limbs 3) >>>? 31)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      24
      (← hax_cast_op (← (← ops_index_Index_index limbs 3) >>>? 39)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      25
      (← hax_cast_op
      (← hax_machine_int_bitor
        (← (← ops_index_Index_index limbs 3) >>>? 47)
          (← hax_machine_int_shl (← ops_index_Index_index limbs 4) 4))));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      26
      (← hax_cast_op (← (← ops_index_Index_index limbs 4) >>>? 4)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      27
      (← hax_cast_op (← (← ops_index_Index_index limbs 4) >>>? 12)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      28
      (← hax_cast_op (← (← ops_index_Index_index limbs 4) >>>? 20)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      29
      (← hax_cast_op (← (← ops_index_Index_index limbs 4) >>>? 28)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      30
      (← hax_cast_op (← (← ops_index_Index_index limbs 4) >>>? 36)));
  let (s : (RustArray UInt8 32)) ← pure
    (← hax_monomorphized_update_at_update_at_usize
    s
      31
      (← hax_cast_op (← (← ops_index_Index_index limbs 4) >>>? 44)));
  let (_ : hax_Tuple0) ← pure
    if true
    then
      let (_ : hax_Tuple0) ← pure
        (← assert
        (← hax_machine_int_eq
          (← hax_machine_int_bitand (← ops_index_Index_index s 31) 128)
            0));
      hax_Tuple0
    else hax_Tuple0;
  s

def field_pow2k (input : (RustArray UInt64 5)) (k : UInt32)
  : Result (RustArray UInt64 5) := do
  let (_ : hax_Tuple0) ← pure
    if true
    then
      let (_ : hax_Tuple0) ← pure (← assert (← hax_machine_int_gt k 0));
      hax_Tuple0
    else hax_Tuple0;
  let ((a : (RustArray UInt64 5)) : (RustArray UInt64 5)) ← pure input;
  let (TODO_LINE_300 : (hax_Tuple2 (RustArray UInt64 5) UInt32)) ← pure
    (← hax_failure
    "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/933.
Please upvote or comment this issue if you see this error message.
Unhandled loop kind"
      "{
 (loop {
 |Tuple2(a, k)| {
 {
 let a3_19: int = {
 rust_primitives::hax::machine_int::mul(
 19,
 core::ops::index::f_index(a, 3),
 )
 };
 {
 let a4_19: int = {
 rust_primitives::hax::machine_int::mu...");
  a

def field_pow2k_m (x : UInt64) (y : UInt64) : Result TODO_LINE_385 := do
  (← (← hax_cast_op x) *? (← hax_cast_op y))

def field_pow2k_LOW_51_BIT_MASK : Result UInt64 := do
  (← (← hax_machine_int_shl 1 51) -? 1)

def field_square (input : (RustArray UInt64 5))
  : Result (RustArray UInt64 5) := do
  (← field_pow2k input 1)

def field_square2 (input : (RustArray UInt64 5))
  : Result (RustArray UInt64 5) := do
  let (square : (RustArray UInt64 5)) ← pure (← field_pow2k input 1);
  let (square : (RustArray UInt64 5)) ← pure
    (← hax_folds_fold_range
    0
      5
      (fun (square : (RustArray UInt64 5)) (_ : USize) => do true)
      square
      (fun (square : (RustArray UInt64 5)) (i : USize) => do
        (← hax_monomorphized_update_at_update_at_usize
        square
          i
          (← (← ops_index_Index_index square i) *? 2))));
  square




def ZERO : Result (RustArray UInt64 5) := do #v[0, 0, 0, 0, 0
