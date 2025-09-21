/- This is the file produce by `hax into lean` and should not be edited manually (although in this
case some minor edits were required). This is the Lean representation of the Rust source code. -/

import Verify.Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

def LOW_51_BIT_MASK : u64 := 2251799813685247

@[spec]
def reduce
  (limbs : (RustArray u64 (5 : usize)))
  : Result (RustArray u64 (5 : usize))
  := do
  let c0 : u64 ← (pure (← (← limbs[(0 : usize)]_?) >>>? (51 : i32)));
  let c1 : u64 ← (pure (← (← limbs[(1 : usize)]_?) >>>? (51 : i32)));
  let c2 : u64 ← (pure (← (← limbs[(2 : usize)]_?) >>>? (51 : i32)));
  let c3 : u64 ← (pure (← (← limbs[(3 : usize)]_?) >>>? (51 : i32)));
  let c4 : u64 ← (pure (← (← limbs[(4 : usize)]_?) >>>? (51 : i32)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (0 : usize)
        (← (← limbs[(0 : usize)]_?)
          &&&? LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (1 : usize)
        (← (← limbs[(1 : usize)]_?)
          &&&? LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (2 : usize)
        (← (← limbs[(2 : usize)]_?)
          &&&? LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (3 : usize)
        (← (← limbs[(3 : usize)]_?)
          &&&? LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (4 : usize)
        (← (← limbs[(4 : usize)]_?)
          &&&? LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (0 : usize)
        (← (← limbs[(0 : usize)]_?) +? (← c4 *? (19 : u64)))));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (1 : usize)
        (← (← limbs[(1 : usize)]_?) +? c0)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (2 : usize)
        (← (← limbs[(2 : usize)]_?) +? c1)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (3 : usize)
        (← (← limbs[(3 : usize)]_?) +? c2)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (4 : usize)
        (← (← limbs[(4 : usize)]_?) +? c3)));
  limbs
