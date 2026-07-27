/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Internal

/-!
# Streamable deterministic unrolling families

This module exposes a deterministic tableau family whose positive members are
reconstructed directly from `acceptanceRawCircuit`.  Its circuit code is exactly
the encoding of that raw gate list, avoiding the repeated typed hardwiring used
by the older nonuniform family.  This is the code target for the log-space
uniformity emitter.

## Main results

- `TM.directUnrollingCircuitFamily_function` — exact bounded-trace semantics.
- `TM.directUnrollingCircuitFamily_encodeAt_zero` — explicit empty-input code.
- `TM.directUnrollingCircuitFamily_encodeAt_succ` — exact raw serialization.
- `TM.directUnrollingCircuitFamily_encodeAt` — total exact code specification.
- `TM.DecidesInTime.directUnrollingCircuitFamily_decides` — language correctness.
- `TM.directUnrollingCircuitFamily_size_bigO` — cubic-in-time size.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Every deterministic choice position reuses primary input wire zero. -/
@[simp] theorem deterministicInputWires_choice_val
    (T n : ℕ) [NeZero n] (i : Fin T) :
    ((deterministicInputWires T n).choice i).val = 0 :=
  deterministicInputWires_choice_val_internal T n i

/-- Deterministic unrolling leaves every data input at its original wire. -/
@[simp] theorem deterministicInputWires_data
    (T n : ℕ) [NeZero n] (i : Fin n) :
    (deterministicInputWires T n).data i = i :=
  deterministicInputWires_data_internal T n i

end CircuitUnrolling

namespace TM

/-- The direct deterministic family computes the exact bounded acceptance bit. -/
theorem directUnrollingCircuitFamily_function
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) (x : BitString n) :
    (tm.directUnrollingCircuitFamily f).function n x =
      CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f n) x
        (fun _ => false) :=
  tm.directUnrollingCircuitFamily_function_internal f n x

/-- At length zero, the direct family code is the tag followed by the fixed
bounded-run answer bit. -/
theorem directUnrollingCircuitFamily_encodeAt_zero
    (tm : TM k) (f : ℕ → ℕ) :
    (tm.directUnrollingCircuitFamily f).encodeAt 0 =
      [false, CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f 0)
        (fun i => Fin.elim0 i) (fun _ => false)] := rfl

/-- At every positive length, the family code is literally the tagged encoding
of the direct raw tableau circuit. -/
theorem directUnrollingCircuitFamily_encodeAt_succ
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) :
    (tm.directUnrollingCircuitFamily f).encodeAt (n + 1) =
      true :: (tm.directUnrollingRawCircuit f (n + 1)).encode :=
  tm.directUnrollingCircuitFamily_encodeAt_succ_internal f n

/-- The family codec agrees at every length with the explicit direct code map,
including the separate zero-length member. -/
theorem directUnrollingCircuitFamily_encodeAt
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) :
    (tm.directUnrollingCircuitFamily f).encodeAt n =
      tm.directUnrollingCode f n :=
  tm.directUnrollingCircuitFamily_encodeAt_internal f n

/-- A deterministic decider's direct tableau family decides the same language. -/
theorem DecidesInTime.directUnrollingCircuitFamily_decides
    {tm : TM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInTime L f) :
    (tm.directUnrollingCircuitFamily f).Decides L :=
  hdec.directUnrollingCircuitFamily_decides_internal

/-- A horizon in `O(n^d)` gives the direct family size `O(n^(3d))`. -/
theorem directUnrollingCircuitFamily_size_bigO
    (tm : TM k) {f : ℕ → ℕ} {d : ℕ}
    (hf : f =O ((· ^ d) : ℕ → ℕ)) :
    (tm.directUnrollingCircuitFamily f).size =O
      ((· ^ (3 * d)) : ℕ → ℕ) :=
  tm.directUnrollingCircuitFamily_size_bigO_internal hf

end TM

end Complexity
