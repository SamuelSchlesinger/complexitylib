/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Hardwiring
public import Complexitylib.Circuits.Unrolling.Acceptance

/-!
# Fixed-choice bounded acceptance circuits

This module fixes the choices-first prefix of a canonical bounded acceptance
circuit, leaving only the positive-length data input live. It is the reusable
single-run analogue of amplified-seed hardwiring.

## Main definitions and results

- `fixedChoicesAcceptanceCircuit`: hardwire one complete choice string.
- `fixedChoicesAcceptanceCircuit_eval`: exact bounded-acceptance semantics.
- `fixedChoicesAcceptanceCircuit_size`: exact size preservation.
- `fixedChoicesAcceptanceCircuit_size_le`: inherited cubic size bound.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Fix every choice input of a canonical bounded acceptance circuit while
leaving its positive-length data suffix live. -/
noncomputable def fixedChoicesAcceptanceCircuit
    (tm : NTM k) (T n : ℕ) [NeZero n] (choices : BitString T) :
    Circuit Basis.andOr2 n 1
      ((acceptanceRawCircuit tm T n (T + n) (prefixInputWires T n)).length - 1) :=
  Circuit.restrictPrefix choices (canonicalAcceptanceCircuit tm T n)

/-- Fixing the choice prefix preserves the exact bounded acceptance bit. -/
theorem fixedChoicesAcceptanceCircuit_eval
    (tm : NTM k) (T n : ℕ) [NeZero n]
    (choices : BitString T) (x : BitString n) :
    ((fixedChoicesAcceptanceCircuit tm T n choices).eval x) 0 =
      boundedAcceptanceBit tm T x choices := by
  rw [fixedChoicesAcceptanceCircuit, Circuit.restrictPrefix_eval,
    canonicalAcceptanceCircuit_eval]
  rfl

/-- Fixing the choice prefix preserves the canonical circuit's exact size. -/
@[simp] theorem fixedChoicesAcceptanceCircuit_size
    (tm : NTM k) (T n : ℕ) [NeZero n] (choices : BitString T) :
    (fixedChoicesAcceptanceCircuit tm T n choices).size =
      (canonicalAcceptanceCircuit tm T n).size := by
  rw [fixedChoicesAcceptanceCircuit, Circuit.restrictPrefix_size]

/-- A fixed-choice acceptance circuit inherits the canonical cubic bound. -/
theorem fixedChoicesAcceptanceCircuit_size_le
    (tm : NTM k) (T n : ℕ) [NeZero n] (choices : BitString T) :
    (fixedChoicesAcceptanceCircuit tm T n choices).size ≤
      acceptanceSizeCoeff tm * (T + 2) ^ 3 := by
  rw [fixedChoicesAcceptanceCircuit_size]
  exact canonicalAcceptanceCircuit_size_le tm T n

end CircuitUnrolling

end Complexity
