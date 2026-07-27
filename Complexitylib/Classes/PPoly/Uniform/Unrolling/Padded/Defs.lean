/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling

/-!
# Regularly padded deterministic unrolling families -- definitions

The direct tableau circuit has a polynomial upper bound on its gate count, but
its exact length depends on the compiled machine. Padding every positive member
to that bound and adding one final output copy makes the gate-count header a
closed expression of the time horizon while retaining the original acceptance
wire.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- Closed gate-count bound used to regularize a direct tableau member. -/
noncomputable def directUnrollingGateBound (tm : TM k) (f : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  CircuitUnrolling.acceptanceSizeCoeff tm.toNTM * (f n + 2) ^ 3

/-- A positive direct-unrolling raw circuit padded to its cubic gate bound.

The padding gates are constant false and are semantically dead. The final gate
copies the original last gate, so it remains the designated output after the
padding is appended. -/
noncomputable def paddedDirectUnrollingRawCircuit (tm : TM k) (f : ℕ → ℕ)
    (n : ℕ) [NeZero n] : CircuitCode.RawCircuit :=
  let raw := tm.directUnrollingRawCircuit f n
  let bound := tm.directUnrollingGateBound f n
  raw ++
    List.replicate (bound - raw.length)
      (CircuitCode.RawGate.constant 0 false) ++
    [CircuitCode.RawGate.copy (n + raw.length - 1)]

/-- Total tagged code of the regularly padded direct family. The zero-length
member retains the explicit bounded-run answer used by the direct family. -/
noncomputable def paddedDirectUnrollingCode (tm : TM k) (f : ℕ → ℕ) :
    ℕ → List Bool
  | 0 => [false, CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f 0)
      (fun i => Fin.elim0 i) (fun _ => false)]
  | n + 1 => true :: (tm.paddedDirectUnrollingRawCircuit f (n + 1)).encode

end TM

end Complexity
