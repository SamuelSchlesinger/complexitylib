/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Family
public import Complexitylib.Circuits.Unrolling.Acceptance

/-!
# Streamable deterministic unrolling families — definitions

The nonuniform unrolling family fixes the choice prefix of `tm.toNTM` by
repeated typed-circuit hardwiring.  That construction has convenient semantics,
but its serialized syntax is needlessly difficult for a log-space generator to
reproduce.

For a deterministic machine, the embedded NTM ignores every choice bit.  At
positive input lengths this module therefore reuses primary input wire zero for
all choice positions and leaves the ordinary data wires in place.  The resulting
typed circuit is reconstructed directly from `acceptanceRawCircuit`, so erasing
it recovers exactly the raw list that a streaming generator will emit.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Positive-arity input layout for deterministic unrolling.  Data bit `i`
remains primary input `i`; every semantically irrelevant choice position reuses
primary input zero. -/
def deterministicInputWires (T n : ℕ) [NeZero n] : InputWires T n n where
  choice _ := ⟨0, NeZero.pos n⟩
  data i := i

end CircuitUnrolling

namespace TM

/-- The exact raw circuit underlying the streamable positive-length member. -/
noncomputable def directUnrollingRawCircuit (tm : TM k) (f : ℕ → ℕ)
    (n : ℕ) [NeZero n] : CircuitCode.RawCircuit :=
  CircuitUnrolling.acceptanceRawCircuit tm.toNTM (f n) n n
    (CircuitUnrolling.deterministicInputWires (f n) n)

/-- Total tagged code specification for the direct family.  The zero-length
case is the explicit answer bit; every positive case is the literal raw
tableau encoding that the future streaming transducer must produce. -/
noncomputable def directUnrollingCode (tm : TM k) (f : ℕ → ℕ) :
    ℕ → List Bool
  | 0 => [false, CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f 0)
      (fun i => Fin.elim0 i) (fun _ => false)]
  | n + 1 => true :: (tm.directUnrollingRawCircuit f (n + 1)).encode

/-- A deterministic unrolling family whose positive members are reconstructed
directly from their raw tableau circuits.  Unlike the older fixed-prefix family,
its canonical serialization has no intervening hardwiring transformation. -/
noncomputable def directUnrollingCircuitFamily (tm : TM k) (f : ℕ → ℕ) :
    CircuitFamily Basis.andOr2 := by
  classical
  exact
    { emptyOutput := CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f 0)
        (fun i => Fin.elim0 i) (fun _ => false)
      circuits := fun n _ =>
        ⟨_, CircuitUnrolling.acceptanceCircuit tm.toNTM (f n) n n
          (CircuitUnrolling.deterministicInputWires (f n) n)⟩ }

end TM

end Complexity
