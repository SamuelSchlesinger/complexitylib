/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Witness
public import Complexitylib.Models.TuringMachine.Witness.PhaseSafety
public import Complexitylib.Models.TuringMachine.Subroutines.GuessBounded

/-!
# Materializing finite certificates from a witness stream

The bounded guess phase stores at most `B` bits on an ordinary charged work
tape, controlled by an ordinary preloaded unary counter. It can stop early,
so every finite certificate up to the bound is available, including the empty
one. Only the external source stream is excluded from the space account.
-/

@[expose] public section

namespace Complexity
namespace WitnessTM

/-- The online phase that stores a bounded, reusable ordinary certificate. -/
def storeBounded (witness counter : Fin k) : WitnessTM k :=
  (NTM.guessBoundedNTM witness counter).toWitnessTM

/-- Exact entry frame for a materialization phase. -/
def storeEntry (inp₀ : Tape) (work₀ : Fin k → Tape) (out₀ source : Tape) :
    TapePred (k + 1) :=
  fun inp work out => inp = inp₀ ∧ work = Fin.snoc work₀ source ∧ out = out₀

/-- A stored certificate with all unrelated tapes framed, and a source stream
whose cells are unchanged and whose cursor advances by at most the phase time. -/
def storePost (witness counter : Fin k) (B : ℕ)
    (inp₀ : Tape) (work₀ : Fin k → Tape) (out₀ source : Tape) : TapePred (k + 1) :=
  fun inp work out => ∃ y : List Bool, y.length ≤ B ∧
    inp = inp₀ ∧ out = out₀ ∧
    work witness.castSucc = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
    (∀ i, i ≠ witness → i ≠ counter → work i.castSucc = work₀ i) ∧
    ∃ consumed, consumed ≤ NTM.guessBoundedTime B 0 ∧
      work (Fin.last k) = ⟨source.head + consumed, source.cells⟩

end WitnessTM
end Complexity
