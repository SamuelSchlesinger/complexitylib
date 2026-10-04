/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Graph
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Observation

/-!
# Exact output-guess simulation of commutative aggregate circuits

The mixed signature combines arbitrary binary Boolean operations with finite
commutative-monoid aggregates. One guessed bit per special occurrence replaces
that gate by a nullary constant. All wire indices and ordinary slots are retained.

`consistent_iff_eq_actualGuess` gives exact unique-witness simulation, including
special-to-special wiring. `accepts_mix_of_componentKey_eq` gives the component
rectangle-cover property with at most `2 ^ budget p` keys. `componentAccept_iff`
expresses each fixed-guess, fixed-outside computation as a product of local signal
observations, suitable for the aggregate network compiler.
-/

@[expose] public section

namespace Algebraic.Aggregate

variable {J : Type} {State : J → Type} {n m : ℕ}

/-- Every designated output is preserved by a consistent special-output guess. -/
theorem eval_eraseCircuit_of_consistent [∀ j, CommMonoid (State j)]
    (c : Circuit (signature State) n m) (a : Guess c.program) (input : Fin n → Bool)
    (consistent : Consistent c.program a input) :
    (eraseCircuit c a).eval ordinaryInterpretation input = c.eval interpretation input := by
  funext output
  change Wire.elim input ((erase c.program a).eval ordinaryInterpretation input)
    (c.outputs output) = Wire.elim input (c.program.eval interpretation input) (c.outputs output)
  rw [erase_eval_of_consistent c.program a input consistent]

/-- Exact circuit semantics via output guesses and their original consistency equations. -/
theorem eval_eq_iff_exists_consistent [∀ j, CommMonoid (State j)]
    (c : Circuit (signature State) n m) (input : Fin n → Bool) (outputs : Fin m → Bool) :
    c.eval interpretation input = outputs ↔
      ∃ a : Guess c.program, Consistent c.program a input ∧
        (eraseCircuit c a).eval ordinaryInterpretation input = outputs := by
  constructor
  · intro h
    refine ⟨actualGuess c.program input, actualGuess_consistent c.program input, ?_⟩
    rw [eval_eraseCircuit_of_consistent c _ input (actualGuess_consistent c.program input), h]
  · rintro ⟨a, consistent, h⟩
    rwa [eval_eraseCircuit_of_consistent c a input consistent] at h

end Algebraic.Aggregate
