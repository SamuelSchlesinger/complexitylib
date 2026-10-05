/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Compressed.Basic

/-!
# Observing a compressed candidate computation

One joint-state guess determines all special outputs. A product of local observations
checks that guess and the designated output, including after outside inputs are fixed.
-/

@[expose] public section

namespace Algebraic.Aggregate.Compressed

variable {J : Type} {State : J → Type} [∀ j, CommMonoid (State j)] {n g : ℕ}
  {p : Program (signature State) n g} {M : Type} [CommMonoid M]

/-- The joint aggregate and the multiplicative output flag. -/
abbrev Observation (M : Type) := M × ZMod 2

namespace Factorization

variable (c : Factorization p M)

/-- Each signal contributes once to the compressed state and designated output. -/
def observe (out wire : Wire n g) (value : Bool) : Observation M :=
  (c.contribution wire value, outputFlag out wire value)

/-- The final aggregate equals its guess and the designated output is true. -/
def AcceptObservation (state : M) (observed : Observation M) : Prop :=
  observed.1 = state ∧ observed.2 = 1

/-- A candidate accepts when its accumulated state agrees with its guess. -/
def AcceptsGuess (state : M) (out : Wire n g) (input : Fin n → Bool) : Prop :=
  c.aggregate Finset.univ ((erase p (c.guess state)).trace ordinaryInterpretation input) =
    state ∧ (erase p (c.guess state)).trace ordinaryInterpretation input out = true

/-- The observation predicate is the candidate's aggregate and output check. -/
theorem acceptObservation_iff (state : M) (out : Wire n g) (input : Fin n → Bool) :
    AcceptObservation state (∏ wire,
      c.observe out wire ((erase p (c.guess state)).trace ordinaryInterpretation input wire)) ↔
      c.AcceptsGuess state out input := by
  simp only [AcceptObservation, Prod.fst_prod, Prod.snd_prod, observe, prod_outputFlag,
    AcceptsGuess, aggregate]
  cases (erase p (c.guess state)).trace ordinaryInterpretation input out <;> simp

/-- An accepted state is the actual state and the original circuit accepts. -/
theorem acceptsGuess_iff (state : M) (out : Wire n g) (input : Fin n → Bool) :
    c.AcceptsGuess state out input ↔
      state = c.actual input ∧ p.trace interpretation input out = true := by
  unfold AcceptsGuess
  rw [c.aggregate_eq_iff]
  constructor
  · rintro ⟨rfl, output⟩
    rw [c.guess_actual] at output
    exact ⟨rfl, by simpa only [Program.trace, erase_eval_actualGuess] using output⟩
  · rintro ⟨rfl, output⟩
    rw [c.guess_actual]
    exact ⟨rfl, by simpa only [Program.trace, erase_eval_actualGuess] using output⟩

/-- Existentially guessing the compressed state preserves the original function. -/
theorem accepts_iff_exists_guess (out : Wire n g) (input : Fin n → Bool) :
    p.trace interpretation input out = true ↔ ∃ state, c.AcceptsGuess state out input := by
  simp only [c.acceptsGuess_iff, exists_eq_left]

/-- Fixed outside signals contribute to the final observation predicate. -/
def outsideObservation (state : M) (S : Finset (Wire n g)) (out : Wire n g)
    (fixed : Fin n → Bool) : Observation M :=
  ∏ wire ∈ Sᶜ, c.observe out wire
    ((erase p (c.guess state)).trace ordinaryInterpretation fixed wire)

/-- Component acceptance includes the already fixed outside observations. -/
def ComponentAccept (state : M) (S : Finset (Wire n g)) (out : Wire n g)
    (fixed : Fin n → Bool) (observed : Observation M) : Prop :=
  AcceptObservation state (observed * c.outsideObservation state S out fixed)

/-- Closed components retain exact compressed-state semantics after restriction. -/
theorem componentAccept_iff (state : M)
    (K : Cutwidth.MultiOutput.Internal.ClosedSet (erase p (c.guess state)))
    (out : Wire n g) (fixed input : Fin n → Bool)
    (agree : ∀ j, j ∉ Cutwidth.SingleCut.inputsIn K.carrier → input j = fixed j) :
    c.ComponentAccept state K.carrier out fixed
        (∏ wire : Cutwidth.MultiOutput.Internal.WireGraph.Signal K,
          c.observe out wire ((erase p (c.guess state)).trace ordinaryInterpretation input wire)) ↔
      c.AcceptsGuess state out input := by
  have outside : c.outsideObservation state K.carrier out fixed =
      ∏ wire ∈ K.carrierᶜ, c.observe out wire
        ((erase p (c.guess state)).trace ordinaryInterpretation input wire) := by
    apply Finset.prod_congr rfl
    intro wire hwire
    rw [Cutwidth.Aggregate.Wiring.trace_eq_of_outside_inputs_agree K ordinaryInterpretation
      agree wire (Finset.mem_compl.mp hwire)]
  have inside : (∏ wire : Cutwidth.MultiOutput.Internal.WireGraph.Signal K,
      c.observe out wire ((erase p (c.guess state)).trace ordinaryInterpretation input wire)) =
      ∏ wire ∈ K.carrier, c.observe out wire
        ((erase p (c.guess state)).trace ordinaryInterpretation input wire) := by
    exact Finset.prod_coe_sort K.carrier (fun wire => c.observe out wire
      ((erase p (c.guess state)).trace ordinaryInterpretation input wire))
  rw [ComponentAccept, outside, inside, Finset.prod_mul_prod_compl]
  exact c.acceptObservation_iff state out input

end Factorization

omit [CommMonoid M] in
/-- The guess and observation use only one output bit beyond the compressed budget. -/
theorem card_guess_mul_card_observation_le [Fintype M] :
    Fintype.card M * Fintype.card (Observation M) ≤ 2 ^ (budget M + 1) := by
  rw [show Fintype.card (Observation M) = Fintype.card M * 2 by simp [Observation], pow_succ]
  simpa only [← mul_assoc, ← Fintype.card_prod] using
    Nat.mul_le_mul_right 2 (card_key_le (M := M))

end Algebraic.Aggregate.Compressed
