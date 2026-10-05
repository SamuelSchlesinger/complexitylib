/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Compressed.Defs

/-!
# Exact semantics and mixing for joint aggregate compression

Factoring local contributions preserves every special equation. Guessing one final
joint state therefore recovers the true trace whenever the accumulated state agrees.
-/

@[expose] public section

namespace Algebraic.Aggregate.Compressed

variable {J : Type} {State : J → Type} [∀ j, CommMonoid (State j)] {n g : ℕ}
  {p : Program (signature State) n g} {M : Type} [CommMonoid M]

namespace Factorization

variable (c : Factorization p M)

/-- Decoding any partial aggregate recovers the original partial registers. -/
theorem decode_aggregate (S : Finset (Wire n g)) (values : Wire n g → Bool) :
    c.decode (c.aggregate S values) =
      fun gate : SpecialGate p => lineAggregate (p.lines gate) S values := by
  ext gate
  simp only [aggregate, map_prod, c.factor]
  exact prod_wireContribution p S values gate

/-- Decoding the true joint state gives the true special-output vector. -/
theorem guess_actual (input : Fin n → Bool) : c.guess (c.actual input) = actualGuess p input := by
  funext gate
  rw [guess, actual, decode_aggregate]
  symm
  exact (Program.lines_eval p interpretation input gate).symm.trans
    (special_eval_eq_readout (p.lines gate) gate.property input (p.eval interpretation input))

/-- Equal compressed keys imply equality of the original component keys. -/
theorem componentKey_eq (S : Finset (Wire n g)) (x y : Fin n → Bool)
    (same : c.componentKey S x = c.componentKey S y) :
    Algebraic.Aggregate.componentKey p S x = Algebraic.Aggregate.componentKey p S y := by
  apply Prod.ext
  · exact (c.guess_actual x).symm.trans
      ((congrArg c.guess (congrArg Prod.fst same)).trans (c.guess_actual y))
  · have h := congrArg c.decode (congrArg Prod.snd same)
    simp only [componentKey, decode_aggregate] at h
    convert h using 1 <;> rfl


/-- The compressed state preserves the exact component mixing argument. -/
theorem accepts_mix_of_componentKey_eq (S : Finset (Wire n g)) (closed : ClosedSet p S)
    (out : Wire n g) (x y : Fin n → Bool)
    (hx : p.trace interpretation x out = true) (hy : p.trace interpretation y out = true)
    (same : c.componentKey S x = c.componentKey S y) :
    p.trace interpretation (Cutwidth.SingleCut.mix S x y) out = true :=
  Algebraic.Aggregate.accepts_mix_of_componentKey_eq p S closed out x y hx hy
    (c.componentKey_eq S x y same)

/-- Checking the joint state checks every original special gate. -/
theorem consistent_of_aggregate_eq (state : M) (input : Fin n → Bool)
    (same : c.aggregate Finset.univ
      ((erase p (c.guess state)).trace ordinaryInterpretation input) = state) :
    Consistent p (c.guess state) input := by
  intro gate
  rw [special_eval_eq_readout _ gate.property]
  have h := congrFun (c.decode_aggregate Finset.univ
    ((erase p (c.guess state)).trace ordinaryInterpretation input)) gate
  rw [same] at h
  exact congrArg (p.lines gate).op.readout h.symm

/-- A guessed joint state accepts only if it is the actual joint state. -/
theorem aggregate_eq_iff (state : M) (input : Fin n → Bool) :
    c.aggregate Finset.univ
        ((erase p (c.guess state)).trace ordinaryInterpretation input) = state ↔
      state = c.actual input := by
  constructor
  · intro same
    have consistent := c.consistent_of_aggregate_eq state input same
    simpa only [Program.trace, erase_eval_of_consistent p (c.guess state) input consistent,
      actual] using same.symm
  · rintro rfl
    rw [c.guess_actual]
    simp only [Program.trace, erase_eval_actualGuess, actual]

end Factorization

omit [CommMonoid M] in
/-- Two copies of the compressed state fit in the stated budget. -/
theorem card_key_le [Fintype M] : Fintype.card (M × M) ≤ 2 ^ budget M := by
  rw [Fintype.card_prod, budget, two_mul, Nat.pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _)

end Algebraic.Aggregate.Compressed
