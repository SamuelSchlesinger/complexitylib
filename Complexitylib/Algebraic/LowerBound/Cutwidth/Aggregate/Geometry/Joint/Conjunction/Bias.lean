/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Conjunction.Basic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Coordinates
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Numbers
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Finite.Counting
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Finite.Bias

/-!
# One-eighth bias for conjunctions using three or more primary variables

Three distinct required coordinates already force an event of probability at
most one eighth. Contradictory literals only decrease this probability. Its
binary entropy fits the graph bound's remaining-edge charge.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Entropy
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Three different primary variables force at least three independent Boolean coordinates. -/
theorem eight_mul_card_evalLiterals_le {L : Finset (V × Bool)}
    (three : 3 ≤ (literalVars L).card) :
    8 * (Finset.univ.filter fun x => evalLiterals L x = true).card ≤
      2 ^ Fintype.card V := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < (literalVars L).card by lia)
  obtain ⟨sa, hsa⟩ := mem_literalVars.mp ha
  obtain ⟨sb, hsb⟩ := mem_literalVars.mp hb
  obtain ⟨sc, hsc⟩ := mem_literalVars.mp hc
  have bound := pow_card_mul_card_le_of_forces_coordinates
    (tripleCoordinates a b c hab hac hbc) ![sa, sb, sc]
    (fun x => evalLiterals L x = true) (by
      intro x hx
      have holds : ∀ t ∈ L, x t.1 = t.2 := by
        simpa only [evalLiterals, decide_eq_true_eq] using hx
      funext i
      fin_cases i
      · exact holds (a, sa) hsa
      · exact holds (b, sb) hsb
      · exact holds (c, sc) hsc)
  simpa [Fintype.card_subtype] using bound

/-- A conjunction on at least three primary variables has at most one-eighth bit entropy. -/
noncomputable def evalLiteralsEighthWeightBoundOfThreeLe {L : Finset (V × Bool)}
    (three : 3 ≤ (literalVars L).card) :
    WeightBound (evalLiterals L) (Real.binEntropy (1 / 8)) := by
  apply WeightBound.ofTrueCountLE (evalLiterals L) (p := 1 / 8)
    (by norm_num) (by norm_num)
  have count : (8 : ℝ) *
      (Finset.univ.filter fun x => evalLiterals L x = true).card ≤
        (2 : ℝ) ^ Fintype.card V := by
    exact_mod_cast eight_mul_card_evalLiterals_le three
  simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  linarith

/-- A conjunction on at least three primary variables fits the remaining-edge graph cost. -/
noncomputable def evalLiteralsWeightBoundOfThreeLe {L : Finset (V × Bool)}
    (three : 3 ≤ (literalVars L).card) :
    WeightBound (evalLiterals L) (3 / 2 * Real.log 2 - Real.binEntropy (1 / 4)) :=
  (evalLiteralsEighthWeightBoundOfThreeLe three).mono binEntropy_eighth_le_chord

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
