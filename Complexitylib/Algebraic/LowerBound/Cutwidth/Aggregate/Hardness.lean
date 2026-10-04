/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.LowerBound
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Family
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian

/-!
# The explicit lower bound with finite commutative aggregate gates

The fixed polynomial-time `sourceReductionHardFamily` keeps the unconditional
coefficient `1 + π/(3 arccos((1 + 2√2)/4))`, about `4.5625`, when binary circuits
are augmented with special gates whose total finite-state budget is sublinear.

Each special gate computes a Boolean predicate of the product of slot-dependent
contributions in a finite commutative monoid. Its budget is one guessed output
bit plus the ceiling binary logarithm of its number of states. The conclusion
counts all gates. Fan-in of special gates, fanout, depth, repeated slots, and
special-to-special connections are unrestricted. No extractor, compiler,
invertibility, or unproved graph hypothesis remains in the Gaussian theorem.

The existing extractor construction is due to Chattopadhyay--Liao; the cutwidth
lower-bound architecture follows Ryan Williams's private working note. This
extension replaces invertible accumulators by outgoing-transition counting.
See the sources in `FourN` and `Extractor.SourceReduction.Construction.Defs`.
-/

public section

namespace Algebraic.Cutwidth.Aggregate

variable {J : Type} {State : J → Type}
  [∀ j, CommMonoid (State j)] [∀ j, Fintype (State j)]

/-- Any proved graph-ordering coefficient transfers to the fixed explicit family for
mixed circuits with a sublinear budget of special-output guesses and monoid registers. -/
theorem sourceReductionHardFamily_eventually_lt_size_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C)
    (D : Nat → Nat)
    (hD : (fun n => (D n : ℝ)) =o[Filter.atTop] (fun n => (n : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ c : Circuit (Algebraic.Aggregate.signature State) n 1,
      c.Computes Algebraic.Aggregate.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
      Algebraic.Aggregate.budget c.program ≤ D n →
        (1 + 1 / A - ε) * n < c.size :=
  eventually_lt_size_of_orderingBound hA order Extractor.sourceReductionHardFamily D
    familyThreshold hD familyThreshold_log_isLittleO family_eventually_hard hε

/-- **The unconditional aggregate-gate extension.** The same fixed family in polynomial time
needs more than `(4.56249… - ε) n` total gates, even with arbitrary finite commutative-monoid
aggregate gates whose total output-guess and register budget is `o(n)`. -/
theorem sourceReductionHardFamily_eventually_lt_size_gaussian
    (D : Nat → Nat)
    (hD : (fun n => (D n : ℝ)) =o[Filter.atTop] (fun n => (n : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ c : Circuit (Algebraic.Aggregate.signature State) n 1,
      c.Computes Algebraic.Aggregate.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
      Algebraic.Aggregate.budget c.program ≤ D n →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
          c.size := by
  have bound := sourceReductionHardFamily_eventually_lt_size_of_orderingBound
    (State := State) (mul_pos two_pos Gaussian.frontierCoefficient_pos)
    Multigraph.exists_orderingBound_frontier D hD hε
  rwa [Gaussian.one_add_inv_two_mul_frontierCoefficient] at bound

/-- A convenient rational weakening of the unconditional aggregate-gate bound. -/
theorem sourceReductionHardFamily_eventually_lt_size_fortyOne_div_nine
    (D : Nat → Nat)
    (hD : (fun n => (D n : ℝ)) =o[Filter.atTop] (fun n => (n : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ c : Circuit (Algebraic.Aggregate.signature State) n 1,
      c.Computes Algebraic.Aggregate.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
      Algebraic.Aggregate.budget c.program ≤ D n →
        (41 / 9 - ε) * n < c.size := by
  have bound := sourceReductionHardFamily_eventually_lt_size_of_orderingBound
    (State := State) (by norm_num : (0 : ℝ) < 9 / 32)
    Multigraph.exists_orderingBound_nine_div_thirtyTwo D hD hε
  norm_num at bound ⊢
  exact bound

end Algebraic.Cutwidth.Aggregate
