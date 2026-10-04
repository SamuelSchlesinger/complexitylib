/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.LowerBound
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Asymptotics
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Circuit.RealCount
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Family

/-!
# Whole-basis lower bounds from aggregate capacity

The same fixed polynomial-time family requires almost `n` bits of exact aggregate
capacity, with no bound on the number of special gates. Binary gates cost one bit;
special gates cost `log₂ |M|`, without rounding or guessed-output bits. If every
special register has at most `r ≥ 2` states, the gate coefficient is `1 / log₂ r`.
In particular two-state aggregate gates preserve a coefficient of one at arbitrary
depth and fan-in, with repeated slots and arbitrary special-to-special connections.

The circuit-to-summary argument belongs to the classical communication-complexity
approach of Roychowdhury--Orlitsky--Siu (1994). The explicit family is the existing
Chattopadhyay--Liao construction, with its full input length and balanced padding.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate

open Filter Algebraic.Aggregate.Capacity

variable {J : Type} {State : J → Type}
  [∀ j, CommMonoid (State j)] [∀ j, Fintype (State j)]

/-- The fixed explicit family requires nearly one bit of exact aggregate capacity per
input, with no sparsity condition on the special gates. -/
theorem sourceReductionHardFamily_eventually_lt_realCapacity {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ c : Circuit (Algebraic.Aggregate.signature State) n 1,
      c.Computes Algebraic.Aggregate.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
      (1 - ε) * n < realCapacity c.program := by
  have numerical := eventually_lt_of_real_oneWayBound familyThreshold
    familyThreshold_log_isLittleO
    (Filter.Eventually.of_forall fun n => (familyThreshold_one_lt n).le) 7 hε
  filter_upwards [family_eventually_hard, numerical] with n hard bound c computes
  have heq : c.outputFunction Algebraic.Aggregate.interpretation 0 =
      Extractor.sourceReductionHardFamily n := by
    funext x
    exact congrFun (computes x) 0
  have finite := input_le_logCard_of_circuit c (K := familyThreshold n)
    (by simpa only [heq] using hard.1) (by simpa only [heq] using hard.2)
  rw [logb_card_key_eq_realCapacity] at finite
  exact bound _ finite

/-- The rounded per-register capacity also has leading coefficient one. -/
theorem sourceReductionHardFamily_eventually_lt_capacity {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ c : Circuit (Algebraic.Aggregate.signature State) n 1,
      c.Computes Algebraic.Aggregate.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
      (1 - ε) * n < capacity c.program := by
  filter_upwards [sourceReductionHardFamily_eventually_lt_realCapacity (State := State) hε]
    with n bound c computes
  exact (bound c computes).trans_le (realCapacity_le_capacity c.program)

/-- A uniform bound on state cardinalities gives a whole-basis gate lower bound,
with the unrounded coefficient `1 / log₂ states`. -/
theorem sourceReductionHardFamily_eventually_lt_size_of_register_card
    (states : Nat) (hs : 2 ≤ states) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ c : Circuit (Algebraic.Aggregate.signature State) n 1,
      c.Computes Algebraic.Aggregate.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
      (∀ gate : Algebraic.Aggregate.SpecialGate c.program,
        Fintype.card (Algebraic.Aggregate.Register c.program gate) ≤ states) →
      (1 / Real.logb 2 states - ε) * n < c.size := by
  have hlog : 0 < Real.logb 2 states :=
    Real.logb_pos one_lt_two (by exact_mod_cast (show 1 < states by lia))
  filter_upwards [sourceReductionHardFamily_eventually_lt_realCapacity
    (State := State) (show 0 < ε * Real.logb 2 states by positivity)]
    with n bound c computes registers
  have main := (bound c computes).trans_le
    (realCapacity_le_of_register_card c.program states hs registers)
  have inverse : 1 / Real.logb 2 states * Real.logb 2 states = 1 := by
    exact div_mul_cancel₀ 1 hlog.ne'
  nlinarith

/-- Arbitrarily many two-state aggregate gates, together with all binary Boolean
gates, still require more than `(1 - ε)n` gates. -/
theorem sourceReductionHardFamily_eventually_lt_size_two_state {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ c : Circuit (Algebraic.Aggregate.signature State) n 1,
      c.Computes Algebraic.Aggregate.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
      (∀ gate : Algebraic.Aggregate.SpecialGate c.program,
        Fintype.card (Algebraic.Aggregate.Register c.program gate) ≤ 2) →
      (1 - ε) * n < c.size := by
  simpa only [Nat.cast_ofNat, Real.logb_self_eq_one one_lt_two, div_one] using
    sourceReductionHardFamily_eventually_lt_size_of_register_card
      (State := State) 2 (by decide) hε

end Algebraic.Cutwidth.Aggregate
