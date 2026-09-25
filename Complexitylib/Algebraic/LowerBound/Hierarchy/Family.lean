/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Hierarchy.Finite
public import Complexitylib.Algebraic.CircuitFamily

/-!
# Nonuniform circuit size classes and hierarchy

`sizeClass bound` consists of Boolean function families computed by circuits
of size `O(bound n)`. The definition uses minimum gate count; an equivalence
exhibits actual circuit families with the same eventual multiplicative bound.
No uniformity or computability of the chosen circuits is asserted.

Below the Shannon scale, an upper budget separated from every constant
multiple of a lower budget by the `2 * n` interpolation overhead gives a
strict inclusion of size classes.
-/

@[expose] public section

namespace Algebraic.DeMorgan

open Filter

/-- One scalar Boolean function at each input width. -/
abbrev FunctionFamily := (n : Nat) → ScalarFunction Bool n

/-- Nonuniform size `O(bound n)`, allowing a constant factor and finitely many
exceptional widths. All internal De Morgan gates are counted. -/
def sizeClass (bound : Nat → Nat) : Set FunctionFamily :=
  {family | ∃ constant : Nat, ∀ᶠ n in atTop, complexity (family n) ≤ constant * bound n}

/-- Size-class membership is equivalent to the existence of an actual shared
circuit family with an eventual constant-factor size bound. -/
theorem mem_sizeClass_iff (family : FunctionFamily) (bound : Nat → Nat) :
    family ∈ sizeClass bound ↔
      ∃ circuits : Circuit.Family signature 1,
        circuits.Computes interpretation (Target.scalarFamily family) ∧
          ∃ constant : Nat, ∀ᶠ n in atTop, circuits.size n ≤ constant * bound n := by
  constructor
  · rintro ⟨constant, bounded⟩
    refine ⟨{ circuit := fun n => (minimumCircuit (family n)).circuit }, ?_, constant,
      bounded⟩
    intro n
    exact (minimumCircuit (family n)).computes
  · rintro ⟨circuits, computes, constant, bounded⟩
    refine ⟨constant, ?_⟩
    filter_upwards [bounded] with n hn
    exact (complexity_le (circuits.circuit n) (computes n)).trans hn

/-- Eventual domination of budgets gives inclusion of nonuniform size classes. -/
theorem sizeClass_mono {lower upper : Nat → Nat}
    (dominated : ∀ᶠ n in atTop, lower n ≤ upper n) :
    sizeClass lower ⊆ sizeClass upper := by
  rintro family ⟨constant, bounded⟩
  refine ⟨constant, ?_⟩
  filter_upwards [bounded, dominated] with n hn hle
  exact hn.trans (Nat.mul_le_mul_left constant hle)

/-- A nonuniform family simultaneously realizes an arbitrary eventual budget
below the Shannon scale, with additive error at most twice the width. -/
theorem exists_family_between (budget : Nat → Nat)
    (positive : ∀ᶠ n in atTop, 1 ≤ budget n)
    (small : ∀ᶠ n in atTop, budget n ≤ 2 ^ n / n) :
    ∃ family : FunctionFamily, ∀ᶠ n in atTop,
      budget n < complexity (family n) ∧ complexity (family n) ≤ budget n + 2 * n := by
  classical
  let P := fun n (function : ScalarFunction Bool n) =>
    budget n < complexity function ∧ complexity function ≤ budget n + 2 * n
  have available : ∀ᶠ n in atTop, ∃ function, P n function := by
    filter_upwards [eventually_exists_complexity_between, positive, small] with n hn hp hs
    exact hn (budget n) hp hs
  let family : FunctionFamily := fun n =>
    if existsFunction : ∃ function, P n function then Classical.choose existsFunction
    else fun _ => false
  refine ⟨family, ?_⟩
  filter_upwards [available] with n hn
  simpa only [family, dite_eq_left hn] using Classical.choose_spec hn

/-- General size hierarchy below the Shannon scale. The gap must absorb every
constant multiple of the smaller budget and the exact interpolation overhead. -/
theorem sizeClass_ssubset_of_gap (lower upper : Nat → Nat)
    (small : ∀ᶠ n in atTop, upper n ≤ 2 ^ n / n)
    (gap : ∀ constant : Nat, ∀ᶠ n in atTop,
      constant * lower n + 2 * n + 1 ≤ upper n) :
    sizeClass lower ⊂ sizeClass upper := by
  have inclusion : sizeClass lower ⊆ sizeClass upper := by
    apply sizeClass_mono
    filter_upwards [gap 1] with n hn
    omega
  let budget := fun n => upper n - 2 * n
  have positive : ∀ᶠ n in atTop, 1 ≤ budget n := by
    filter_upwards [gap 0] with n hn
    dsimp [budget]
    omega
  have budgetSmall : ∀ᶠ n in atTop, budget n ≤ 2 ^ n / n := by
    filter_upwards [small] with n hn
    exact (Nat.sub_le _ _).trans hn
  obtain ⟨family, between⟩ := exists_family_between budget positive budgetSmall
  have member : family ∈ sizeClass upper := by
    refine ⟨1, ?_⟩
    filter_upwards [between, gap 0] with n hn hg
    dsimp [budget] at hn
    omega
  have nonmember : family ∉ sizeClass lower := by
    rintro ⟨constant, bounded⟩
    have impossible : ∀ᶠ (_ : Nat) in atTop, False := by
      filter_upwards [between, bounded, gap constant] with n hn hb hg
      dsimp [budget] at hn
      omega
    obtain ⟨_, contradiction⟩ := impossible.exists
    exact contradiction
  exact Set.ssubset_iff_subset_ne.mpr ⟨inclusion, fun equal => nonmember (equal ▸ member)⟩

end Algebraic.DeMorgan
