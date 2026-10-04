/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Averaging
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Message.Bias

/-!
# Retaining multiple-primary conjunction messages

Designate two primary inputs at each marked gate and apply exact pair averaging.
The actual selected-pair predicate may hold at additional gates, so its count is
at least the designated-pair score.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Algebraic.Aggregate.Geometry
open scoped Classical

/-- A sending side retains the expected fraction of the circuit's marked gates. -/
theorem exists_subset_selectedPair_ratio {n g a : ℕ} (p : Program signature n g)
    (ha : 2 ≤ a) (han : a ≤ n) :
    ∃ U : Finset (Fin n), U.card = a ∧
      (((a : ℝ) * (a - 1) / ((n : ℝ) * (n - 1))) * multiCount p) ≤
        (Finset.univ.filter fun i : Fin g => SelectedPair (p.lines i) U).card := by
  let J := {i : Fin g // multiPrimary (p.lines i) = true}
  have witnesses (j : J) : ∃ i ∈ primaryInputs (p.lines j.val),
      ∃ t ∈ primaryInputs (p.lines j.val), i ≠ t :=
    ((multiPrimary_iff_exists_pair _).mp j.property).2
  choose left hl right hr distinct using witnesses
  obtain ⟨U, hU, bound⟩ := Entropy.exists_subset_pair_ratio ha han left right distinct
  have count : Fintype.card J = multiCount p := by
    rw [multiCount_eq_card_filter]
    exact Fintype.card_subtype _
  have selected :
      (Finset.univ.filter fun j : J => left j ∈ U ∧ right j ∈ U).card ≤
        (Finset.univ.filter fun i : Fin g => SelectedPair (p.lines i) U).card := by
    apply Finset.card_le_card_of_injOn (fun j : J => j.val)
    · intro j hj
      have pair := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((multiPrimary_iff_exists_pair _).mp j.property).1,
        left j, hl j, right j, hr j, distinct j, pair.1, pair.2⟩
    · intro i _ j _ same
      exact Subtype.ext same
  refine ⟨U, hU, ?_⟩
  rw [count] at bound
  exact bound.trans (by exact_mod_cast selected)

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
