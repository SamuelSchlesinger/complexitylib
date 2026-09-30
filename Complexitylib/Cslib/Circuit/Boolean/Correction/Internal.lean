/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Cslib.Circuit.Boolean.Correction.Defs

/-!
# Circuits for support-masked corrections

The support circuit is shared by every corrected output. The labels are a
single circuit required to be correct only on the support, so its internal
sharing is preserved too. Each selected output adds one mask and four XOR gates.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Correction.Internal

variable {n m : ℕ}

/-- Wire carrying an old output in the correction interface. -/
def oldWire (outputs : Finset (Fin m)) (j : Fin m) : Fin (m + 1 + outputs.card) :=
  Fin.castAdd outputs.card (Fin.castAdd 1 j)

/-- Wire carrying the common support indicator. -/
def supportWire (outputs : Finset (Fin m)) : Fin (m + 1 + outputs.card) :=
  Fin.castAdd outputs.card (Fin.natAdd m (0 : Fin 1))

/-- Wire carrying the partial correction for an active coordinate. -/
noncomputable def labelWire (outputs : Finset (Fin m)) (j : Fin m) (hj : j ∈ outputs) :
    Fin (m + 1 + outputs.card) :=
  Fin.natAdd (m + 1) (outputs.equivFin ⟨j, hj⟩)

/-- Mask a supplied correction and XOR it into a selected output. -/
noncomputable def patch (outputs : Finset (Fin m)) :
    (Fin (m + 1 + outputs.card) → Bool) → Fin m → Bool :=
  fun x j => if hj : j ∈ outputs then
    Bool.xor (x (oldWire outputs j))
      (x (supportWire outputs) && x (labelWire outputs j hj))
    else x (oldWire outputs j)

theorem exists_patch (outputs : Finset (Fin m)) :
    ∃ c : Circuit signature (m + 1 + outputs.card) m,
      c.Computes interpretation (patch outputs) ∧ c.size ≤ 5 * outputs.card := by
  classical
  have input (wire : Fin (m + 1 + outputs.card)) :
      Synthesis interpretation (inputs (m + 1 + outputs.card)) {fun x => x wire} 0 :=
    Synthesis.of_mem ⟨wire, rfl⟩
  have each (j : Fin m) :
      Synthesis interpretation (inputs (m + 1 + outputs.card))
        {fun x => patch outputs x j} (if j ∈ outputs then 5 else 0) := by
    by_cases hj : j ∈ outputs
    · let mask : BooleanFunction (m + 1 + outputs.card) :=
        fun x => x (supportWire outputs) && x (labelWire outputs j hj)
      have hm : Synthesis interpretation (inputs (m + 1 + outputs.card)) {mask} 1 := by
        simpa [mask] using
          (input (supportWire outputs)).and (input (labelWire outputs j hj))
      have hx : Synthesis interpretation (inputs (m + 1 + outputs.card) ∪ {mask})
          {fun x => Bool.xor (x (oldWire outputs j)) (mask x)} 4 :=
        Synthesis.xor_of_mem (Or.inl ⟨oldWire outputs j, rfl⟩) (by simp)
      simpa [patch, hj, mask] using hm.trans hx
    · simpa [patch, hj] using input (oldWire outputs j)
  have all := Synthesis.family (fun j x => patch outputs x j)
    (fun j => if j ∈ outputs then 5 else 0) each
  have budget : (∑ j : Fin m, if j ∈ outputs then 5 else 0) = 5 * outputs.card := by
    rw [← Finset.sum_filter]
    have h : Finset.univ.filter (fun j : Fin m => j ∈ outputs) = outputs := by ext; simp
    simp [h, Nat.mul_comm]
  rw [budget] at all
  exact all.exists_circuit_outputs

theorem exists_correction
    (f g : (Fin n → Bool) → Fin m → Bool) (s : Set (Fin n → Bool))
    (outputs : Finset (Fin m))
    (outside : ∀ x ∉ s, f x = g x)
    (unchanged : ∀ j ∉ outputs, ∀ x, f x j = g x j)
    (support : Circuit signature n 1) (hs : support.Computes interpretation (indicator s))
    (labels : Circuit signature n outputs.card)
    (hl : labels.ComputesOn interpretation s (errorVector f g outputs)) :
    ∃ c : Circuit signature (n + m) m,
      (∀ x, c.eval interpretation (Fin.append x (g x)) = f x) ∧
        c.size ≤ support.size + labels.size + 5 * outputs.card := by
  classical
  obtain ⟨finish, hf, hb⟩ := exists_patch outputs
  change ∀ x, finish.eval interpretation x = patch outputs x at hf
  let readInput : Circuit signature (n + m) n := Circuit.wiring signature (Fin.castAdd m)
  let old : Circuit signature (n + m) m := Circuit.wiring signature (Fin.natAdd n)
  let sources := (old.append (support.comp readInput)).append (labels.comp readInput)
  refine ⟨finish.comp sources, ?_, ?_⟩
  · intro x
    simp only [Circuit.eval_comp, sources, Circuit.eval_append, old, readInput,
      Circuit.eval_wiring, Fin.append_comp_natAdd, Fin.append_comp_castAdd, hf]
    funext j
    rw [hs x]
    by_cases hj : j ∈ outputs
    · simp only [patch, dite_eq_left hj, oldWire, supportWire, labelWire,
        Fin.append_left, Fin.append_right, indicator]
      by_cases hx : x ∈ s
      · rw [show labels.eval interpretation x = errorVector f g outputs x from hl hx]
        simp only [errorVector, Equiv.symm_apply_apply, decide_eq_true hx, Bool.true_and]
        cases f x j <;> cases g x j <;> rfl
      · simp [hx, outside x hx]
    · simp [patch, hj, oldWire, unchanged j hj x]
  · simp only [Circuit.size_comp, sources, Circuit.size_append, old, readInput,
      Circuit.size_wiring]
    omega

theorem complexityGiven_bound
    (f g : (Fin n → Bool) → Fin m → Bool) (s : Set (Fin n → Bool))
    (outputs : Finset (Fin m))
    (outside : ∀ x ∉ s, f x = g x)
    (unchanged : ∀ j ∉ outputs, ∀ x, f x j = g x j) :
    complexityGiven interpretation f g ≤ complexity interpretation (indicator s) +
      complexityOn interpretation s (errorVector f g outputs) + 5 * outputs.card := by
  obtain ⟨support, hs, hsize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := indicator s)
  obtain ⟨labels, hl, hlabels⟩ := exists_computesOn_size_eq_ecomplexityOn
    (I := interpretation) (S := s) (f := errorVector f g outputs)
    (ecomplexityOn_ne_top_iff.mp ecomplexityOn_ne_top)
  have hlabels' : labels.size = complexityOn interpretation s (errorVector f g outputs) := by
    exact_mod_cast hlabels.trans natCast_complexityOn.symm
  obtain ⟨c, hc, hcost⟩ := exists_correction f g s outputs outside unchanged support hs labels hl
  have bound := (ecomplexityGiven_le_of_eval f g c hc).trans
    (show (c.size : ℕ∞) ≤
      (complexity interpretation (indicator s) +
        complexityOn interpretation s (errorVector f g outputs) + 5 * outputs.card : ℕ) by
      exact_mod_cast (by simpa [hsize, hlabels'] using hcost))
  rw [← natCast_complexityGiven] at bound
  exact_mod_cast bound

end Cslib.Circuits.Boolean.Correction.Internal
