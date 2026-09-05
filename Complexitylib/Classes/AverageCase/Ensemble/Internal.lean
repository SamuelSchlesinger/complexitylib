/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.Ensemble.Defs

/-!
# Exact dyadic distribution ensembles -- proof internals

The results reduce ensemble probability to exact counting over the underlying
Boolean seed space. In particular, total mass follows by partitioning seeds into
sample fibers, and product probability follows from the explicit block bijection.
-/


public section

universe u v

namespace Complexity

namespace DyadicEnsemble

variable {α : Type u} {β : Type v}

theorem probability_nonneg_internal (D : DyadicEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    0 ≤ D.probability n P :=
  eventProb_nonneg _

theorem probability_le_one_internal (D : DyadicEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    D.probability n P ≤ 1 :=
  eventProb_le_one _

theorem probability_false_internal (D : DyadicEnsemble α) (n : ℕ) :
    D.probability n (fun _ => False) = 0 := by
  simp [probability, event]

theorem probability_true_internal (D : DyadicEnsemble α) (n : ℕ) :
    D.probability n (fun _ => True) = 1 := by
  simp [probability, event]

theorem probability_not_internal (D : DyadicEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    D.probability n (fun x => ¬ P x) = 1 - D.probability n P := by
  have hevent : D.event n (fun x => ¬ P x) = (D.event n P)ᶜ := by
    ext seed
    simp [event]
  rw [probability, hevent, eventProb_compl]
  rfl

theorem probability_or_le_internal (D : DyadicEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    D.probability n (fun x => P x ∨ Q x) ≤
      D.probability n P + D.probability n Q := by
  have hevent : D.event n (fun x => P x ∨ Q x) = D.event n P ∪ D.event n Q := by
    ext seed
    simp [event]
  rw [probability, hevent]
  exact eventProb_union_le _ _

theorem probability_mono_internal (D : DyadicEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x → Q x) :
    D.probability n P ≤ D.probability n Q := by
  unfold probability eventProb
  gcongr
  intro seed hseed
  rw [show D.event n P =
      Finset.univ.filter (fun seed => P (D.sample n seed)) from rfl] at hseed
  rw [show D.event n Q =
      Finset.univ.filter (fun seed => Q (D.sample n seed)) from rfl]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hseed ⊢
  exact hPQ _ hseed

theorem probability_congr_internal (D : DyadicEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x ↔ Q x) :
    D.probability n P = D.probability n Q := by
  unfold probability
  apply congrArg eventProb
  ext seed
  rw [show D.event n P =
      Finset.univ.filter (fun seed => P (D.sample n seed)) from rfl]
  rw [show D.event n Q =
      Finset.univ.filter (fun seed => Q (D.sample n seed)) from rfl]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hPQ _

theorem probability_map_internal (D : DyadicEnsemble α) (f : α → β)
    (n : ℕ) (P : β → Prop) [DecidablePred P] :
    (D.map f).probability n P = D.probability n (fun x => P (f x)) := by
  rfl

theorem sum_mass_eq_one_internal [DecidableEq α]
    (D : DyadicEnsemble α) (n : ℕ) :
    ∑ x ∈ D.support n, D.mass n x = 1 := by
  have hmaps :
      ((Finset.univ : Finset (Fin (D.seedLength n) → Bool)) :
          Set (Fin (D.seedLength n) → Bool)).MapsTo
        (D.sample n) (D.support n) := by
    intro seed _
    simp [support]
  have hpartition := eventProb_eq_sum_fiberwise
    (Finset.univ : Finset (Fin (D.seedLength n) → Bool))
    (D.support n) (D.sample n) hmaps
  rw [eventProb_univ] at hpartition
  simpa [mass, probability, event] using hpartition.symm

theorem probability_product_internal (D : DyadicEnsemble α)
    (E : DyadicEnsemble β) (n : ℕ) (P : α → Prop) (Q : β → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (D.product E).probability n (fun xy => P xy.1 ∧ Q xy.2) =
      D.probability n P * E.probability n Q := by
  exact eventProb_block
    (fun seed : Fin (D.seedLength n) → Bool => P (D.sample n seed))
    (fun seed : Fin (E.seedLength n) → Bool => Q (E.sample n seed))

theorem probability_dirac_internal (x : ℕ → α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    (dirac x).probability n P = if P (x n) then 1 else 0 := by
  by_cases hP : P (x n)
  · rw [ite_eq_left hP]
    unfold probability
    rw [show (dirac x).event n P = Finset.univ by
      ext seed
      simp [event, dirac, hP]]
    exact eventProb_univ
  · rw [ite_eq_right hP]
    unfold probability
    rw [show (dirac x).event n P = ∅ by
      refine Finset.eq_empty_of_forall_notMem fun seed hseed => hP ?_
      exact (Finset.mem_filter.mp hseed).2]
    exact eventProb_empty

theorem probability_uniformBits_internal (n : ℕ)
    (P : List Bool → Prop) [DecidablePred P] :
    uniformBits.probability n P =
      eventProb (Finset.univ.filter fun seed : Fin n → Bool =>
        P (List.ofFn seed)) := by
  rfl

end DyadicEnsemble

end Complexity
