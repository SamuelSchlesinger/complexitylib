/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Multigraph
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Independent local improvements of all threshold cuts

Changing the keys at an independent set of vertices to the medians of their neighbours
cannot increase any threshold cut. Independence matters: simultaneous majority updates at
adjacent vertices need not improve a cut. The exact accounting identity also records the
gain needed for a probabilistic improvement of the Gaussian layout constant.
-/

@[expose] public section

namespace Complexity.Frontier.Multigraph

open Finset

variable {V E : Type*} [Fintype E] (G : Multigraph V E)

/-- Indicator that the endpoints receive different colours. -/
def crossing (c : V → Bool) (e : E) : ℕ := if c (G.src e) = c (G.tgt e) then 0 else 1

/-- Number of edges crossing a Boolean cut. -/
def cutSize (c : V → Bool) : ℕ := ∑ e, G.crossing c e

/-- The sum definition is the ordinary multigraph cut cardinality. -/
theorem cutSize_eq_ncard (c : V → Bool) : G.cutSize c = (G.cut {v | c v = true}).ncard := by
  classical
  have he (e : E) : G.crossing c e = if c (G.src e) ≠ c (G.tgt e) then 1 else 0 := by
    unfold crossing
    split_ifs <;> simp_all
  simp only [cutSize, he, Finset.sum_boole]
  have hc : (↑(Finset.univ.filter fun e => c (G.src e) ≠ c (G.tgt e)) : Set E) =
      G.cut {v | c v = true} := by
    ext e
    cases hs : c (G.src e) <;> cases ht : c (G.tgt e) <;> simp [mem_cut, hs, ht]
  rw [← hc, Set.ncard_coe_finset]
  rfl

/-- Number of crossing edges incident to a vertex. -/
noncomputable def localCut (c : V → Bool) (v : V) : ℕ := by
  classical
  exact ∑ e, if G.Incident v e then G.crossing c e else 0

open Classical in
/-- Incident-edge costs are counted once when the selected vertices are independent. -/
theorem sum_incident_independent (I : Finset V)
    (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I)) (w : E → ℕ) :
    (∑ v ∈ I, ∑ e, if G.Incident v e then w e else 0) =
      ∑ e, if G.src e ∈ I ∨ G.tgt e ∈ I then w e else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hs : G.src e ∈ I
  · have ht : G.tgt e ∉ I := fun ht => hI e ⟨hs, ht⟩
    have he : ∀ v ∈ I, G.Incident v e ↔ v = G.src e := by
      intro v hv
      unfold Incident
      constructor
      · rintro (h | h)
        · exact h.symm
        · exact False.elim (ht (h.symm ▸ hv))
      · intro h; exact Or.inl h.symm
    simp only [hs, true_or, ite_true]
    calc (∑ v ∈ I, if G.Incident v e then w e else 0) =
        ∑ v ∈ I, if v = G.src e then w e else 0 :=
          Finset.sum_congr rfl fun v hv => by rw [he v hv]
      _ = _ := by simp [hs]
  · by_cases ht : G.tgt e ∈ I
    · have he : ∀ v ∈ I, G.Incident v e ↔ v = G.tgt e := by
        intro v hv
        unfold Incident
        constructor
        · rintro (h | h)
          · exact False.elim (hs (h.symm ▸ hv))
          · exact h.symm
        · intro h; exact Or.inr h.symm
      simp only [ht, or_true, ite_true]
      calc (∑ v ∈ I, if G.Incident v e then w e else 0) =
          ∑ v ∈ I, if v = G.tgt e then w e else 0 :=
            Finset.sum_congr rfl fun v hv => by rw [he v hv]
        _ = _ := by simp [ht]
    · rw [ite_eq_right (not_or.mpr ⟨hs, ht⟩)]
      apply Finset.sum_eq_zero
      intro v hv
      have he : ¬G.Incident v e := by
        rintro (he | he) <;> subst v <;> contradiction
      simp [he]

/-- Exact change in a cut after updating an independent set. -/
theorem cutSize_add_local_eq (I : Finset V) (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I))
    (c c' : V → Bool) (hfix : ∀ v, v ∉ I → c' v = c v) :
    G.cutSize c' + ∑ v ∈ I, G.localCut c v =
      G.cutSize c + ∑ v ∈ I, G.localCut c' v := by
  classical
  simp only [localCut, G.sum_incident_independent I hI, cutSize, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : G.src e ∈ I ∨ G.tgt e ∈ I
  · simp [he, Nat.add_comm]
  · rw [not_or] at he
    simp [he.1, he.2, crossing, hfix _ he.1, hfix _ he.2]

/-- Independent local minimizers improve the entire cut. -/
theorem cutSize_le_of_local (I : Finset V) (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I))
    (c c' : V → Bool) (hfix : ∀ v, v ∉ I → c' v = c v)
    (hlocal : ∀ v ∈ I, G.localCut c' v ≤ G.localCut c v) : G.cutSize c' ≤ G.cutSize c := by
  have H := G.cutSize_add_local_eq I hI c c' hfix
  have h := Finset.sum_le_sum hlocal
  lia

theorem cutSize_lt_of_local (I : Finset V) (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I))
    (c c' : V → Bool) (hfix : ∀ v, v ∉ I → c' v = c v)
    (hlocal : ∀ v ∈ I, G.localCut c' v ≤ G.localCut c v)
    (hstrict : ∃ v ∈ I, G.localCut c' v < G.localCut c v) : G.cutSize c' < G.cutSize c := by
  have H := G.cutSize_add_local_eq I hI c c' hfix
  have h := Finset.sum_lt_sum hlocal hstrict
  lia

/-- The gain is the sum of local gains, with no loss from overlapping updated stars. -/
theorem cutSize_eq_add_gain (I : Finset V) (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I))
    (c c' : V → Bool) (hfix : ∀ v, v ∉ I → c' v = c v)
    (hlocal : ∀ v ∈ I, G.localCut c' v ≤ G.localCut c v) :
    G.cutSize c = G.cutSize c' + ∑ v ∈ I, (G.localCut c v - G.localCut c' v) := by
  have H := G.cutSize_add_local_eq I hI c c' hfix
  have hs : (∑ v ∈ I, G.localCut c v) =
      (∑ v ∈ I, G.localCut c' v) + ∑ v ∈ I, (G.localCut c v - G.localCut c' v) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v hv => by have := hlocal v hv; lia
  lia

/-- The other endpoint of an incident edge. -/
noncomputable def otherEnd (v : V) (e : E) : V := by
  classical
  exact if G.src e = v then G.tgt e else G.src e

omit [Fintype E] in
theorem crossing_eq_otherEnd (c : V → Bool) (v : V) {e : E} (he : G.Incident v e) :
    G.crossing c e = if c v = c (G.otherEnd v e) then 0 else 1 := by
  classical
  by_cases hs : G.src e = v
  · simp [crossing, otherEnd, hs]
  · have ht : G.tgt e = v := he.resolve_left hs
    simp [crossing, otherEnd, hs, ht, eq_comm]

end Complexity.Frontier.Multigraph

namespace Complexity.Frontier.LocalLayout

/-- The median of three keys, expressed using lattice operations. -/
def median3 (a b c : ℝ) : ℝ := max (min a b) (min (max a b) c)

/-- The number of the three neighbour colours that differ from `c`. -/
def disagreements3 (c : Bool) (neighbours : Fin 3 → Bool) : ℕ :=
  ∑ i, if c = neighbours i then 0 else 1

/-- At every threshold, the median agrees with a majority of the neighbours. -/
theorem disagreements_median3_le (k : Fin 3 → ℝ) (t : ℝ) (c : Bool) :
    disagreements3 (decide (median3 (k 0) (k 1) (k 2) < t)) (fun i => decide (k i < t)) ≤
      disagreements3 c (fun i => decide (k i < t)) := by
  classical
  by_cases h0 : k 0 < t <;> by_cases h1 : k 1 < t <;> by_cases h2 : k 2 < t <;>
    cases c <;> simp [disagreements3, median3, max_lt_iff, min_lt_iff,
      Fin.sum_univ_succ, h0, h1, h2]
  all_goals simp_all [← not_lt]

open Multigraph

variable {V E : Type*} [Fintype E] (G : Multigraph V E)

/-- Enumerating the three incident edges supplies exactly the star identity used below. -/
theorem localCut_eq_star (v : V) (edges : Fin 3 ≃ G.edgesAt v) (c : V → Bool) :
    G.localCut c v = disagreements3 (c v) (fun i => c (G.otherEnd v (edges i).1)) := by
  classical
  have hsum : G.localCut c v = ∑ i, G.crossing c (edges i).1 := by
    rw [Multigraph.localCut, ← Finset.sum_filter]
    symm
    apply Finset.sum_bij (fun i _ => (edges i).1)
    · intro i _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (edges i).2⟩
    · intro i _ j _ h
      exact edges.injective (Subtype.ext h)
    · intro e he
      refine ⟨edges.symm ⟨e, (Finset.mem_filter.mp he).2⟩, Finset.mem_univ _, ?_⟩
      simp
    · intro i _
      rfl
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  exact G.crossing_eq_otherEnd c v (edges i).2

omit [Fintype E] in
/-- Independence keeps every neighbour of an updated vertex fixed. -/
theorem otherEnd_notMem (I : Finset V) (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I))
    {v : V} (hv : v ∈ I) {e : E} (he : G.Incident v e) : G.otherEnd v e ∉ I := by
  classical
  unfold Multigraph.otherEnd
  split_ifs with hs
  · exact fun ht => hI e ⟨hs ▸ hv, ht⟩
  · have ht := he.resolve_left hs
    exact fun hs => hI e ⟨hs, ht ▸ hv⟩

/-- Replace the selected keys by the medians of their three neighbour keys. -/
noncomputable def improve (I : Finset V) (neighbours : V → Fin 3 → V) (key : V → ℝ) : V → ℝ := by
  classical
  exact fun v => if v ∈ I then
    median3 (key (neighbours v 0)) (key (neighbours v 1)) (key (neighbours v 2)) else key v

theorem improve_of_mem {I : Finset V} (neighbours : V → Fin 3 → V) (key : V → ℝ)
    {v : V} (hv : v ∈ I) : improve I neighbours key v =
      median3 (key (neighbours v 0)) (key (neighbours v 1)) (key (neighbours v 2)) := by
  simp [improve, hv]

theorem improve_of_not_mem {I : Finset V} (neighbours : V → Fin 3 → V) (key : V → ℝ)
    {v : V} (hv : v ∉ I) : improve I neighbours key v = key v := by
  simp [improve, hv]

/-- **All thresholds improve simultaneously.** The star identity makes the three-neighbour
representation explicit; it is satisfied by an enumeration of each cubic graph's neighbours. -/
theorem cutSize_improve_le (I : Finset V) (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I))
    (neighbours : V → Fin 3 → V)
    (hstar : ∀ v ∈ I, ∀ c : V → Bool,
      G.localCut c v = disagreements3 (c v) (fun i => c (neighbours v i)))
    (hout : ∀ v ∈ I, ∀ i, neighbours v i ∉ I) (key : V → ℝ) (t : ℝ) :
    G.cutSize (fun v => decide (improve I neighbours key v < t)) ≤
      G.cutSize (fun v => decide (key v < t)) := by
  classical
  refine G.cutSize_le_of_local I hI _ _ (fun v hv => by simp [improve, hv]) ?_
  intro v hv
  rw [hstar v hv, hstar v hv]
  have H : (fun i => decide (improve I neighbours key (neighbours v i) < t)) =
      (fun i => decide (key (neighbours v i) < t)) := by
    funext i
    rw [improve_of_not_mem neighbours key (hout v hv i)]
  rw [improve_of_mem neighbours key hv, H]
  exact disagreements_median3_le (fun i => key (neighbours v i)) t _

/-- A cubic multigraph can use its actual incident-edge enumerations, with no additional
assumption about boundary states or the distribution of keys. -/
theorem cutSize_improve_cubic_le (I : Finset V)
    (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I))
    (edges : ∀ v, Fin 3 ≃ G.edgesAt v) (key : V → ℝ) (t : ℝ) :
    G.cutSize (fun v => decide (improve I
      (fun v i => G.otherEnd v (edges v i).1) key v < t)) ≤
        G.cutSize (fun v => decide (key v < t)) :=
  cutSize_improve_le G I hI _ (fun v _ c => localCut_eq_star G v (edges v) c)
    (fun _ hv i => otherEnd_notMem G I hI hv (edges _ i).2) key t

end Complexity.Frontier.LocalLayout
