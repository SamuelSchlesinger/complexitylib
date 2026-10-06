/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.Compression
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Counting multigraph boundaries

Parallel edges are distinct records throughout. The simple support supplies distances;
the multigraph supplies degrees, crossing counts, and the core density estimate.
-/

@[expose] public section

namespace Complexity.Frontier.Multigraph

open Set Finset

variable {V E : Type*} (G : Multigraph V E)

/-- The simple support of a multigraph, with loops discarded. -/
def support : SimpleGraph V := SimpleGraph.fromRel G.Adj

theorem support_adj {u v : V} : G.support.Adj u v ↔ u ≠ v ∧ G.Adj u v := by
  rw [support, SimpleGraph.fromRel_adj]
  exact and_congr_right fun _ => ⟨fun h => h.elim id Adj.symm, Or.inl⟩

theorem support_src_tgt (hl : G.Loopless) (e : E) : G.support.Adj (G.src e) (G.tgt e) :=
  G.support_adj.mpr ⟨hl e, e, Or.inl ⟨rfl, rfl⟩⟩

/-- Distinct neighbours inject into incident edges. -/
theorem support_degree_le [Finite E] [G.support.LocallyFinite] (v : V) :
    G.support.degree v ≤ (G.edgesAt v).ncard := by
  classical
  rw [← SimpleGraph.ncard_neighborSet]
  have hs : G.support.neighborSet v ⊆
      (fun e => if G.src e = v then G.tgt e else G.src e) '' G.edgesAt v := by
    intro w hw
    obtain ⟨hne, e, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ := G.support_adj.mp hw
    · exact ⟨e, Or.inl hs, by simp [hs, ht]⟩
    · exact ⟨e, Or.inr ht, by simp [hs, Ne.symm hne]⟩
  exact (ncard_le_ncard hs).trans (ncard_image_le (toFinite _))

open Classical in
/-- A finite cut, retaining edge multiplicity. -/
noncomputable def crossingFinset [Fintype E] (S : Finset V) : Finset E :=
  univ.filter fun e => ¬(G.src e ∈ S ↔ G.tgt e ∈ S)

@[simp] theorem mem_crossingFinset [Fintype E] {S : Finset V} {e : E} :
    e ∈ G.crossingFinset S ↔ ¬(G.src e ∈ S ↔ G.tgt e ∈ S) := by
  classical
  simp [crossingFinset]

theorem card_crossingFinset [Fintype E] (S : Finset V) :
    (G.crossingFinset S).card = (G.cut (S : Set V)).ncard := by
  rw [← ncard_coe_finset]
  congr 1
  ext e
  simp [mem_cut]

/-- The incident-edge union pays once per edge, at most the degree budget per vertex. -/
theorem ncard_touching_le {d : ℕ} (hd : G.MaxDegreeLE d) (S : Finset V) :
    (G.touching (S : Set V)).ncard ≤ d * S.card := by
  have heq : G.touching (S : Set V) = ⋃ v ∈ S, G.edgesAt v := by
    ext e
    simp only [touching, mem_ofPred_eq, mem_coe, mem_iUnion, edgesAt, Incident]
    aesop
  rw [heq]
  calc _ ≤ ∑ v ∈ S, (G.edgesAt v).ncard := Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ _v ∈ S, d := sum_le_sum fun v _ => hd v
    _ = d * S.card := by simp [Nat.mul_comm]

theorem card_edges_le [Fintype V] {d : ℕ} (hd : G.MaxDegreeLE d) :
    Nat.card E ≤ d * Fintype.card V := by
  have h := G.ncard_touching_le hd (univ : Finset V)
  simpa [touching] using h

/-- Weighted handshaking, counting parallel edges with multiplicity. -/
theorem sum_degree_mul [Fintype V] [Fintype E] (hl : G.Loopless) (w : V → ℕ) :
    (∑ v, (G.edgesAt v).ncard * w v) = ∑ e, (w (G.src e) + w (G.tgt e)) := by
  classical
  have hf (v : V) : (G.edgesAt v).ncard * w v =
      ∑ e, if G.Incident v e then w v else 0 := by
    rw [← Finset.sum_filter, sum_const, smul_eq_mul]
    congr 1
    rw [← ncard_coe_finset]
    congr 1
    ext e
    simp [edgesAt]
  simp_rw [hf]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  have hi (v : V) : (if G.Incident v e then w v else 0) =
      (if v = G.src e then w v else 0) + (if v = G.tgt e then w v else 0) := by
    simp only [Incident]
    by_cases hs : v = G.src e <;> by_cases ht : v = G.tgt e <;>
      simp_all [eq_comm, hl e]
  simp_rw [hi]
  rw [sum_add_distrib]
  simp

/-- Terminal-core density in every degree: adjacent degree sums at least `d + 3`
force `3d |V| ≤ (d + 3) |E|`. -/
theorem core_density [Fintype V] [Fintype E] (hl : G.Loopless) {d : ℕ}
    (hlo : ∀ v, 3 ≤ (G.edgesAt v).ncard) (hhi : G.MaxDegreeLE d)
    (hadj : ∀ e, d + 3 ≤ (G.edgesAt (G.src e)).ncard + (G.edgesAt (G.tgt e)).ncard) :
    3 * d * Fintype.card V ≤ (d + 3) * Fintype.card E := by
  let w (v : V) := d + 3 - (G.edgesAt v).ncard
  have hv (v : V) : 3 * d ≤ (G.edgesAt v).ncard * w v := by
    have h1 := hlo v
    have h2 := hhi v
    have hw : w v + (G.edgesAt v).ncard = d + 3 := by dsimp [w]; lia
    have hprod : 0 ≤ ((G.edgesAt v).ncard - 3) * (d - (G.edgesAt v).ncard) := Nat.zero_le _
    have hsub1 : (G.edgesAt v).ncard - 3 + 3 = (G.edgesAt v).ncard := by lia
    have hsub2 : d - (G.edgesAt v).ncard + (G.edgesAt v).ncard = d := by lia
    nlinarith
  have he (e : E) : w (G.src e) + w (G.tgt e) ≤ d + 3 := by
    have := hadj e
    have := hhi (G.src e)
    have := hhi (G.tgt e)
    dsimp [w]
    lia
  calc 3 * d * Fintype.card V = ∑ _v : V, 3 * d := by simp [Nat.mul_comm]
    _ ≤ ∑ v, (G.edgesAt v).ncard * w v := sum_le_sum fun v _ => hv v
    _ = ∑ e, (w (G.src e) + w (G.tgt e)) := G.sum_degree_mul hl w
    _ ≤ ∑ _e : E, (d + 3) := sum_le_sum fun e _ => he e
    _ = (d + 3) * Fintype.card E := by simp [Nat.mul_comm]

end Complexity.Frontier.Multigraph
