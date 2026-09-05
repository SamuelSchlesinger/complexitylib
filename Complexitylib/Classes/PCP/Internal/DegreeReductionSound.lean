/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.CloudDisagreement

/-!
# Soundness of degree reduction

Completeness was proved in `DegreeReduction`; this is the other half. An
assignment `A` of the reduced system is decoded to a vertex assignment by
plurality, and the unsatisfied darts of `A` are charged against the edges that
decoding fails:

* **cloud-links** pay for every half-edge that disagrees with its vertex's
  plurality label (`CloudDisagreement.total_cloud_charge`), and
* **edge-links** pay for every original edge that the decoded assignment fails
  *and* whose two half-edges both agree — for such an edge the edge-link carries
  exactly the failed original constraint.

An edge escapes the second bill only by having a disagreeing half-edge, and
those are already billed by the first. Trading the two off gives a bound of
`min 1 c` times the original unsatisfied fraction, with
`c = (1 - lam) · degree / card α`.

## Main definitions

- `ConstraintGraph.cloudDarts`, `edgeDarts` — the unsatisfied darts split by
  which kind of link they are
- `ConstraintGraph.goodEdges` — the failed original edges whose halves agree

## Main results

- `ConstraintGraph.card_unsatEdges_le_charge` — an edge failed by decoding is either
  billed to an edge-link or has a disagreeing half-edge
- `ConstraintGraph.card_unsatDarts_ge` — the combined charge
- `ConstraintGraph.unsatFrac_reduce_ge`, `ConstraintGraph.le_unsatVal_reduce` —
  soundness: the reduced system's unsatisfied fraction, and its value, are at
  least `reduceConst` times `G`'s value
-/

@[expose] public section

namespace Complexity

namespace ConstraintGraph

/-- The constant factor degree reduction costs: the trade-off between the cloud
charge `(1 - lam) · degree / card α` and the edge charge `1`, diluted by the
`(1 + degree)`-fold increase in darts. -/
noncomputable def reduceConst (E : ExpanderFamily) (α : Type) [Fintype α] : ℝ :=
  min 1 ((1 - E.lam) * (E.degree : ℝ) / (Fintype.card α : ℝ)) / (2 * (1 + (E.degree : ℝ)))

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
variable (G : ConstraintGraph α) (E : ExpanderFamily)

attribute [local instance] Classical.propDecidable

/-! ### Splitting the unsatisfied darts -/

/-- The unsatisfied cloud-links. -/
noncomputable def cloudDarts (A : (G.reduce E).Assignment) : Finset (G.reduce E).Dart :=
  ((G.reduce E).unsatDarts A).filter fun x => x.2 ≠ none

/-- The unsatisfied edge-links. -/
noncomputable def edgeDarts (A : (G.reduce E).Assignment) : Finset (G.reduce E).Dart :=
  ((G.reduce E).unsatDarts A).filter fun x => x.2 = none

omit [Fintype α] [Nonempty α] in
theorem card_cloudDarts_add_card_edgeDarts (A : (G.reduce E).Assignment) :
    (G.cloudDarts E A).card + (G.edgeDarts E A).card = ((G.reduce E).unsatDarts A).card := by
  rw [cloudDarts, edgeDarts, Nat.add_comm]
  exact Finset.card_filter_add_card_filter_not (s := (G.reduce E).unsatDarts A)
    (p := fun x : (G.reduce E).Dart => x.2 = none)

omit [Fintype α] [Nonempty α] in
theorem cloudUnsat_subset_cloudDarts (A : (G.reduce E).Assignment) (v : Fin G.numVerts) :
    G.cloudUnsat E A v ⊆ G.cloudDarts E A := by
  intro x hx
  rw [cloudUnsat, Finset.mem_filter] at hx
  rw [cloudDarts, Finset.mem_filter]
  exact ⟨hx.1, hx.2.2⟩

/-- The cloud charge lands entirely among the unsatisfied cloud-links. -/
theorem cloud_charge_le_card_cloudDarts (A : (G.reduce E).Assignment) :
    (1 - E.lam) * (E.degree : ℝ) * ((G.devSet A).card : ℝ) / (Fintype.card α : ℝ)
      ≤ ((G.cloudDarts E A).card : ℝ) := by
  have hsum : ∑ v : Fin G.numVerts,
      ((1 - E.lam) * (E.degree : ℝ) * ((G.devIdx A v).card : ℝ) / (Fintype.card α : ℝ))
      ≤ ∑ v : Fin G.numVerts, ((G.cloudUnsat E A v).card : ℝ) :=
    Finset.sum_le_sum fun v _ => G.cloud_disagreement_bound E A v
  have hleft : ∑ v : Fin G.numVerts,
      ((1 - E.lam) * (E.degree : ℝ) * ((G.devIdx A v).card : ℝ) / (Fintype.card α : ℝ))
      = (1 - E.lam) * (E.degree : ℝ) * ((G.devSet A).card : ℝ) / (Fintype.card α : ℝ) := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    congr 2
    rw [← Nat.cast_sum, G.sum_card_devIdx A]
  have hdisj : ∀ u ∈ (Finset.univ : Finset (Fin G.numVerts)),
      ∀ v ∈ (Finset.univ : Finset (Fin G.numVerts)), u ≠ v →
      Disjoint (G.cloudUnsat E A u) (G.cloudUnsat E A v) :=
    fun u _ v _ h => G.cloudUnsat_disjoint E A h
  have hnat : ∑ v : Fin G.numVerts, (G.cloudUnsat E A v).card ≤ (G.cloudDarts E A).card := by
    rw [← Finset.card_biUnion hdisj]
    refine Finset.card_le_card ?_
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨v, -, hxv⟩ := hx
    exact G.cloudUnsat_subset_cloudDarts E A v hxv
  have hright : ∑ v : Fin G.numVerts, ((G.cloudUnsat E A v).card : ℝ)
      ≤ ((G.cloudDarts E A).card : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hnat
  rw [← hleft]
  exact le_trans hsum hright

/-! ### The edge-link charge -/

/-- The original edges that decoding fails and whose two half-edges both agree
with their vertices' labels. -/
noncomputable def goodEdges (A : (G.reduce E).Assignment) : Finset (Fin G.numEdges) :=
  (G.unsatEdges (G.decode A)).filter fun e =>
    (e, false) ∉ G.devSet A ∧ (e, true) ∉ G.devSet A

/-- Each such edge contributes an unsatisfied edge-link: the link carries
exactly the original constraint, evaluated at the decoded labels. -/
theorem card_goodEdges_le (A : (G.reduce E).Assignment) :
    (G.goodEdges E A).card ≤ (G.edgeDarts E A).card := by
  refine Finset.card_le_card_of_injOn (fun e => ((e, false), none)) ?_ ?_
  · intro e he
    simp only [Finset.mem_coe] at he ⊢
    rw [goodEdges, Finset.mem_filter] at he
    obtain ⟨hfail, h0, h1⟩ := he
    have hA0 : A (e, false) = G.decode A (G.tail e) := by
      have h := (G.mem_devSet (A := A) (p := (e, false))).not.mp h0
      simp only [not_not] at h
      have howner : G.owner ((e, false) : G.HalfEdge) = G.tail e := by simp [owner]
      rw [h, howner]
    have hA1 : A (e, true) = G.decode A (G.head e) := by
      have h := (G.mem_devSet (A := A) (p := (e, true))).not.mp h1
      simp only [not_not] at h
      have howner : G.owner ((e, true) : G.HalfEdge) = G.head e := by simp [owner]
      rw [h, howner]
    rw [edgeDarts, Finset.mem_filter]
    refine ⟨?_, rfl⟩
    rw [RegCSP.mem_unsatDarts]
    show ¬ ((if ((e, false) : G.HalfEdge).2 then
        G.rel e (A ((G.reduce E).graph.nbr (e, false) none)) (A (e, false))
      else G.rel e (A (e, false)) (A ((G.reduce E).graph.nbr (e, false) none))) = true)
    have hnbr : (G.reduce E).graph.nbr ((e, false) : G.HalfEdge) none = (e, true) := by
      show G.flipHalf (e, false) = (e, true)
      simp [flipHalf]
    rw [hnbr]
    simp only [ite_eq_right (by simp : ¬ (((e, false) : G.HalfEdge).2 = true))]
    rw [hA0, hA1]
    rw [mem_unsatEdges] at hfail
    rw [Satisfies, satisfies] at hfail
    exact hfail
  · intro e _ f _ hef
    have := congrArg (fun x => x.1.1) hef
    simpa using this

/-- An edge that decoding fails is either billed to an edge-link or has a
disagreeing half-edge. -/
theorem card_unsatEdges_le_charge (A : (G.reduce E).Assignment) :
    (G.unsatEdges (G.decode A)).card ≤ (G.goodEdges E A).card + (G.devSet A).card := by
  have hsub : G.unsatEdges (G.decode A)
      ⊆ G.goodEdges E A ∪ (G.devSet A).image Prod.fst := by
    intro e he
    by_cases hgood : (e, false) ∉ G.devSet A ∧ (e, true) ∉ G.devSet A
    · exact Finset.mem_union_left _ (by rw [goodEdges, Finset.mem_filter]; exact ⟨he, hgood⟩)
    · refine Finset.mem_union_right _ ?_
      rw [Finset.mem_image]
      rw [not_and_or, not_not, not_not] at hgood
      rcases hgood with h | h
      · exact ⟨(e, false), h, rfl⟩
      · exact ⟨(e, true), h, rfl⟩
  calc (G.unsatEdges (G.decode A)).card
      ≤ (G.goodEdges E A ∪ (G.devSet A).image Prod.fst).card := Finset.card_le_card hsub
    _ ≤ (G.goodEdges E A).card + ((G.devSet A).image Prod.fst).card := Finset.card_union_le _ _
    _ ≤ (G.goodEdges E A).card + (G.devSet A).card := by
        exact Nat.add_le_add_left (Finset.card_image_le) _

/-! ### Soundness -/

/-- **The combined charge.** With `c = (1 - lam) · degree / card α`, the
unsatisfied darts number at least `min 1 c` times the edges that decoding
fails. -/
theorem card_unsatDarts_ge (A : (G.reduce E).Assignment) :
    min 1 ((1 - E.lam) * (E.degree : ℝ) / (Fintype.card α : ℝ))
        * ((G.unsatEdges (G.decode A)).card : ℝ)
      ≤ (((G.reduce E).unsatDarts A).card : ℝ) := by
  set c : ℝ := (1 - E.lam) * (E.degree : ℝ) / (Fintype.card α : ℝ) with hc
  set D : ℝ := ((G.devSet A).card : ℝ) with hD
  set U : ℝ := ((G.unsatEdges (G.decode A)).card : ℝ) with hU
  have hcloud : c * D ≤ ((G.cloudDarts E A).card : ℝ) := by
    have h := G.cloud_charge_le_card_cloudDarts E A
    rw [hc, hD]
    calc (1 - E.lam) * (E.degree : ℝ) / (Fintype.card α : ℝ) * ((G.devSet A).card : ℝ)
        = (1 - E.lam) * (E.degree : ℝ) * ((G.devSet A).card : ℝ) / (Fintype.card α : ℝ) := by
          ring
      _ ≤ ((G.cloudDarts E A).card : ℝ) := h
  have hedge : U ≤ ((G.edgeDarts E A).card : ℝ) + D := by
    have h1 := G.card_unsatEdges_le_charge E A
    have h2 := G.card_goodEdges_le E A
    have h1R : U ≤ ((G.goodEdges E A).card : ℝ) + D := by rw [hU, hD]; exact_mod_cast h1
    have h2R : ((G.goodEdges E A).card : ℝ) ≤ ((G.edgeDarts E A).card : ℝ) := by
      exact_mod_cast h2
    linarith
  have htotal : ((G.cloudDarts E A).card : ℝ) + ((G.edgeDarts E A).card : ℝ)
      = (((G.reduce E).unsatDarts A).card : ℝ) := by
    rw [← Nat.cast_add, G.card_cloudDarts_add_card_edgeDarts E A]
  have hDnn : 0 ≤ D := by rw [hD]; positivity
  have hcnn : 0 ≤ c := by
    rw [hc]
    have h1 : 0 ≤ 1 - E.lam := by linarith [E.lam_lt_one]
    positivity
  rcases le_total 1 c with hcge | hcle
  · have hmin : min 1 c = 1 := min_eq_left hcge
    rw [hmin, one_mul, ← htotal]
    nlinarith [hcloud, hedge]
  · have hmin : min 1 c = c := min_eq_right hcle
    rw [hmin, ← htotal]
    nlinarith [hcloud, hedge, hDnn, hcnn]

/-- **Soundness of degree reduction.** The reduced system's unsatisfied
fraction is at least a constant times the original's unsatisfiability value,
the constant depending only on the alphabet size and the cloud expander. -/
theorem unsatFrac_reduce_ge (A : (G.reduce E).Assignment) :
    min 1 ((1 - E.lam) * (E.degree : ℝ) / (Fintype.card α : ℝ)) / (2 * (1 + (E.degree : ℝ)))
        * ((G.unsatVal : ℚ) : ℝ)
      ≤ (((G.reduce E).unsatFrac A : ℚ) : ℝ) := by
  set c : ℝ := min 1 ((1 - E.lam) * (E.degree : ℝ) / (Fintype.card α : ℝ)) with hc
  have hcnn : 0 ≤ c := by
    rw [hc]
    refine le_min zero_le_one ?_
    have h1 : 0 ≤ 1 - E.lam := by linarith [E.lam_lt_one]
    positivity
  have hdart : ((G.reduce E).graph.order * (G.reduce E).graph.deg : ℕ)
      = 2 * G.numEdges * (1 + E.degree) := by
    show ((G.reduceGraph E).order * (G.reduceGraph E).deg : ℕ) = _
    rw [G.order_reduceGraph E, G.deg_reduceGraph E]
  rcases Nat.eq_zero_or_pos G.numEdges with hm | hm
  · have hsat : G.Satisfiable := by
      by_contra hcon
      have := G.numEdges_pos_of_not_satisfiable hcon
      omega
    have h0 : G.unsatVal = 0 := (G.unsatVal_eq_zero_iff_satisfiable).mpr hsat
    rw [h0]
    simp only [Rat.cast_zero, mul_zero]
    have : (0 : ℚ) ≤ (G.reduce E).unsatFrac A := (G.reduce E).unsatFrac_nonneg A
    exact_mod_cast this
  · have hmq : (0 : ℝ) < (G.numEdges : ℝ) := by exact_mod_cast hm
    have hfrac : (((G.reduce E).unsatFrac A : ℚ) : ℝ)
        = (((G.reduce E).unsatDarts A).card : ℝ)
          / (2 * (G.numEdges : ℝ) * (1 + (E.degree : ℝ))) := by
      rw [RegCSP.unsatFrac, hdart]
      push_cast
      ring
    have hU : ((G.unsatVal : ℚ) : ℝ) * (G.numEdges : ℝ)
        ≤ ((G.unsatEdges (G.decode A)).card : ℝ) := by
      have h := G.unsatVal_le (G.decode A)
      rw [unsatFrac] at h
      have hR : ((G.unsatVal : ℚ) : ℝ)
          ≤ ((G.unsatEdges (G.decode A)).card : ℝ) / (G.numEdges : ℝ) := by
        have hcast := (Rat.cast_le (K := ℝ)).mpr h
        push_cast at hcast
        exact hcast
      rwa [le_div_iff₀ hmq] at hR
    have hcharge := G.card_unsatDarts_ge E A
    have hkey : c * ((G.unsatVal : ℚ) : ℝ) * (G.numEdges : ℝ)
        ≤ (((G.reduce E).unsatDarts A).card : ℝ) := by
      calc c * ((G.unsatVal : ℚ) : ℝ) * (G.numEdges : ℝ)
          = c * (((G.unsatVal : ℚ) : ℝ) * (G.numEdges : ℝ)) := by ring
        _ ≤ c * ((G.unsatEdges (G.decode A)).card : ℝ) :=
            mul_le_mul_of_nonneg_left hU hcnn
        _ ≤ (((G.reduce E).unsatDarts A).card : ℝ) := hcharge
    have hden : (0 : ℝ) < 2 * (G.numEdges : ℝ) * (1 + (E.degree : ℝ)) := by positivity
    rw [hfrac, le_div_iff₀ hden]
    calc c / (2 * (1 + (E.degree : ℝ))) * ((G.unsatVal : ℚ) : ℝ)
          * (2 * (G.numEdges : ℝ) * (1 + (E.degree : ℝ)))
        = c * ((G.unsatVal : ℚ) : ℝ) * (G.numEdges : ℝ) := by
          field_simp
      _ ≤ (((G.reduce E).unsatDarts A).card : ℝ) := hkey

/-- **Soundness of degree reduction, on values.** -/
theorem le_unsatVal_reduce :
    reduceConst E α * ((G.unsatVal : ℚ) : ℝ) ≤ (((G.reduce E).unsatVal : ℚ) : ℝ) := by
  obtain ⟨A, hA⟩ := (G.reduce E).exists_assignment_unsatFrac_eq_unsatVal
  rw [reduceConst, ← hA]
  exact G.unsatFrac_reduce_ge E A

end ConstraintGraph

end Complexity
