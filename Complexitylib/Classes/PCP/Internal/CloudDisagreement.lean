/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.DegreeReduction
public import Complexitylib.Classes.PCP.Internal.EdgeExpansion
public import Complexitylib.Classes.PCP.Internal.FinsetPlurality
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Charging disagreement inside a cloud

The soundness half of Dinur's degree reduction, one cloud at a time.

An assignment of the reduced system labels half-edges, not vertices. It is
decoded back to a vertex assignment by **plurality**: `decode A v` is a label
that at least a `1 / card α` fraction of `v`'s cloud agrees with. The
half-edges of the cloud that *disagree* form a set the cloud's expander must
charge for: by edge expansion, the disagreeing set sends out many cloud-links,
and every one of them joins two half-edges with different labels, so every one
of them is an unsatisfied constraint.

Everything is phrased at the level of a cloud's *enumeration* `cloudList v`, so
that the expander family — which lives on `Fin n` — applies directly, with
`cloudRot_getElem` as the only bridge back to half-edges.

## Main definitions

- `ConstraintGraph.decode` — the plurality label of a cloud
- `ConstraintGraph.devIdx` — the indices of a cloud that disagree with it
- `ConstraintGraph.cloudUnsat` — the unsatisfied cloud-links sitting at a vertex

## Main results

- `ConstraintGraph.length_le_card_agree` — plurality: the agreeing part of a
  cloud is at least a `1 / card α` fraction of it
- `ConstraintGraph.card_dartsBetween_le_card_cloudUnsat` — every expander
  boundary dart of the disagreeing set is an unsatisfied cloud-link
- `ConstraintGraph.cloud_disagreement_bound` — the resulting charge:
  `(1 - lam) · degree · |dev| / card α` unsatisfied links at `v`
- `ConstraintGraph.total_cloud_charge` — summed over the vertices, since the
  clouds' bills never overlap
-/

@[expose] public section

namespace Complexity

namespace ConstraintGraph

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
variable (G : ConstraintGraph α) (E : ExpanderFamily)

attribute [local instance] Classical.propDecidable

/-! ### Plurality decoding -/

/-- The plurality label of `v`'s cloud: a label at least a `1 / card α`
fraction of the cloud agrees with. -/
noncomputable def decode (A : G.HalfEdge → α) (v : Fin G.numVerts) : α :=
  Classical.choose (exists_plurality (Finset.univ : Finset (Fin (G.cloudList v).length))
    fun i => A (G.cloudList v)[i.val])

/-- The indices of `v`'s cloud whose labels disagree with the plurality. -/
noncomputable def devIdx (A : G.HalfEdge → α) (v : Fin G.numVerts) :
    Finset (Fin (G.cloudList v).length) :=
  Finset.univ.filter fun i => A (G.cloudList v)[i.val] ≠ G.decode A v

theorem mem_devIdx {A : G.HalfEdge → α} {v : Fin G.numVerts}
    {i : Fin (G.cloudList v).length} :
    i ∈ G.devIdx A v ↔ A (G.cloudList v)[i.val] ≠ G.decode A v := by
  simp [devIdx]

theorem mem_compl_devIdx {A : G.HalfEdge → α} {v : Fin G.numVerts}
    {i : Fin (G.cloudList v).length} :
    i ∈ (G.devIdx A v)ᶜ ↔ A (G.cloudList v)[i.val] = G.decode A v := by
  simp [devIdx]

/-- **Plurality.** The part of a cloud agreeing with its decoded label is at
least a `1 / card α` fraction of the cloud. -/
theorem length_le_card_agree (A : G.HalfEdge → α) (v : Fin G.numVerts) :
    (G.cloudList v).length ≤ Fintype.card α * ((G.devIdx A v)ᶜ).card := by
  have h := Classical.choose_spec
    (exists_plurality (Finset.univ : Finset (Fin (G.cloudList v).length))
      fun i => A (G.cloudList v)[i.val])
  simpa [devIdx, decode, Finset.compl_filter, not_not] using h

/-! ### From cloud indices to half-edges -/

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- A cloud's filtered subset is the image of the corresponding index set. -/
theorem cloud_filter_eq_image (v : Fin G.numVerts) (P : G.HalfEdge → Prop) [DecidablePred P] :
    (G.cloud v).filter P
      = (Finset.univ.filter fun i : Fin (G.cloudList v).length =>
          P (G.cloudList v)[i.val]).image fun i => (G.cloudList v)[i.val] := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hP⟩
    have hmem : p ∈ G.cloudList v := (G.mem_cloudList).mpr hp
    have hlt : (G.cloudList v).idxOf p < (G.cloudList v).length :=
      List.idxOf_lt_length_iff.mpr hmem
    have hget : (G.cloudList v)[(G.cloudList v).idxOf p] = p := List.getElem_idxOf hlt
    exact ⟨⟨(G.cloudList v).idxOf p, hlt⟩, by rw [hget]; exact hP, hget⟩
  · rintro ⟨i, hP, rfl⟩
    exact ⟨(G.mem_cloudList).mp (List.getElem_mem i.isLt), hP⟩

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- Counting inside a cloud is the same through its enumeration. -/
theorem card_filter_cloud (v : Fin G.numVerts) (P : G.HalfEdge → Prop) [DecidablePred P] :
    (Finset.univ.filter fun i : Fin (G.cloudList v).length =>
        P (G.cloudList v)[i.val]).card = ((G.cloud v).filter P).card := by
  rw [G.cloud_filter_eq_image v P, Finset.card_image_of_injOn]
  intro i _ j _ h
  exact Fin.ext ((G.nodup_cloudList v).getElem_inj_iff.mp h)

/-- The half-edges whose label disagrees with their vertex's decoded label. -/
noncomputable def devSet (A : G.HalfEdge → α) : Finset G.HalfEdge :=
  Finset.univ.filter fun p => A p ≠ G.decode A (G.owner p)

theorem mem_devSet {A : G.HalfEdge → α} {p : G.HalfEdge} :
    p ∈ G.devSet A ↔ A p ≠ G.decode A (G.owner p) := by
  simp [devSet]

/-- A cloud's disagreeing indices count the same as its disagreeing
half-edges. -/
theorem card_devIdx_eq (A : G.HalfEdge → α) (v : Fin G.numVerts) :
    (G.devIdx A v).card = ((G.devSet A).filter fun p => G.owner p = v).card := by
  have hset : (G.cloud v).filter (fun p => A p ≠ G.decode A v)
      = (G.devSet A).filter fun p => G.owner p = v := by
    ext p
    simp only [Finset.mem_filter, mem_cloud, mem_devSet]
    constructor
    · rintro ⟨hv, hne⟩
      exact ⟨by rw [hv]; exact hne, hv⟩
    · rintro ⟨hne, hv⟩
      exact ⟨hv, by rw [← hv]; exact hne⟩
  rw [devIdx, G.card_filter_cloud v fun p => A p ≠ G.decode A v, hset]

/-- Summed over the vertices, the cloud charges account for every disagreeing
half-edge exactly once. -/
theorem sum_card_devIdx (A : G.HalfEdge → α) :
    ∑ v : Fin G.numVerts, (G.devIdx A v).card = (G.devSet A).card := by
  have h : (G.devSet A).card
      = ∑ v : Fin G.numVerts, ((G.devSet A).filter fun p => G.owner p = v).card :=
    Finset.card_eq_sum_card_fiberwise fun p _ => Finset.mem_univ (G.owner p)
  rw [h]
  exact Finset.sum_congr rfl fun v _ => G.card_devIdx_eq A v

/-! ### Unsatisfied cloud-links -/

/-- The unsatisfied cloud-links of the reduced system sitting at `v`. -/
noncomputable def cloudUnsat (A : (G.reduce E).Assignment) (v : Fin G.numVerts) :
    Finset (G.reduce E).Dart :=
  ((G.reduce E).unsatDarts A).filter fun x => G.owner x.1 = v ∧ x.2 ≠ none

omit [Fintype α] [Nonempty α] in
theorem cloudUnsat_subset (A : (G.reduce E).Assignment) (v : Fin G.numVerts) :
    G.cloudUnsat E A v ⊆ (G.reduce E).unsatDarts A :=
  Finset.filter_subset _ _

omit [Fintype α] [Nonempty α] in
/-- The clouds' unsatisfied links are disjoint: a dart's tail determines the
vertex it sits at. -/
theorem cloudUnsat_disjoint (A : (G.reduce E).Assignment) {u v : Fin G.numVerts} (huv : u ≠ v) :
    Disjoint (G.cloudUnsat E A u) (G.cloudUnsat E A v) := by
  refine Finset.disjoint_left.mpr fun x hx hx' => ?_
  rw [cloudUnsat, Finset.mem_filter] at hx hx'
  exact huv (hx.2.1.symm.trans hx'.2.1)

/-- Every boundary dart of the disagreeing set is an unsatisfied cloud-link:
its two ends carry different labels, one being the plurality and one not. -/
theorem card_dartsBetween_le_card_cloudUnsat (A : (G.reduce E).Assignment)
    (v : Fin G.numVerts) :
    ((E.graph (G.cloudList v).length).dartsBetween (G.devIdx A v) (G.devIdx A v)ᶜ).card
      ≤ (G.cloudUnsat E A v).card := by
  refine Finset.card_le_card_of_injOn
    (fun x => ((G.cloudList v)[x.1.val], some x.2)) ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe] at hx ⊢
    simp only [RegGraph.dartsBetween, Finset.mem_filter] at hx
    obtain ⟨-, hx1, hx2⟩ := hx
    have hnbr : (E.graph (G.cloudList v).length).nbr x.1 x.2
        = (E.rot (G.cloudList v).length (x.1, x.2)).1 := rfl
    rw [hnbr] at hx2
    have hdev : A (G.cloudList v)[x.1.val] ≠ G.decode A v := (G.mem_devIdx).mp hx1
    have hagree : A (G.cloudList v)[(E.rot (G.cloudList v).length (x.1, x.2)).1.val]
        = G.decode A v := (G.mem_compl_devIdx).mp hx2
    have howner : G.owner (G.cloudList v)[x.1.val] = v :=
      (G.mem_cloud).mp ((G.mem_cloudList).mp (List.getElem_mem x.1.isLt))
    rw [cloudUnsat, Finset.mem_filter]
    refine ⟨?_, howner, by exact Option.some_ne_none _⟩
    rw [RegCSP.mem_unsatDarts]
    show ¬ ((A (G.cloudList v)[x.1.val]
      == A ((G.reduce E).graph.nbr (G.cloudList v)[x.1.val] (some x.2))) = true)
    have hstep : (G.reduce E).graph.nbr (G.cloudList v)[x.1.val] (some x.2)
        = (G.cloudList v)[(E.rot (G.cloudList v).length (x.1, x.2)).1.val] := by
      show (G.cloudRot E (G.cloudList v)[x.1.val] x.2).1 = _
      rw [G.cloudRot_getElem E v x.1 x.2]
    rw [hstep, hagree]
    simpa using hdev
  · intro x _ y _ hxy
    have h1 : (G.cloudList v)[x.1.val] = (G.cloudList v)[y.1.val] := congrArg Prod.fst hxy
    have h2 : x.2 = y.2 := by
      have h := congrArg Prod.snd hxy
      exact Option.some.inj h
    have h3 : x.1 = y.1 :=
      Fin.ext ((G.nodup_cloudList v).getElem_inj_iff.mp h1)
    exact Prod.ext h3 h2

/-! ### The charge -/

/-- **The cloud charge.** The disagreeing part of `v`'s cloud is billed
`(1 - lam) · degree / card α` unsatisfied cloud-links per disagreeing
half-edge. -/
theorem cloud_disagreement_bound (A : (G.reduce E).Assignment) (v : Fin G.numVerts) :
    (1 - E.lam) * (E.degree : ℝ) * ((G.devIdx A v).card : ℝ) / (Fintype.card α : ℝ)
      ≤ ((G.cloudUnsat E A v).card : ℝ) := by
  rcases Nat.eq_zero_or_pos (G.cloudList v).length with hlen | hlen
  · have hempty : G.devIdx A v = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro i
      exact absurd i.isLt (by omega)
    rw [hempty]
    simp
  · have hordpos : 0 < (E.graph (G.cloudList v).length).order := by
      rw [E.order_graph]; exact hlen
    have hexp := (E.graph (G.cloudList v).length).card_dartsBetween_compl_ge
      E.lam_nonneg (E.spectral_graph _) hordpos (G.devIdx A v)
    rw [E.deg_graph, E.order_graph] at hexp
    have hinj := G.card_dartsBetween_le_card_cloudUnsat E A v
    have hinjR : (((E.graph (G.cloudList v).length).dartsBetween (G.devIdx A v)
        (G.devIdx A v)ᶜ).card : ℝ) ≤ ((G.cloudUnsat E A v).card : ℝ) := by
      exact_mod_cast hinj
    refine le_trans ?_ (le_trans hexp hinjR)
    -- plurality: `|devᶜ| ≥ length / card α`
    have hplur : ((G.cloudList v).length : ℝ)
        ≤ (Fintype.card α : ℝ) * (((G.devIdx A v)ᶜ).card : ℝ) := by
      exact_mod_cast G.length_le_card_agree A v
    have hlam : 0 ≤ 1 - E.lam := by linarith [E.lam_lt_one]
    have hdev : (0 : ℝ) ≤ ((G.devIdx A v).card : ℝ) := by positivity
    have hkey : ((G.devIdx A v).card : ℝ) / (Fintype.card α : ℝ)
        ≤ ((G.devIdx A v).card : ℝ) * (((G.devIdx A v)ᶜ).card : ℝ)
            / ((G.cloudList v).length : ℝ) := by
      have hnum : ((G.devIdx A v).card : ℝ) * ((G.cloudList v).length : ℝ)
          ≤ (((G.devIdx A v).card : ℝ) * (((G.devIdx A v)ᶜ).card : ℝ))
            * (Fintype.card α : ℝ) := by
        nlinarith [hplur, hdev]
      calc ((G.devIdx A v).card : ℝ) / (Fintype.card α : ℝ)
          = (((G.devIdx A v).card : ℝ) * ((G.cloudList v).length : ℝ))
              / ((Fintype.card α : ℝ) * ((G.cloudList v).length : ℝ)) := by
            field_simp
        _ ≤ ((((G.devIdx A v).card : ℝ) * (((G.devIdx A v)ᶜ).card : ℝ))
              * (Fintype.card α : ℝ))
              / ((Fintype.card α : ℝ) * ((G.cloudList v).length : ℝ)) := by
            gcongr
        _ = ((G.devIdx A v).card : ℝ) * (((G.devIdx A v)ᶜ).card : ℝ)
              / ((G.cloudList v).length : ℝ) := by
            field_simp
    calc (1 - E.lam) * (E.degree : ℝ) * ((G.devIdx A v).card : ℝ) / (Fintype.card α : ℝ)
        = (1 - E.lam) * (E.degree : ℝ)
            * (((G.devIdx A v).card : ℝ) / (Fintype.card α : ℝ)) := by ring
      _ ≤ (1 - E.lam) * (E.degree : ℝ)
            * (((G.devIdx A v).card : ℝ) * (((G.devIdx A v)ᶜ).card : ℝ)
              / ((G.cloudList v).length : ℝ)) := by
          have : (0 : ℝ) ≤ (1 - E.lam) * (E.degree : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left hkey this

/-! ### The total charge -/

omit [Fintype α] [Nonempty α] in
/-- The clouds' unsatisfied links are disjoint subsets of all the unsatisfied
darts, so their counts add up to at most the whole. -/
theorem sum_card_cloudUnsat_le (A : (G.reduce E).Assignment) :
    ∑ v : Fin G.numVerts, (G.cloudUnsat E A v).card ≤ (((G.reduce E).unsatDarts A)).card := by
  have hdisj : ∀ u ∈ (Finset.univ : Finset (Fin G.numVerts)),
      ∀ v ∈ (Finset.univ : Finset (Fin G.numVerts)), u ≠ v →
      Disjoint (G.cloudUnsat E A u) (G.cloudUnsat E A v) :=
    fun u _ v _ h => G.cloudUnsat_disjoint E A h
  rw [← Finset.card_biUnion hdisj]
  refine Finset.card_le_card ?_
  intro x hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨v, -, hxv⟩ := hx
  exact G.cloudUnsat_subset E A v hxv

/-- **The total cloud charge.** Every disagreeing half-edge is billed
`(1 - lam) · degree / card α` unsatisfied cloud-links, and the bills for
different vertices never overlap. -/
theorem total_cloud_charge (A : (G.reduce E).Assignment) :
    (1 - E.lam) * (E.degree : ℝ) * ((G.devSet A).card : ℝ) / (Fintype.card α : ℝ)
      ≤ (((G.reduce E).unsatDarts A).card : ℝ) := by
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
  have hright : ∑ v : Fin G.numVerts, ((G.cloudUnsat E A v).card : ℝ)
      ≤ (((G.reduce E).unsatDarts A).card : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast G.sum_card_cloudUnsat_le E A
  rw [← hleft]
  exact le_trans hsum hright

end ConstraintGraph

end Complexity
