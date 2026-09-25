/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.EquivFin

/-!
# Ordering a cubic graph by median edge positions

Given a path decomposition of a simple 3-regular graph, place every edge at a
position inside a bag containing its endpoints, so that positions are
distinct and increase with the bag index. Each vertex has three incident
positions; order the vertices by the middle one. Then every prefix cut has at
most one more edge than the bag in which the last vertex's median edge lies:
a crossing edge below the median of the last vertex is the unique low edge of
its later endpoint, one above it is the unique high edge of its earlier
endpoint, and the median itself is a single edge. Each charged vertex lies in
that bag by consecutiveness.

The main result is `card_cutFinset_key_lt_le`: with bags of size at most
`p + 1`, an injective key orders the vertices so that every prefix cut has at
most `p + 2` edges.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical

namespace MedianOrdering

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
  (D : PathDecomposition H)

/-! ### Bags indexed by natural numbers -/

/-- The bag with index `i`, or the empty set beyond the decomposition. -/
noncomputable def bagN (i : Nat) : Finset W :=
  if h : i < D.length then D.bag ⟨i, h⟩ else ∅

omit [Fintype W] [DecidableEq W] [DecidableRel H.Adj] in
theorem card_bagN_le {p : Nat} (hbag : ∀ i, (D.bag i).card ≤ p + 1) (i : Nat) :
    (bagN H D i).card ≤ p + 1 := by
  unfold bagN
  split_ifs
  · exact hbag _
  · simp

omit [Fintype W] [DecidableEq W] [DecidableRel H.Adj] in
theorem bagN_consecutive {w : W} {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : w ∈ bagN H D i) (hk : w ∈ bagN H D k) : w ∈ bagN H D j := by
  have hk' : k < D.length := by
    by_contra h
    simp [bagN, h] at hk
  have hi' : i < D.length := by omega
  have hj' : j < D.length := by omega
  simp only [bagN, hi', hj', hk', ↓reduceDIte] at hi hk ⊢
  exact D.consecutive w ⟨i, hi'⟩ ⟨j, hj'⟩ ⟨k, hk'⟩ hij hjk hi hk

/-- A bag containing both endpoints of an edge; `0` for non-edges. -/
noncomputable def bagOf (e : Sym2 W) : Nat :=
  if h : ∃ i : Fin D.length, ∀ a ∈ e, a ∈ D.bag i then (Classical.choose h).val else 0

omit [DecidableRel H.Adj] in
theorem mem_bagN_bagOf {e : Sym2 W} (he : e ∈ H.edgeSet) {a : W} (ha : a ∈ e) :
    a ∈ bagN H D (bagOf H D e) := by
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨i, hu, hv⟩ := D.edge_mem u v he
    have h : ∃ i : Fin D.length, ∀ a ∈ s(u, v), a ∈ D.bag i :=
      ⟨i, fun a ha => by rcases Sym2.mem_iff.mp ha with rfl | rfl <;> assumption⟩
    have spec := Classical.choose_spec h a ha
    simp only [bagOf, h, ↓reduceDIte, bagN, (Classical.choose h).isLt, Fin.eta]
    exact spec

/-! ### Edge positions -/

/-- An injective rank of the edges. -/
noncomputable def rank (e : Sym2 W) : Nat :=
  (Fintype.equivFin (Sym2 W) e).val

omit [DecidableEq W] in
theorem rank_lt (e : Sym2 W) : rank e < Fintype.card (Sym2 W) :=
  (Fintype.equivFin (Sym2 W) e).isLt

omit [DecidableEq W] in
theorem rank_injective : Function.Injective (rank : Sym2 W → Nat) :=
  fun _ _ h => (Fintype.equivFin (Sym2 W)).injective (Fin.ext h)

/-- The position of an edge: its bag index, refined by its rank. -/
noncomputable def pos (e : Sym2 W) : Nat :=
  bagOf H D e * Fintype.card (Sym2 W) + rank e

/-- Mixed-radix comparison: the leading digit is monotone. -/
theorem digit_le_of_le {b b' r r' c : Nat} (hr' : r' < c)
    (h : b * c + r ≤ b' * c + r') : b ≤ b' := by
  by_contra hlt
  rw [not_le] at hlt
  have : (b' + 1) * c ≤ b * c := Nat.mul_le_mul_right _ hlt
  rw [Nat.add_mul, one_mul] at this
  omega

omit [DecidableRel H.Adj] in
theorem pos_injective : Function.Injective (pos H D) := by
  intro e e' h
  have h₁ := digit_le_of_le (rank_lt e') h.le
  have h₂ := digit_le_of_le (rank_lt e) h.ge
  have hb : bagOf H D e = bagOf H D e' := le_antisymm h₁ h₂
  apply rank_injective
  unfold pos at h
  rw [hb] at h
  omega

omit [DecidableRel H.Adj] in
theorem bagOf_le_of_pos_le {e e' : Sym2 W} (h : pos H D e ≤ pos H D e') :
    bagOf H D e ≤ bagOf H D e' :=
  digit_le_of_le (rank_lt e') h

/-! ### Incident edges and medians -/

omit [DecidableEq W] in
theorem mem_incidenceFinset_iff {u : W} {e : Sym2 W} :
    e ∈ H.incidenceFinset u ↔ e ∈ H.edgeSet ∧ u ∈ e := by
  rw [SimpleGraph.mem_incidenceFinset]
  rfl

variable (regular : H.IsRegularOfDegree 3)

omit [DecidableEq W] in
include regular in
theorem card_incidenceFinset (u : W) : (H.incidenceFinset u).card = 3 := by
  rw [SimpleGraph.card_incidenceFinset_eq_degree, regular.degree_eq]

include regular in
/-- Among the three incident edges of a vertex there is a middle one. -/
theorem exists_median (u : W) :
    ∃ e ∈ H.incidenceFinset u,
      (∃ e₁ ∈ H.incidenceFinset u, pos H D e₁ < pos H D e) ∧
        ∃ e₂ ∈ H.incidenceFinset u, pos H D e < pos H D e₂ := by
  set I := H.incidenceFinset u
  set P := I.image (pos H D) with hP
  have cardP : P.card = 3 := by
    rw [hP, Finset.card_image_of_injective _ (pos_injective H D), card_incidenceFinset H regular u]
  have hne : P.Nonempty := Finset.card_pos.mp (by omega)
  set a := P.min' hne
  set c := P.max' hne
  have hac : a < c := Finset.min'_lt_max'_of_card P (by omega)
  have hcmem : c ∈ P.erase a := Finset.mem_erase.mpr ⟨hac.ne', Finset.max'_mem P hne⟩
  have hcard : ((P.erase a).erase c).card = 1 := by
    rw [Finset.card_erase_of_mem hcmem, Finset.card_erase_of_mem (Finset.min'_mem P hne), cardP]
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < ((P.erase a).erase c).card)
  obtain ⟨hbc, hb'⟩ := Finset.mem_erase.mp hb
  obtain ⟨hba, hbP⟩ := Finset.mem_erase.mp hb'
  have hab : a < b := lt_of_le_of_ne (Finset.min'_le P b hbP) hba.symm
  have hbc' : b < c := lt_of_le_of_ne (Finset.le_max' P b hbP) hbc
  obtain ⟨e, heI, rfl⟩ := Finset.mem_image.mp hbP
  obtain ⟨e₁, he₁, he₁'⟩ := Finset.mem_image.mp (Finset.min'_mem P hne)
  obtain ⟨e₂, he₂, he₂'⟩ := Finset.mem_image.mp (Finset.max'_mem P hne)
  exact ⟨e, heI, ⟨e₁, he₁, he₁' ▸ hab⟩, ⟨e₂, he₂, he₂' ▸ hbc'⟩⟩

/-- The median edge of a vertex. -/
noncomputable def median (u : W) : Sym2 W :=
  Classical.choose (exists_median H D regular u)

theorem median_mem (u : W) : median H D regular u ∈ H.incidenceFinset u :=
  (Classical.choose_spec (exists_median H D regular u)).1

theorem exists_lt_median (u : W) :
    ∃ e₁ ∈ H.incidenceFinset u, pos H D e₁ < pos H D (median H D regular u) :=
  (Classical.choose_spec (exists_median H D regular u)).2.1

theorem exists_median_lt (u : W) :
    ∃ e₂ ∈ H.incidenceFinset u, pos H D (median H D regular u) < pos H D e₂ :=
  (Classical.choose_spec (exists_median H D regular u)).2.2

/-- The position of the median edge. -/
noncomputable def theta (u : W) : Nat :=
  pos H D (median H D regular u)

/-- The incident edges split into those below, at, and above the median. -/
theorem incidenceFinset_eq (u : W) :
    H.incidenceFinset u =
      (H.incidenceFinset u).filter (fun e => pos H D e < theta H D regular u) ∪
        (H.incidenceFinset u).filter (fun e => theta H D regular u < pos H D e) ∪
          {median H D regular u} := by
  ext e
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · intro he
    rcases lt_trichotomy (pos H D e) (theta H D regular u) with h | h | h
    · exact Or.inl (Or.inl ⟨he, h⟩)
    · exact Or.inr (pos_injective H D h)
    · exact Or.inl (Or.inr ⟨he, h⟩)
  · rintro ((⟨he, _⟩ | ⟨he, _⟩) | rfl)
    · exact he
    · exact he
    · exact median_mem H D regular u

theorem card_below_add_card_above (u : W) :
    ((H.incidenceFinset u).filter fun e => pos H D e < theta H D regular u).card +
      ((H.incidenceFinset u).filter fun e => theta H D regular u < pos H D e).card + 1 = 3 := by
  have h := card_incidenceFinset H regular u
  rw [incidenceFinset_eq H D regular u] at h
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_singleton] at h
  · exact h
  · rw [Finset.disjoint_left]
    intro e he
    rw [Finset.mem_filter] at he
    intro he'
    rw [Finset.mem_filter] at he'
    omega
  · rw [Finset.disjoint_left]
    intro e he
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at he
    rw [Finset.mem_singleton]
    rintro rfl
    unfold theta at he
    omega

/-- At most one incident edge lies below the median. -/
theorem eq_of_lt_theta {u : W} {e e' : Sym2 W} (he : e ∈ H.incidenceFinset u)
    (he' : e' ∈ H.incidenceFinset u) (h : pos H D e < theta H D regular u)
    (h' : pos H D e' < theta H D regular u) : e = e' := by
  have total := card_below_add_card_above H D regular u
  obtain ⟨e₂, he₂, he₂'⟩ := exists_median_lt H D regular u
  have above_pos : 0 < ((H.incidenceFinset u).filter fun e => theta H D regular u < pos H D e).card :=
    Finset.card_pos.mpr ⟨e₂, Finset.mem_filter.mpr ⟨he₂, he₂'⟩⟩
  have below_le : ((H.incidenceFinset u).filter fun e => pos H D e < theta H D regular u).card ≤ 1 := by
    omega
  exact Finset.card_le_one.mp below_le e (Finset.mem_filter.mpr ⟨he, h⟩) e'
    (Finset.mem_filter.mpr ⟨he', h'⟩)

/-- At most one incident edge lies above the median. -/
theorem eq_of_theta_lt {u : W} {e e' : Sym2 W} (he : e ∈ H.incidenceFinset u)
    (he' : e' ∈ H.incidenceFinset u) (h : theta H D regular u < pos H D e)
    (h' : theta H D regular u < pos H D e') : e = e' := by
  have total := card_below_add_card_above H D regular u
  obtain ⟨e₁, he₁, he₁'⟩ := exists_lt_median H D regular u
  have below_pos : 0 < ((H.incidenceFinset u).filter fun e => pos H D e < theta H D regular u).card :=
    Finset.card_pos.mpr ⟨e₁, Finset.mem_filter.mpr ⟨he₁, he₁'⟩⟩
  have above_le : ((H.incidenceFinset u).filter fun e => theta H D regular u < pos H D e).card ≤ 1 := by
    omega
  exact Finset.card_le_one.mp above_le e (Finset.mem_filter.mpr ⟨he, h⟩) e'
    (Finset.mem_filter.mpr ⟨he', h'⟩)

/-! ### The vertex ordering -/

/-- The ordering key of a vertex: its median position, refined by a rank. -/
noncomputable def key (w : W) : Nat :=
  theta H D regular w * Fintype.card W + (Fintype.equivFin W w).val

theorem key_injective : Function.Injective (key H D regular) := by
  intro w w' h
  have h₁ := digit_le_of_le (Fintype.equivFin W w').isLt h.le
  have h₂ := digit_le_of_le (Fintype.equivFin W w).isLt h.ge
  have hθ : theta H D regular w = theta H D regular w' := le_antisymm h₁ h₂
  apply (Fintype.equivFin W).injective
  apply Fin.ext
  unfold key at h
  rw [hθ] at h
  omega

theorem theta_le_of_key_le {w w' : W} (h : key H D regular w ≤ key H D regular w') :
    theta H D regular w ≤ theta H D regular w' :=
  digit_le_of_le (Fintype.equivFin W w').isLt h

/-- **The median ordering bound.** Every prefix of the key ordering has a cut of
at most `p + 2` edges when all bags have at most `p + 1` vertices. -/
theorem card_cutFinset_key_lt_le {p : Nat} (hbag : ∀ i, (D.bag i).card ≤ p + 1) (t : Nat) :
    (H.cutFinset (Finset.univ.filter fun w => key H D regular w < t)).card ≤ p + 2 := by
  set L := Finset.univ.filter fun w => key H D regular w < t with hL
  rcases L.eq_empty_or_nonempty with hempty | hne
  · have : H.cutFinset L = ∅ := by
      ext e
      simp only [Finset.notMem_empty, iff_false]
      intro he
      obtain ⟨_, a, _, _, ha, _⟩ := (H.mem_cutFinset).mp he
      rw [hempty] at ha
      exact Finset.notMem_empty a ha
    rw [this, Finset.card_empty]
    exact Nat.zero_le _
  obtain ⟨v, hvL, hvmax⟩ := Finset.exists_max_image L (key H D regular) hne
  set θ₀ := theta H D regular v with hθ₀
  set j₀ := bagOf H D (median H D regular v) with hj₀
  have inL_theta : ∀ a ∈ L, theta H D regular a ≤ θ₀ :=
    fun a ha => theta_le_of_key_le H D regular (hvmax a ha)
  have outL_theta : ∀ b, b ∉ L → θ₀ ≤ theta H D regular b := by
    intro b hb
    apply theta_le_of_key_le
    have h₁ : key H D regular v < t := (Finset.mem_filter.mp hvL).2
    have h₂ : ¬ key H D regular b < t := fun h => hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  -- The endpoints of a crossing edge inside and outside `L`.
  choose inEnd outEnd hends using
    fun (e : Sym2 W) (he : e ∈ H.cutFinset L) => ((H.mem_cutFinset).mp he).2
  have edge_of_mem : ∀ e ∈ H.cutFinset L, e ∈ H.edgeSet :=
    fun e he => ((H.mem_cutFinset).mp he).1
  have inEnd_incident : ∀ e (he : e ∈ H.cutFinset L), e ∈ H.incidenceFinset (inEnd e he) := by
    intro e he
    rw [mem_incidenceFinset_iff]
    refine ⟨edge_of_mem e he, ?_⟩
    have key : ∀ e' : Sym2 W, e' = s(inEnd e he, outEnd e he) → inEnd e he ∈ e' :=
      fun e' h => h ▸ Sym2.mem_mk_left _ _
    exact key e (hends e he).1
  have outEnd_incident : ∀ e (he : e ∈ H.cutFinset L), e ∈ H.incidenceFinset (outEnd e he) := by
    intro e he
    rw [mem_incidenceFinset_iff]
    refine ⟨edge_of_mem e he, ?_⟩
    have key : ∀ e' : Sym2 W, e' = s(inEnd e he, outEnd e he) → outEnd e he ∈ e' :=
      fun e' h => h ▸ Sym2.mem_mk_right _ _
    exact key e (hends e he).1
  -- A vertex lies in bag `j₀` when an incident edge and its median straddle `j₀`.
  have mem_bag_of_straddle : ∀ (u : W) (e : Sym2 W), e ∈ H.incidenceFinset u →
      (bagOf H D e ≤ j₀ ∧ j₀ ≤ bagOf H D (median H D regular u) ∨
        bagOf H D (median H D regular u) ≤ j₀ ∧ j₀ ≤ bagOf H D e) → u ∈ bagN H D j₀ := by
    intro u e he hstraddle
    have hu₁ : u ∈ bagN H D (bagOf H D e) :=
      mem_bagN_bagOf H D ((mem_incidenceFinset_iff H).mp he).1 ((mem_incidenceFinset_iff H).mp he).2
    have hu₂ : u ∈ bagN H D (bagOf H D (median H D regular u)) :=
      mem_bagN_bagOf H D ((mem_incidenceFinset_iff H).mp (median_mem H D regular u)).1
        ((mem_incidenceFinset_iff H).mp (median_mem H D regular u)).2
    rcases hstraddle with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact bagN_consecutive H D h₁ h₂ hu₁ hu₂
    · exact bagN_consecutive H D h₁ h₂ hu₂ hu₁
  -- The charging map.
  let φ : Sym2 W → Option W := fun e =>
    if he : e ∈ H.cutFinset L then
      (if pos H D e < θ₀ then some (outEnd e he)
        else if θ₀ < pos H D e then some (inEnd e he) else none)
    else none
  have maps : Set.MapsTo φ ↑(H.cutFinset L) ↑(insert none ((bagN H D j₀).image some)) := by
    intro e he
    rw [Finset.mem_coe] at he
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_image]
    simp only [φ, he, ↓reduceDIte]
    by_cases hlow : pos H D e < θ₀
    · simp only [hlow, ↓reduceIte]
      right
      refine ⟨outEnd e he, ?_, rfl⟩
      apply mem_bag_of_straddle _ e (outEnd_incident e he)
      left
      exact ⟨bagOf_le_of_pos_le H D hlow.le,
        bagOf_le_of_pos_le H D (outL_theta _ (hends e he).2.2)⟩
    · simp only [hlow, ↓reduceIte]
      by_cases hhigh : θ₀ < pos H D e
      · simp only [hhigh, ↓reduceIte]
        right
        refine ⟨inEnd e he, ?_, rfl⟩
        apply mem_bag_of_straddle _ e (inEnd_incident e he)
        right
        exact ⟨bagOf_le_of_pos_le H D (inL_theta _ (hends e he).2.1),
          bagOf_le_of_pos_le H D hhigh.le⟩
      · simp [hhigh]
  have inj : Set.InjOn φ ↑(H.cutFinset L) := by
    intro e he e' he' heq
    rw [Finset.mem_coe] at he he'
    simp only [φ, he, he', ↓reduceDIte] at heq
    by_cases hlow : pos H D e < θ₀ <;> by_cases hlow' : pos H D e' < θ₀ <;>
      simp only [hlow, hlow', ↓reduceIte] at heq
    · -- Both below: the unique low edge of the common outer endpoint.
      have hb : outEnd e he = outEnd e' he' := Option.some.inj heq
      have h₁ := outEnd_incident e he
      have h₂ := outEnd_incident e' he'
      rw [hb] at h₁
      have hθ := outL_theta _ (hends e' he').2.2
      exact eq_of_lt_theta H D regular h₁ h₂ (hlow.trans_le hθ) (hlow'.trans_le hθ)
    · by_cases hhigh' : θ₀ < pos H D e'
      · simp only [hhigh', ↓reduceIte] at heq
        have hb : outEnd e he = inEnd e' he' := Option.some.inj heq
        exact absurd (hb ▸ (hends e' he').2.1) (hends e he).2.2
      · simp [hhigh'] at heq
    · by_cases hhigh : θ₀ < pos H D e
      · simp only [hhigh, ↓reduceIte] at heq
        have hb : inEnd e he = outEnd e' he' := Option.some.inj heq
        exact absurd (hb ▸ (hends e he).2.1) (hends e' he').2.2
      · simp [hhigh] at heq
    · by_cases hhigh : θ₀ < pos H D e <;> by_cases hhigh' : θ₀ < pos H D e' <;>
        simp only [hhigh, hhigh', ↓reduceIte] at heq
      · -- Both above: the unique high edge of the common inner endpoint.
        have ha : inEnd e he = inEnd e' he' := Option.some.inj heq
        have h₁ := inEnd_incident e he
        have h₂ := inEnd_incident e' he'
        rw [ha] at h₁
        have hθ := inL_theta _ (hends e' he').2.1
        exact eq_of_theta_lt H D regular h₁ h₂ (lt_of_le_of_lt hθ hhigh) (lt_of_le_of_lt hθ hhigh')
      · exact absurd heq (by simp)
      · exact absurd heq (by simp)
      · -- Both at the median position of `v`.
        exact pos_injective H D (by omega)
  calc (H.cutFinset L).card ≤ (insert none ((bagN H D j₀).image some)).card :=
        Finset.card_le_card_of_injOn φ maps inj
    _ ≤ ((bagN H D j₀).image some).card + 1 := Finset.card_insert_le _ _
    _ ≤ (bagN H D j₀).card + 1 := by
        gcongr
        exact Finset.card_image_le
    _ ≤ p + 2 := by
        have := card_bagN_le H D hbag j₀
        omega

end MedianOrdering

end Cutwidth
end Algebraic
