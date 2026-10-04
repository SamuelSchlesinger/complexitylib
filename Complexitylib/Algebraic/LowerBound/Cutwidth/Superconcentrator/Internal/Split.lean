/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Superconcentrator.Internal.Cut

/-!
# Splitting the vertices of a multigraph into directed paths

Fix a set `K` of kept edges. Every vertex `w` is replaced by a directed path of *slots*, one
for each end at `w` of a kept edge: first the ends of the kept edges entering `w`, then the
ends of those leaving `w`. Each kept edge joins the slot of its tail end to the slot of its
head end, and consecutive slots of a path are joined by a path edge.

Every slot meets at most two path edges and one kept edge, and no edge is a loop. A vertex
with `s > 0` slots contributes `s` vertices and `s - 1` path edges, so the number of edges
minus the number of vertices is the number of kept edges minus the number of vertices with a
slot. A directed walk entering a vertex along a kept edge arrives at an entering slot, and the
path reaches every leaving slot from there, so directed walks lift; a lifted walk stays in
the paths of the vertices of the original walk, so vertex-disjoint walks lift to
vertex-disjoint walks.

Keeping the edges whose tail lies in the undirected component of a vertex `r` makes the split
graph connected. Applied to a superconcentrator whose terminals lie in that component, the
split graph is a superconcentrator, with each input placed at the first slot of its path and
each output at the last.
-/

@[expose] public section

open scoped Classical

namespace Algebraic.Cutwidth.Superconcentrator.Internal

open Multigraph Relation

variable {V E : Type} (G : Multigraph V E) (K : Finset E)

/-- Two elements of a sigma type of `Fin` fibres are equal when their components are. -/
theorem sigma_fin_eq_iff {f : V → ℕ} {a b : Σ w : V, Fin (f w)} :
    a = b ↔ a.1 = b.1 ∧ (a.2 : ℕ) = b.2 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · obtain ⟨w, k⟩ := a
    obtain ⟨w', k'⟩ := b
    rintro ⟨h₁, h₂⟩
    simp only at h₁ h₂
    subst h₁
    rw [Fin.ext h₂]

/-! ### Positions in a finite set -/

/-- The position of `e` in a fixed enumeration of `s`. -/
noncomputable def pos (s : Finset E) (e : E) (h : e ∈ s) : ℕ :=
  (s.equivFin ⟨e, h⟩ : ℕ)

theorem pos_lt {s : Finset E} {e : E} (h : e ∈ s) : pos s e h < s.card :=
  (s.equivFin ⟨e, h⟩).isLt

theorem eq_of_pos_eq {s t : Finset E} (hst : s = t) {e₁ e₂ : E} {h₁ : e₁ ∈ s} {h₂ : e₂ ∈ t}
    (h : pos s e₁ h₁ = pos t e₂ h₂) : e₁ = e₂ := by
  subst hst
  have : s.equivFin ⟨e₁, h₁⟩ = s.equivFin ⟨e₂, h₂⟩ := Fin.ext h
  exact congrArg Subtype.val (s.equivFin.injective this)

/-! ### The split graph -/

/-- The kept edges directed into `w`. -/
noncomputable def inEdges (w : V) : Finset E :=
  K.filter fun e => G.snd e = w

/-- The kept edges directed out of `w`. -/
noncomputable def outEdges (w : V) : Finset E :=
  K.filter fun e => G.fst e = w

/-- The number of slots of `w`: the number of ends at `w` of kept edges. -/
noncomputable def slots (w : V) : ℕ :=
  (inEdges G K w).card + (outEdges G K w).card

/-- The vertices of the split graph: the slots of all vertices. -/
abbrev SplitVertex : Type :=
  Σ w : V, Fin (slots G K w)

/-- The edges of the split graph: the kept edges and the path edges joining consecutive
slots. -/
abbrev SplitEdge : Type :=
  {e // e ∈ K} ⊕ Σ w : V, Fin (slots G K w - 1)

theorem mem_inEdges_snd (e : {e // e ∈ K}) : e.1 ∈ inEdges G K (G.snd e.1) := by
  simp [inEdges, e.2]

theorem mem_outEdges_fst (e : {e // e ∈ K}) : e.1 ∈ outEdges G K (G.fst e.1) := by
  simp [outEdges, e.2]

/-- The slot at which a kept edge leaves its tail. -/
noncomputable def tail (e : {e // e ∈ K}) : SplitVertex G K :=
  ⟨G.fst e.1, ⟨(inEdges G K (G.fst e.1)).card +
      pos (outEdges G K (G.fst e.1)) e.1 (mem_outEdges_fst G K e), by
    have := pos_lt (mem_outEdges_fst G K e)
    unfold slots
    omega⟩⟩

/-- The slot at which a kept edge enters its head. -/
noncomputable def head (e : {e // e ∈ K}) : SplitVertex G K :=
  ⟨G.snd e.1, ⟨pos (inEdges G K (G.snd e.1)) e.1 (mem_inEdges_snd G K e), by
    have := pos_lt (mem_inEdges_snd G K e)
    unfold slots
    omega⟩⟩

/-- The split graph: kept edges run from tail slots to head slots, and path edges from each
slot to the next slot of the same vertex. -/
noncomputable def split : Multigraph (SplitVertex G K) (SplitEdge G K) where
  fst
    | .inl e => tail G K e
    | .inr x => ⟨x.1, ⟨x.2, by have := x.2.isLt; omega⟩⟩
  snd
    | .inl e => head G K e
    | .inr x => ⟨x.1, ⟨x.2 + 1, by have := x.2.isLt; omega⟩⟩

variable {G K}

theorem tail_ne_head (a b : {e // e ∈ K}) : tail G K a ≠ head G K b := by
  intro h
  rw [sigma_fin_eq_iff] at h
  obtain ⟨h₁, h₂⟩ := h
  simp only [tail, head] at h₁ h₂
  have hlt := pos_lt (mem_inEdges_snd G K b)
  have hc : (inEdges G K (G.fst a.1)).card = (inEdges G K (G.snd b.1)).card := by rw [h₁]
  omega

theorem tail_injective : Function.Injective (tail G K) := by
  intro a b h
  rw [sigma_fin_eq_iff] at h
  obtain ⟨h₁, h₂⟩ := h
  simp only [tail] at h₁ h₂
  have hc : (inEdges G K (G.fst a.1)).card = (inEdges G K (G.fst b.1)).card := by rw [h₁]
  exact Subtype.ext (eq_of_pos_eq (by rw [h₁]) (by omega : pos (outEdges G K (G.fst a.1)) a.1
    (mem_outEdges_fst G K a) = pos (outEdges G K (G.fst b.1)) b.1 (mem_outEdges_fst G K b)))

theorem head_injective : Function.Injective (head G K) := by
  intro a b h
  rw [sigma_fin_eq_iff] at h
  obtain ⟨h₁, h₂⟩ := h
  simp only [head] at h₁ h₂
  exact Subtype.ext (eq_of_pos_eq (by rw [h₁]) h₂)

/-- The split graph has no loops. -/
theorem split_loopless : (split G K).Loopless := by
  rintro (e | x) h
  · exact tail_ne_head e e h
  · rw [sigma_fin_eq_iff] at h
    simp [split] at h

/-- Every slot meets at most three edges: the kept edge of the slot and two path edges. -/
theorem split_maxDegreeLE [Fintype V] : (split G K).MaxDegreeLE 3 := by
  rintro ⟨w, k⟩
  let φ : SplitEdge G K → Fin 3 := fun
    | .inl _ => 0
    | .inr x => if (x.2 : ℕ) = k then 1 else 2
  have hinj : Set.InjOn φ ((split G K).edgesAt ⟨w, k⟩ : Set (SplitEdge G K)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, mem_edgesAt] at ha hb
    rcases a with a | ⟨wa, ja⟩ <;> rcases b with b | ⟨wb, jb⟩
    · congr 1
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact tail_injective ((ha : tail G K a = _).trans (hb : tail G K b = _).symm)
      · exact absurd ((ha : tail G K a = _).trans (hb : head G K b = _).symm) (tail_ne_head a b)
      · exact absurd ((hb : tail G K b = _).trans (ha : head G K a = _).symm) (tail_ne_head b a)
      · exact head_injective ((ha : head G K a = _).trans (hb : head G K b = _).symm)
    · simp only [φ] at hab
      split_ifs at hab <;> simp at hab
    · simp only [φ] at hab
      split_ifs at hab <;> simp at hab
    · simp only [Incident, split, sigma_fin_eq_iff] at ha hb
      simp only [φ] at hab
      have hw : wa = wb := by
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> exact ha.1.trans hb.1.symm
      subst hw
      obtain rfl : ja = jb := by
        apply Fin.ext
        split_ifs at hab with h₁ h₂ h₂ <;> simp at hab <;> omega
      rfl
  calc (split G K).degree ⟨w, k⟩ ≤ (Finset.univ : Finset (Fin 3)).card :=
        Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    _ = 3 := by simp

/-! ### Counting -/

theorem sum_card_inEdges [Fintype V] : ∑ w, (inEdges G K w).card = K.card :=
  (Finset.card_eq_sum_card_fiberwise (f := G.snd) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))).symm

theorem sum_card_outEdges [Fintype V] : ∑ w, (outEdges G K w).card = K.card :=
  (Finset.card_eq_sum_card_fiberwise (f := G.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))).symm

/-- The split graph has two slots for every kept edge. -/
theorem card_splitVertex [Fintype V] : Fintype.card (SplitVertex G K) = 2 * K.card := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [show ∑ w, slots G K w = K.card + K.card by
    simp only [slots, Finset.sum_add_distrib, sum_card_inEdges, sum_card_outEdges]]
  ring

/-- Edges minus vertices of the split graph: kept edges minus vertices with a slot. -/
theorem card_splitEdge_add [Fintype V] :
    Fintype.card (SplitEdge G K) + (Finset.univ.filter fun w => slots G K w ≠ 0).card =
      K.card + Fintype.card (SplitVertex G K) := by
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_sigma, Fintype.card_sigma,
    Finset.card_filter]
  simp only [Fintype.card_fin]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> omega

/-! ### Walks inside one vertex path -/

/-- Directed steps of the split graph between slots of vertices in `P`. -/
def stepIn (P : Set V) (a b : SplitVertex G K) : Prop :=
  (split G K).DirAdj a b ∧ a.1 ∈ P ∧ b.1 ∈ P

theorem reflTransGen_forward_aux (P : Set V) :
    ∀ (d : ℕ) (w : V) (i j : Fin (slots G K w)), w ∈ P → (j : ℕ) = i + d →
      ReflTransGen (stepIn (G := G) (K := K) P) ⟨w, i⟩ ⟨w, j⟩
  | 0, w, i, j, _, h => by
    obtain rfl : i = j := Fin.ext (by omega)
    exact .refl
  | d + 1, w, i, j, hw, h => by
    have hj := j.isLt
    have hstep : (j : ℕ) - 1 < slots G K w - 1 := by omega
    refine (reflTransGen_forward_aux P d w i ⟨j - 1, by omega⟩ hw (by simp only; omega)).tail
      ⟨⟨.inr ⟨w, ⟨j - 1, hstep⟩⟩, rfl, ?_⟩, hw, hw⟩
    rw [sigma_fin_eq_iff]
    refine ⟨rfl, ?_⟩
    show (j : ℕ) - 1 + 1 = j
    omega

/-- Inside the path of a vertex of `P`, each slot reaches every later slot. -/
theorem reflTransGen_forward (P : Set V) {x y : SplitVertex G K} (hxy : x.1 = y.1)
    (hx : x.1 ∈ P) (hle : (x.2 : ℕ) ≤ y.2) : ReflTransGen (stepIn P) x y := by
  obtain ⟨w, i⟩ := x
  obtain ⟨w', j⟩ := y
  simp only at hxy hx hle
  subst hxy
  exact reflTransGen_forward_aux P (j - i) w i j hx (by omega)

/-- Any two slots of one vertex are joined in the split graph. -/
theorem reflTransGen_adj_of_fst_eq {x y : SplitVertex G K} (hxy : x.1 = y.1) :
    ReflTransGen (split G K).Adj x y := by
  have h0 : 0 < slots G K x.1 := by have := x.2.isLt; omega
  have toAdj : ∀ {a b : SplitVertex G K}, ReflTransGen (stepIn Set.univ) a b →
      ReflTransGen (split G K).Adj a b := fun h =>
    ReflTransGen.mono (fun a b hab => by
      obtain ⟨⟨e, h₁, h₂⟩, -, -⟩ := hab
      exact ⟨e, Or.inl ⟨h₁, h₂⟩⟩) _ _ h
  have hx := toAdj (reflTransGen_forward (x := ⟨x.1, ⟨0, h0⟩⟩) (y := x) Set.univ rfl trivial
    (Nat.zero_le _))
  have hy := toAdj (reflTransGen_forward (x := ⟨x.1, ⟨0, h0⟩⟩) (y := y) Set.univ hxy trivial
    (Nat.zero_le _))
  exact (reflTransGen_adj_symm hx).trans hy

end Algebraic.Cutwidth.Superconcentrator.Internal
