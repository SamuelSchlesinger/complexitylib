/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Ordering.Internal.Graph

/-!
# Proofs for the ordering transfer

The components of the wire graph are closed sets of wires (`component_closed`), and a closed
set contributes no crossing signals to a split (`forward_union_of_closed`,
`backward_union_of_closed`). The ranking of the wires lists the components one after another,
ordered by their first wire, and inside each component follows the vertex order that the
graph-ordering bound gives its wire graph (`WireGraph`). A prefix up to a wire `w` is then the
union of whole earlier components, which are closed, and of the wires of the component of `w`
whose vertices lie in a lower set of that order. Its crossing signals are therefore bounded by
a lower-set cut of one connected wire graph (`exists_rank`).
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Internal

open scoped Classical
open SingleCut

variable {σ : Signature} {n s : Nat}

/-! ## Components of the wire graph -/

section Components

variable {p : Program σ n s}

theorem linked_symm {u v : Wire n s} (h : Linked p u v) : Linked p v u :=
  Or.symm h

theorem reflTransGen_linked_symm {u v : Wire n s} (h : Relation.ReflTransGen (Linked p) u v) :
    Relation.ReflTransGen (Linked p) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.head (linked_symm step) ih

theorem linked_of_reads {g : Fin s} {w : Wire n s} (h : p.Reads g w) :
    Linked p (Wire.gate g) w :=
  Or.inl ⟨g, rfl, h⟩

theorem mem_component {v w : Wire n s} :
    v ∈ component p w ↔ Relation.ReflTransGen (Linked p) w v := by
  simp [component]

variable (p) in
theorem mem_component_self (w : Wire n s) : w ∈ component p w :=
  mem_component.mpr Relation.ReflTransGen.refl

variable (p) in
/-- A component is closed: a gate lies in it exactly when the wires it reads do. -/
theorem component_closed (w : Wire n s) (g : Fin s) (v : Wire n s) (h : p.Reads g v) :
    Wire.gate g ∈ component p w ↔ v ∈ component p w := by
  rw [mem_component, mem_component]
  exact ⟨fun hg => hg.tail (linked_of_reads h), fun hv => hv.tail (linked_symm (linked_of_reads h))⟩

theorem component_eq_of_mem {v w : Wire n s} (h : v ∈ component p w) :
    component p v = component p w := by
  have hwv := mem_component.mp h
  ext u
  rw [mem_component, mem_component]
  exact ⟨fun hvu => hwv.trans hvu, fun hwu => (reflTransGen_linked_symm hwv).trans hwu⟩

variable (p) in
/-- Any two wires of a component are joined by a path of linked wires. -/
theorem component_connected (w : Wire n s) :
    ∀ u ∈ component p w, ∀ v ∈ component p w, Relation.ReflTransGen (Linked p) u v :=
  fun _ hu _ hv => (reflTransGen_linked_symm (mem_component.mp hu)).trans (mem_component.mp hv)

/-- A gate and a wire it reads have the same component. -/
theorem component_eq_of_reads {g : Fin s} {v : Wire n s} (h : p.Reads g v) :
    component p (Wire.gate g) = component p v :=
  (component_eq_of_mem ((component_closed p (Wire.gate g) g v h).mp
    (mem_component_self p _))).symm

variable (p) in
/-- The component of a wire, as a closed set. -/
noncomputable def componentSet (w : Wire n s) : ClosedSet p :=
  ⟨component p w, component_closed p w⟩

theorem componentSet_eq {v w : Wire n s} (h : component p v = component p w) :
    componentSet p v = componentSet p w := by
  unfold componentSet
  congr 1

end Components

/-! ## Closed sets contribute no crossing signals -/

section Closed

variable {p : Program σ n s}

/-- Adding a closed set disjoint from `P` does not change the forward signals of `P`. -/
theorem forward_union_of_closed {Q P : Finset (Wire n s)}
    (hQ : ∀ g w, p.Reads g w → (Wire.gate g ∈ Q ↔ w ∈ Q)) (hdisj : Disjoint Q P) :
    forward p (Q ∪ P) = forward p P := by
  ext w
  simp only [mem_forward, Finset.mem_union]
  constructor
  · rintro ⟨hw, g, hg, hr⟩
    have hgQ : Wire.gate g ∉ Q := fun h => hg (Or.inl h)
    have hwQ : w ∉ Q := fun h => hgQ ((hQ g w hr).mpr h)
    exact ⟨hw.resolve_left hwQ, g, fun h => hg (Or.inr h), hr⟩
  · rintro ⟨hw, g, hg, hr⟩
    have hwQ : w ∉ Q := Finset.disjoint_right.mp hdisj hw
    have hgQ : Wire.gate g ∉ Q := fun h => hwQ ((hQ g w hr).mp h)
    exact ⟨Or.inr hw, g, fun h => h.elim hgQ hg, hr⟩

/-- Adding a closed set disjoint from `P` does not change the backward signals of `P`. -/
theorem backward_union_of_closed {Q P : Finset (Wire n s)}
    (hQ : ∀ g w, p.Reads g w → (Wire.gate g ∈ Q ↔ w ∈ Q)) (hdisj : Disjoint Q P) :
    backward p (Q ∪ P) = backward p P := by
  ext w
  simp only [mem_backward, Finset.mem_union, not_or]
  constructor
  · rintro ⟨⟨hwQ, hwP⟩, g, hg, hr⟩
    have hgQ : Wire.gate g ∉ Q := fun h => hwQ ((hQ g w hr).mp h)
    exact ⟨hwP, g, hg.resolve_left hgQ, hr⟩
  · rintro ⟨hwP, g, hg, hr⟩
    have hgQ : Wire.gate g ∉ Q := Finset.disjoint_right.mp hdisj hg
    have hwQ : w ∉ Q := fun h => hgQ ((hQ g w hr).mpr h)
    exact ⟨⟨hwQ, hwP⟩, g, Or.inr hg, hr⟩

/-- A closed set has no forward signals. -/
theorem forward_eq_empty_of_closed {Q : Finset (Wire n s)}
    (hQ : ∀ g w, p.Reads g w → (Wire.gate g ∈ Q ↔ w ∈ Q)) : forward p Q = ∅ := by
  ext w
  simp only [mem_forward, Finset.notMem_empty, iff_false, not_and, not_exists]
  intro hw g hg hr
  exact hg ((hQ g w hr).mpr hw)

/-- A closed set has no backward signals. -/
theorem backward_eq_empty_of_closed {Q : Finset (Wire n s)}
    (hQ : ∀ g w, p.Reads g w → (Wire.gate g ∈ Q ↔ w ∈ Q)) : backward p Q = ∅ := by
  ext w
  simp only [mem_backward, Finset.notMem_empty, iff_false, not_and, not_exists]
  intro hw g hg hr
  exact hw ((hQ g w hr).mp hg)

end Closed

/-! ## Ranking by an injective key -/

section Key

variable {α β : Type*} [Fintype α] [LinearOrder β]

/-- In a finite set ranked by an injective key, the number of elements with a smaller key
compares like the keys. -/
theorem card_lt_le_card_lt_iff (f : α → β) (a b : α) :
    (Finset.univ.filter fun x => f x < f a).card ≤
        (Finset.univ.filter fun x => f x < f b).card ↔ f a ≤ f b := by
  constructor
  · intro h
    by_contra hab
    rw [not_le] at hab
    have hsub : (Finset.univ.filter fun x => f x < f b) ⊂
        (Finset.univ.filter fun x => f x < f a) := by
      rw [Finset.ssubset_iff_of_subset (fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.trans hab)]
      exact ⟨b, by simpa using hab, by simp⟩
    exact absurd (Finset.card_lt_card hsub) (not_lt.mpr h)
  · intro h
    exact Finset.card_le_card fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact lt_of_lt_of_le hx h

theorem card_lt_lt_card (f : α → β) (a : α) :
    (Finset.univ.filter fun x => f x < f a).card < Fintype.card α := by
  rw [← Finset.card_univ]
  exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨a, Finset.mem_univ _, lt_irrefl _⟩)

end Key

/-! ## The ranking of the wires -/

section Ranking

variable {p : Program σ n s}

theorem index_injective : Function.Injective (fun w : Wire n s => w.index) := by
  rintro (a | a) (b | b) h <;>
    simp only [Cslib.Circuits.Wire.index_input, Cslib.Circuits.Wire.index_gate, Fin.ext_iff,
      Fin.val_castAdd, Fin.val_natAdd] at h
  · exact congrArg _ (Fin.ext h)
  · omega
  · omega
  · exact congrArg _ (Fin.ext (by omega))

variable (p) in
/-- The least index of a wire of the component of `w`; it identifies the component. -/
noncomputable def componentId (w : Wire n s) : WithTop Nat :=
  ((component p w).image fun v => (v.index : Nat)).min

theorem componentId_congr {v w : Wire n s} (h : component p v = component p w) :
    componentId p v = componentId p w := by
  unfold componentId
  rw [h]

theorem exists_componentId_eq (w : Wire n s) :
    ∃ v ∈ component p w, componentId p w = ((v.index : Nat) : WithTop Nat) := by
  obtain ⟨a, ha⟩ := Finset.min_of_nonempty
    (Finset.image_nonempty.mpr ⟨w, mem_component_self p w⟩ :
      ((component p w).image fun v => (v.index : Nat)).Nonempty)
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_min ha)
  exact ⟨v, hv, ha⟩

theorem component_eq_of_componentId_eq {v w : Wire n s} (h : componentId p v = componentId p w) :
    component p v = component p w := by
  obtain ⟨v', hv', hv⟩ := exists_componentId_eq (p := p) v
  obtain ⟨w', hw', hw⟩ := exists_componentId_eq (p := p) w
  have : v' = w' := index_injective (Fin.ext (by
    have := hv.symm.trans (h.trans hw)
    exact_mod_cast this))
  subst this
  exact (component_eq_of_mem hv').symm.trans (component_eq_of_mem hw')

variable (ord : ∀ K : ClosedSet p, LinearOrder (WireGraph.Vertex K))

/-- The position of a wire of `K` in the order chosen on the wire graph of `K`. -/
noncomputable def posIn (K : ClosedSet p) (w : Wire n s) : Nat :=
  letI := ord K
  if h : w ∈ K.carrier then
    (Finset.univ.filter fun x : WireGraph.Vertex K => x < Sum.inl ⟨w, h⟩).card
  else 0

theorem posIn_le_posIn_iff (K : ClosedSet p) {u v : Wire n s} (hu : u ∈ K.carrier)
    (hv : v ∈ K.carrier) :
    posIn ord K u ≤ posIn ord K v ↔
      (ord K).le (Sum.inl ⟨u, hu⟩ : WireGraph.Vertex K) (Sum.inl ⟨v, hv⟩) := by
  let _ := ord K
  unfold posIn
  simp only [hu, hv, ↓reduceDIte]
  exact card_lt_le_card_lt_iff id _ _

/-- The position of a wire in the order chosen on its component. -/
noncomputable def pos (w : Wire n s) : Nat :=
  posIn ord (componentSet p w) w

theorem pos_eq_posIn {v w : Wire n s} (h : v ∈ component p w) :
    pos ord v = posIn ord (componentSet p w) v := by
  unfold pos
  rw [componentSet_eq (component_eq_of_mem h)]

/-- The ranking key: the component's identifier, then the position inside the component. -/
noncomputable def key (w : Wire n s) : WithTop Nat ×ₗ Nat :=
  toLex (componentId p w, pos ord w)

theorem key_le_key_iff (v w : Wire n s) :
    key ord v ≤ key ord w ↔ componentId p v < componentId p w ∨
      ∃ hv : v ∈ component p w, (ord (componentSet p w)).le
        (Sum.inl ⟨v, hv⟩ : WireGraph.Vertex (componentSet p w))
        (Sum.inl ⟨w, mem_component_self p w⟩) := by
  unfold key
  rw [Prod.Lex.toLex_le_toLex]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨hid, hpos⟩
    have hv : v ∈ component p w := by
      rw [← component_eq_of_componentId_eq hid]
      exact mem_component_self p v
    refine ⟨hv, ?_⟩
    rw [pos_eq_posIn ord hv, pos_eq_posIn ord (mem_component_self p w)] at hpos
    exact (posIn_le_posIn_iff ord (componentSet p w) hv (mem_component_self p w)).mp hpos
  · rintro ⟨hv, hle⟩
    refine ⟨componentId_congr (component_eq_of_mem hv), ?_⟩
    rw [pos_eq_posIn ord hv, pos_eq_posIn ord (mem_component_self p w)]
    exact (posIn_le_posIn_iff ord (componentSet p w) hv (mem_component_self p w)).mpr hle

theorem key_injective : Function.Injective (key (p := p) ord) := by
  intro v w h
  have hvw := (key_le_key_iff ord v w).mp h.le
  have hwv := (key_le_key_iff ord w v).mp h.ge
  have hid : componentId p v = componentId p w := congrArg (fun k => (ofLex k).1) h
  rcases hvw with hlt | ⟨hv, hle⟩
  · exact absurd hid hlt.ne
  rcases hwv with hlt | ⟨hw, hle'⟩
  · exact absurd hid.symm hlt.ne
  have hcomp := component_eq_of_mem hv
  have hK := componentSet_eq hcomp
  -- Compare inside the component of `w`.
  have hle'' : (ord (componentSet p w)).le
      (Sum.inl ⟨w, mem_component_self p w⟩ : WireGraph.Vertex (componentSet p w))
      (Sum.inl ⟨v, hv⟩) := by
    have hpos : pos ord w ≤ pos ord v := by
      have := congrArg (fun k => (ofLex k).2) h
      simp only [key, ofLex_toLex] at this
      omega
    rw [pos_eq_posIn ord (mem_component_self p w), pos_eq_posIn ord hv] at hpos
    exact (posIn_le_posIn_iff ord _ _ _).mp hpos
  let _ := ord (componentSet p w)
  have := le_antisymm hle hle''
  exact congrArg Subtype.val (Sum.inl_injective this)

/-- The rank of a wire: the number of wires with a smaller key. -/
noncomputable def rank (w : Wire n s) : Nat :=
  (Finset.univ.filter fun v => key (p := p) ord v < key ord w).card

theorem rank_le_rank_iff (v w : Wire n s) : rank ord v ≤ rank ord w ↔ key ord v ≤ key ord w :=
  card_lt_le_card_lt_iff (key ord) v w

theorem rank_injective : Function.Injective (rank (p := p) ord) := fun v w h =>
  key_injective ord (le_antisymm ((rank_le_rank_iff ord v w).mp h.le)
    ((rank_le_rank_iff ord w v).mp h.ge))

theorem rank_lt (w : Wire n s) : rank (p := p) ord w < n + s := by
  have := card_lt_lt_card (key (p := p) ord) w
  rwa [Cslib.Circuits.Wire.card] at this

/-- The vertices of the wire graph of the component of `w` up to the vertex of `w`. -/
noncomputable def lowerUpTo (w : Wire n s) : Finset (WireGraph.Vertex (componentSet p w)) :=
  Finset.univ.filter fun x => (ord (componentSet p w)).le x (Sum.inl ⟨w, mem_component_self p w⟩)

theorem isLowerSet_lowerUpTo (w : Wire n s) :
    @IsLowerSet _ (ord (componentSet p w)).toLE (lowerUpTo ord w : Set _) := by
  let _ := ord (componentSet p w)
  intro x y hxy hx
  rw [Finset.mem_coe, lowerUpTo, Finset.mem_filter] at hx ⊢
  exact ⟨Finset.mem_univ _, le_trans hxy hx.2⟩

/-- **The prefix decomposition.** The prefix up to `w` is the union of the wires of earlier
components and of the wires of the component of `w` whose vertices lie up to that of `w`. -/
theorem prefixUpTo_rank_eq (w : Wire n s) :
    prefixUpTo (rank ord) w = (Finset.univ.filter fun v => componentId p v < componentId p w) ∪
      WireGraph.wiresIn (componentSet p w) (lowerUpTo ord w) := by
  ext v
  simp only [prefixUpTo, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    WireGraph.mem_wiresIn, lowerUpTo]
  rw [rank_le_rank_iff, key_le_key_iff]
  rfl

/-- The earlier components form a closed set. -/
theorem earlier_closed (w : Wire n s) :
    ∀ g v, p.Reads g v → (Wire.gate g ∈ Finset.univ.filter (fun u => componentId p u <
      componentId p w) ↔ v ∈ Finset.univ.filter fun u => componentId p u < componentId p w) := by
  intro g v hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [componentId_congr (component_eq_of_reads hr)]

theorem earlier_disjoint (w : Wire n s) :
    Disjoint (Finset.univ.filter fun u => componentId p u < componentId p w)
      (WireGraph.wiresIn (componentSet p w) (lowerUpTo ord w)) := by
  rw [Finset.disjoint_right]
  intro v hv hlt
  have hvK := WireGraph.wiresIn_subset _ _ hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlt
  rw [componentId_congr (component_eq_of_mem hvK)] at hlt
  exact lt_irrefl _ hlt

/-- **Prefix crossings are lower-set cuts of one component.** -/
theorem card_crossing_le_cut (w : Wire n s) :
    (forward p (prefixUpTo (rank ord) w)).card + (backward p (prefixUpTo (rank ord) w)).card ≤
      ((WireGraph.graph (componentSet p w)).cut (lowerUpTo ord w)).card := by
  rw [prefixUpTo_rank_eq, forward_union_of_closed (earlier_closed w) (earlier_disjoint ord w),
    backward_union_of_closed (earlier_closed w) (earlier_disjoint ord w)]
  exact WireGraph.card_forward_add_card_backward_le _ _

end Ranking

/-! ## The ordering transfer -/

/-- The ordering hypothesis forces a nonnegative additive constant: the empty lower set of the
one-vertex graph has an empty cut. -/
theorem orderingBound_nonneg {A η C : ℝ} (order : Multigraph.OrderingBound A η C) : 0 ≤ C := by
  obtain ⟨_, hb⟩ := order Unit Empty ⟨Empty.elim, Empty.elim⟩ (fun e => e.elim)
    (fun v => by simp [Multigraph.degree, Multigraph.edgesAt])
    (fun u v => by cases u; cases v; exact Relation.ReflTransGen.refl)
  have := hb ∅ (by intro a b _ ha; simp at ha)
  simpa using this

/-- **The ordering transfer.** -/
theorem exists_rank {A η C : ℝ} (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C)
    (p : Program σ n s) (hp : p.FanInAtMost 2) :
    ∃ rank : Wire n s → Nat, Function.Injective rank ∧ (∀ w, rank w < n + s) ∧ ∀ w,
      (((forward p (prefixUpTo rank w)).card + (backward p (prefixUpTo rank w)).card : Nat) :
          ℝ) ≤
        (A + η) * max (((gatesIn (component p w)).card : ℝ) - (inputsIn (component p w)).card) 0 +
          3 * Real.logb 2 (n + 3 * s) + C := by
  have choice : ∀ K : ClosedSet p, ∃ _ : LinearOrder (WireGraph.Vertex K),
      K.carrier.Nonempty →
        (∀ u ∈ K.carrier, ∀ v ∈ K.carrier, Relation.ReflTransGen (Linked p) u v) →
        ∀ L : Finset (WireGraph.Vertex K), IsLowerSet (L : Set (WireGraph.Vertex K)) →
          (((WireGraph.graph K).cut L).card : ℝ) ≤
            (A + η) * max ((Fintype.card (WireGraph.Edge K) : ℝ) -
              Fintype.card (WireGraph.Vertex K)) 0 +
              3 * Real.logb 2 (Fintype.card (WireGraph.Vertex K)) + C := by
    intro K
    by_cases h : K.carrier.Nonempty ∧
        ∀ u ∈ K.carrier, ∀ v ∈ K.carrier, Relation.ReflTransGen (Linked p) u v
    · obtain ⟨o, ho⟩ := order _ _ (WireGraph.graph K) (WireGraph.loopless K)
        (WireGraph.maxDegreeLE_three K hp) (WireGraph.connected K h.1 h.2)
      exact ⟨o, fun _ _ => ho⟩
    · exact ⟨LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective,
        fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩
  choose ord hord using choice
  refine ⟨rank ord, rank_injective ord, rank_lt ord, fun w => ?_⟩
  set K := componentSet p w with hK
  have hcut := hord K ⟨w, mem_component_self p w⟩ (component_connected p w) (lowerUpTo ord w)
    (isLowerSet_lowerUpTo ord w)
  have hcross : (((forward p (prefixUpTo (rank ord) w)).card +
      (backward p (prefixUpTo (rank ord) w)).card : Nat) : ℝ) ≤
      ((WireGraph.graph K).cut (lowerUpTo ord w)).card := by
    exact_mod_cast card_crossing_le_cut ord w
  have hdiff := WireGraph.card_edge_sub_card_vertex_le K hp
  have hVle := WireGraph.card_vertex_le K hp
  have hVpos : (0 : ℝ) < Fintype.card (WireGraph.Vertex K) := by
    have : Nonempty (WireGraph.Vertex K) := ⟨Sum.inl ⟨w, mem_component_self p w⟩⟩
    exact_mod_cast Fintype.card_pos
  have hin : (inputsIn K.carrier).card ≤ n := by
    simpa using Finset.card_le_univ (inputsIn K.carrier)
  have hgate : (gatesIn K.carrier).card ≤ s := by
    simpa using Finset.card_le_univ (gatesIn K.carrier)
  have hV : (Fintype.card (WireGraph.Vertex K) : ℝ) ≤ n + 3 * s := by
    have : Fintype.card (WireGraph.Vertex K) ≤ n + 3 * s := by omega
    exact_mod_cast this
  have hlog : Real.logb 2 (Fintype.card (WireGraph.Vertex K)) ≤ Real.logb 2 (n + 3 * s) :=
    (Real.logb_le_logb one_lt_two hVpos (hVpos.trans_le hV)).mpr hV
  have hmax : (A + η) * max ((Fintype.card (WireGraph.Edge K) : ℝ) -
      Fintype.card (WireGraph.Vertex K)) 0 ≤
      (A + η) * max (((gatesIn (component p w)).card : ℝ) - (inputsIn (component p w)).card) 0 :=
    mul_le_mul_of_nonneg_left (max_le_max hdiff le_rfl) hAη
  linarith

/-- **The ordering transfer for a connected wire graph.** -/
theorem exists_rank_of_connected {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) (p : Program σ n s) (hp : p.FanInAtMost 2)
    (hconn : ∀ u v : Wire n s, Relation.ReflTransGen (Linked p) u v) :
    ∃ rank : Wire n s → Nat, Function.Injective rank ∧ (∀ w, rank w < n + s) ∧ ∀ t,
      (((forward p (prefixBelow rank t)).card + (backward p (prefixBelow rank t)).card : Nat) :
          ℝ) ≤
        (A + η) * max ((s : ℝ) - n) 0 + 3 * Real.logb 2 (n + 3 * s) + C := by
  obtain ⟨rank, hinj, hlt, hbound⟩ := exists_rank hAη order p hp
  refine ⟨rank, hinj, hlt, fun t => ?_⟩
  have hC := orderingBound_nonneg order
  have hlog : 0 ≤ Real.logb 2 ((n : ℝ) + 3 * s) := by
    rcases Nat.eq_zero_or_pos (n + 3 * s) with h | h
    · have : ((n : ℝ) + 3 * s) = 0 := by exact_mod_cast h
      rw [this, Real.logb_zero]
    · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)
  have hmax0 : 0 ≤ (A + η) * max ((s : ℝ) - n) 0 := mul_nonneg hAη (le_max_right _ _)
  by_cases hne : (prefixBelow rank t).Nonempty
  · obtain ⟨w, hw, hmaxw⟩ := Finset.exists_max_image _ rank hne
    have heq : prefixBelow rank t = prefixUpTo rank w := by
      ext v
      simp only [prefixBelow, prefixUpTo, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [prefixBelow, Finset.mem_filter, Finset.mem_univ, true_and] at hw hmaxw
      exact ⟨fun hv => hmaxw v hv, fun hv => lt_of_le_of_lt hv hw⟩
    rw [heq]
    have hcomp : component p w = Finset.univ := by
      ext v
      simp only [Finset.mem_univ, iff_true]
      exact mem_component.mpr (hconn w v)
    have hg : (gatesIn (Finset.univ : Finset (Wire n s))).card = s := by
      simp [gatesIn]
    have hi : (inputsIn (Finset.univ : Finset (Wire n s))).card = n := by
      simp [inputsIn]
    have := hbound w
    rw [hcomp, hg, hi] at this
    exact this
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [forward, backward, Finset.filter_empty, Finset.card_empty, Finset.compl_empty]
    have : (Finset.univ.filter fun w : Wire n s => ∃ g : Fin s, Wire.gate g ∈
        (∅ : Finset (Wire n s)) ∧ p.Reads g w) = ∅ := by
      simp
    rw [this]
    simp only [Finset.card_empty, add_zero, Nat.cast_zero]
    linarith

end Algebraic.Cutwidth.MultiOutput.Internal
