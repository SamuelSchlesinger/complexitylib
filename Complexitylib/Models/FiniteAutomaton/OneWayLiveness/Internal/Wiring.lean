/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Model

/-!
# One-way-liveness proof: Wiring

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Wiring.lean

Module and namespace names, imports, and formatting are adapted to complexitylib.
The machine definitions are shared through `Models.FiniteAutomaton.Defs`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

/-- A perfect matching of ports, represented by a symmetric fixed-point-free relation. -/
@[ext] structure Pairing (P : Type*) where
  /-- The symmetric relation pairing the ports. -/
  link : P → P → Prop
  symm : ∀ {x y}, link x y → link y x
  irrefl : ∀ x, ¬ link x x
  unique : ∀ x, ∃! y, link x y

namespace Pairing
variable {P : Type*} (a : Pairing P)
/-- The unique port paired with the given port. -/
noncomputable def mate (x : P) : P := (a.unique x).choose
lemma mate_link (x : P) : a.link x (a.mate x) := (a.unique x).choose_spec.1
lemma eq_mate {x y : P} (h : a.link x y) : y = a.mate x :=
  (a.unique x).choose_spec.2 y h
lemma mate_involutive : Function.Involutive a.mate := by
  intro x
  exact (a.eq_mate (a.symm (a.mate_link x))).symm
lemma mate_ne (x : P) : a.mate x ≠ x := by
  intro h
  exact a.irrefl x (by simpa only [h] using a.mate_link x)
lemma link_iff (x y : P) : a.link x y ↔ a.mate x = y :=
  ⟨fun h => (a.eq_mate h).symm, fun h => h ▸ a.mate_link x⟩
instance [Finite P] : Finite (Pairing P) :=
  Finite.of_injective Pairing.link (fun _ _ h => Pairing.ext h)
end Pairing


namespace Pairing
variable {P : Type*} (a : Pairing P)

/-- An assignment obeys all wire equalities. -/
def Compatible {C : Type*} (color : P → C) : Prop :=
  ∀ x y, a.link x y → color x = color y

/-- The equivalence relation whose classes are the pairs. -/
def connected (x y : P) : Prop := x = y ∨ a.link x y

lemma connected_refl (x : P) : a.connected x x := Or.inl rfl
lemma connected_symm {x y : P} (h : a.connected x y) : a.connected y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (a.symm h)
lemma connected_trans {x y z : P} (h : a.connected x y) (k : a.connected y z) :
    a.connected x z := by
  rcases h with rfl | h
  · exact k
  rcases k with rfl | k
  · exact Or.inr h
  exact Or.inl ((a.eq_mate (a.symm h)).trans (a.eq_mate k).symm)

/-- The Boolean indicator of the pairing component containing a chosen port. -/
noncomputable def testColor (x : P) (y : P) : Bool := by
  classical
  exact decide (a.connected x y)

@[simp] lemma testColor_self (x : P) : a.testColor x x = true := by
  classical
  simp [testColor, connected]

lemma compatible_testColor (x : P) : a.Compatible (a.testColor x) := by
  classical
  intro u v huv
  apply Bool.eq_iff_iff.mpr
  simp only [testColor, decide_eq_true_eq]
  constructor
  · intro h
    exact a.connected_trans h (.inr huv)
  · intro h
    exact a.connected_trans h (.inr (a.symm huv))

/-- Two-color constraints remember an entire matching, not just rank or
connectivity among one side of its ports. -/
lemma eq_of_compatible {b : Pairing P}
    (h : ∀ c : P → Bool, a.Compatible c ↔ b.Compatible c) : a = b := by
  have sub : ∀ (a b : Pairing P), (∀ c : P → Bool, a.Compatible c → b.Compatible c) →
      ∀ x y, b.link x y → a.link x y := by
    intro a b hab x y hxy
    have he := hab (a.testColor x) (a.compatible_testColor x) x y hxy
    rw [a.testColor_self] at he
    have hc : a.connected x y := by
      simpa only [testColor, decide_eq_true_eq] using he.symm
    rcases hc with heq | hc
    · subst y
      exact (b.irrefl x hxy).elim
    · exact hc
  apply Pairing.ext
  funext x y
  apply propext
  exact ⟨sub b a (fun c => (h c).mpr) x y, sub a b (fun c => (h c).mp) x y⟩

end Pairing

namespace FiniteWiring
open SimpleGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- A finite connected graph with degrees at most two has at most two leaves.
The proof uses the degree-sum formula and the edge-count bound for a connected graph. -/
lemma leaves_card_le_two [DecidableRel G.Adj] (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 2) :
    (Finset.univ.filter fun v => G.degree v = 1).card ≤ 2 := by
  classical
  have hb := hc.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← G.edgeFinset_card] at hb
  have hs : (∑ v, G.degree v) + (Finset.univ.filter fun v => G.degree v = 1).card ≤
      2 * Fintype.card V := by
    calc
      _ = ∑ v, (G.degree v + if G.degree v = 1 then 1 else 0) := by
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ ∑ _v : V, 2 := Finset.sum_le_sum fun v _ => by
        have := hd v
        split_ifs <;> omega
      _ = _ := by simp [Nat.mul_comm]
  rw [G.sum_degrees_eq_twice_card_edges] at hs
  omega

/-- In a finite connected graph of maximum degree two, a leaf has exactly
one other leaf. -/
lemma unique_other_leaf [DecidableRel G.Adj] (hc : G.Connected)
    (hd : ∀ v, G.degree v ≤ 2) (x : V) (hx : G.degree x = 1) :
    ∃! y : V, y ≠ x ∧ G.degree y = 1 := by
  classical
  have ho : Odd (G.degree x) := by simp [hx]
  obtain ⟨y, hyx, hyodd⟩ := G.exists_ne_odd_degree_of_exists_odd_degree x ho
  have hy : G.degree y = 1 := by
    have := hd y
    obtain ⟨k, hk⟩ := hyodd
    omega
  refine ⟨y, ⟨hyx, hy⟩, ?_⟩
  intro z hz
  by_contra hzy
  have hsub : ({x, y, z} : Finset V) ⊆ Finset.univ.filter (fun v => G.degree v = 1) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> simp [hx, hy, hz.2]
  have hnum := Finset.card_le_card hsub
  have hbound := leaves_card_le_two G hc hd
  have hthree : ({x, y, z} : Finset V).card = 3 := by
    simp [Ne.symm hyx, Ne.symm hz.1, Ne.symm hzy]
  omega

/-- Passing to a connected component preserves every vertex degree. -/
lemma component_degree [DecidableRel G.Adj]
    (C : G.ConnectedComponent) [Fintype C] [DecidableRel C.toSimpleGraph.Adj] (v : C) :
    C.toSimpleGraph.degree v = G.degree v.val := by
  classical
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  apply Fintype.card_congr
  refine {
    toFun := fun w => ⟨w.val.val, w.property⟩
    invFun := fun w => ⟨⟨w.val, (C.mem_supp_congr_adj w.property).mp v.property⟩, w.property⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro w; rfl
  · intro w; rfl

/-- Maximum degree two makes the reachable boundary pairing unique, even
when other connected components are cycles. -/
lemma unique_reachable_leaf [DecidableRel G.Adj]
    (hd : ∀ v, G.degree v ≤ 2) (x : V) (hx : G.degree x = 1) :
    ∃! y : V, y ≠ x ∧ G.degree y = 1 ∧ G.Reachable x y := by
  classical
  let C := G.connectedComponentMk x
  let xc : C := ⟨x, rfl⟩
  have hdc : ∀ v : C, C.toSimpleGraph.degree v ≤ 2 := by
    intro v
    rw [component_degree G C]
    exact hd v.val
  have hxc : C.toSimpleGraph.degree xc = 1 := by
    rw [component_degree G C]
    exact hx
  obtain ⟨y, hy, hu⟩ := unique_other_leaf C.toSimpleGraph C.connected_toSimpleGraph hdc xc hxc
  refine ⟨y.val, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro he
    apply hy.1
    exact Subtype.ext he
  · rw [component_degree G C] at hy
    exact hy.2
  · exact (ConnectedComponent.exact y.property).symm
  · intro z hz
    let zc : C := ⟨z, ConnectedComponent.sound hz.2.2.symm⟩
    have hzc : zc ≠ xc ∧ C.toSimpleGraph.degree zc = 1 := by
      constructor
      · intro he; exact hz.1 (congrArg Subtype.val he)
      · rw [component_degree G C]; exact hz.2.1
    exact congrArg Subtype.val (hu zc hzc)

/-- Contract all path components onto their boundary. The degree assumptions
are precisely degree one at the exposed ports and degree zero or two
elsewhere. Closed components disappear. -/
noncomputable def boundaryPairing {P : Type*} (port : P ↪ V)
    [DecidableRel G.Adj] (hd : ∀ v, G.degree v ≤ 2)
    (hb : ∀ v, G.degree v = 1 ↔ ∃ p, port p = v) : Pairing P where
  link x y := x ≠ y ∧ G.Reachable (port x) (port y)
  symm h := ⟨Ne.symm h.1, h.2.symm⟩
  irrefl x h := h.1 rfl
  unique x := by
    classical
    obtain ⟨v, hv, hu⟩ := unique_reachable_leaf G hd (port x) ((hb _).mpr ⟨x, rfl⟩)
    obtain ⟨y, rfl⟩ := (hb v).mp hv.2.1
    refine ⟨y, ⟨?_, hv.2.2⟩, ?_⟩
    · intro h; exact hv.1 (congrArg port h.symm)
    · intro z hz
      apply port.injective
      apply hu
      refine ⟨?_, (hb _).mpr ⟨z, rfl⟩, hz.2⟩
      intro he; exact hz.1 (port.injective he).symm


omit [Fintype V] in
/-- Edge-compatible colors are constant along any finite path. -/
lemma color_eq_of_reachable {C : Type*} (color : V → C)
    (hc : ∀ x y, G.Adj x y → color x = color y) {x y : V}
    (h : G.Reachable x y) : color x = color y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons x y z h p ih => exact (hc x y h).trans ih

/-- Every compatible boundary coloring extends through the wiring. This
justifies replacing a cell's wiring by its boundary matching. -/
lemma coloring_extension {P : Type*} (port : P ↪ V)
    [DecidableRel G.Adj] (hd : ∀ v, G.degree v ≤ 2)
    (hb : ∀ v, G.degree v = 1 ↔ ∃ p, port p = v) (color : P → Bool) :
    (boundaryPairing G port hd hb).Compatible color ↔
      ∃ c : V → Bool, (∀ p, c (port p) = color p) ∧
        ∀ x y, G.Adj x y → c x = c y := by
  classical
  constructor
  · intro hc
    have heq {p q : P} (h : G.Reachable (port p) (port q)) : color p = color q := by
      by_cases hpq : p = q
      · exact congrArg color hpq
      · exact hc p q ⟨hpq, h⟩
    let touches (v : V) : Prop := ∃ p, G.Reachable v (port p)
    let c : V → Bool := fun v => if h : touches v then color h.choose else false
    have hc_at (v : V) (p : P) (hv : G.Reachable v (port p)) : c v = color p := by
      have ht : touches v := ⟨p, hv⟩
      dsimp [c]
      rw [dite_eq_left ht]
      exact heq (ht.choose_spec.symm.trans hv)
    refine ⟨c, ?_, ?_⟩
    · intro p
      exact hc_at (port p) p (.refl _)
    · intro x y hxy
      by_cases ht : touches x
      · obtain ⟨p, hp⟩ := ht
        exact (hc_at x p hp).trans (hc_at y p (hxy.reachable.symm.trans hp)).symm
      · have hty : ¬ touches y := by
          intro hy
          obtain ⟨p, hp⟩ := hy
          exact ht ⟨p, hxy.reachable.trans hp⟩
        simp [c, ht, hty]
  · rintro ⟨c, hp, hc⟩ x y hxy
    have he := color_eq_of_reachable G c hc hxy.2
    simpa only [hp] using he


end FiniteWiring

namespace Pairing
variable {A B C : Type*}

/-- Adjacency in the glued pairing graph. -/
def glueAdj (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    ((A ⊕ B) ⊕ (B ⊕ C)) → ((A ⊕ B) ⊕ (B ⊕ C)) → Prop
  | .inl x, .inl y => a.link x y
  | .inr x, .inr y => b.link x y
  | .inl (.inr i), .inr (.inl j) => i = j
  | .inr (.inl j), .inl (.inr i) => i = j
  | _, _ => False

/-- Keep the two copies of the interface separate and join them by edges.
This subdivision avoids parallel edges without changing boundary paths. -/
def glueGraph (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) : SimpleGraph ((A ⊕ B) ⊕ (B ⊕ C)) where
  Adj := glueAdj a b
  symm := ⟨by
    intro v w h
    rcases v with (v | v) | (v | v) <;>
      rcases w with (w | w) | (w | w) <;>
      simp only [glueAdj] at h ⊢
    all_goals first | exact a.symm h | exact b.symm h | exact h⟩
  loopless := ⟨by
    intro v
    rcases v with (v | v) | (v | v) <;>
      simp only [glueAdj]
    all_goals first | exact a.irrefl _ | exact b.irrefl _⟩

/-- Embed the external ports into the disjoint union of two glued diagrams. -/
def outer : (A ⊕ C) ↪ ((A ⊕ B) ⊕ (B ⊕ C)) where
  toFun
    | .inl i => .inl (.inl i)
    | .inr i => .inr (.inr i)
  inj' := by
    intro v w h
    rcases v with v | v <;> rcases w with w | w <;> simp_all

noncomputable instance glueDec (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    DecidableRel (glueGraph a b).Adj := Classical.decRel _

variable [Fintype A] [Fintype B] [Fintype C] (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C))

lemma glue_degree_LL (i : A) : (glueGraph a b).degree (.inl (.inl i)) = 1 := by
  classical
  have hn : (glueGraph a b).neighborFinset (.inl (.inl i)) =
      {Sum.inl (a.mate (.inl i))} := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    change glueAdj a b _ w ↔ _
    rcases w with (w | w) | (w | w) <;>
      simp [glueAdj, link_iff, eq_comm]
  simp only [SimpleGraph.degree, hn, Finset.card_singleton]

lemma glue_degree_RR (i : C) : (glueGraph a b).degree (.inr (.inr i)) = 1 := by
  classical
  have hn : (glueGraph a b).neighborFinset (.inr (.inr i)) =
      {Sum.inr (b.mate (.inr i))} := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    change glueAdj a b _ w ↔ _
    rcases w with (w | w) | (w | w) <;>
      simp [glueAdj, link_iff, eq_comm]
  simp only [SimpleGraph.degree, hn, Finset.card_singleton]

lemma glue_degree_LR (i : B) : (glueGraph a b).degree (.inl (.inr i)) = 2 := by
  classical
  have hn : (glueGraph a b).neighborFinset (.inl (.inr i)) =
      {Sum.inl (a.mate (.inr i)), Sum.inr (Sum.inl i)} := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    change glueAdj a b _ w ↔ _
    rcases w with (w | w) | (w | w) <;>
      simp [glueAdj, link_iff, eq_comm]
  simp [SimpleGraph.degree, hn]

lemma glue_degree_RL (i : B) : (glueGraph a b).degree (.inr (.inl i)) = 2 := by
  classical
  have hn : (glueGraph a b).neighborFinset (.inr (.inl i)) =
      {Sum.inr (b.mate (.inl i)), Sum.inl (Sum.inr i)} := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    change glueAdj a b _ w ↔ _
    rcases w with (w | w) | (w | w) <;>
      simp [glueAdj, link_iff, eq_comm]
  simp [SimpleGraph.degree, hn]

lemma glue_degree_le_two (v) : (glueGraph a b).degree v ≤ 2 := by
  classical
  rcases v with (v | v) | (v | v)
  · simp [glue_degree_LL]
  · simp [glue_degree_LR]
  · simp [glue_degree_RL]
  · simp [glue_degree_RR]

lemma glue_boundary (v) : (glueGraph a b).degree v = 1 ↔ ∃ p, outer p = v := by
  classical
  rcases v with (v | v) | (v | v)
  · simp only [glue_degree_LL, true_iff]
    exact ⟨.inl v, rfl⟩
  · simp only [glue_degree_LR, OfNat.ofNat_ne_one, false_iff, not_exists]
    intro p
    cases p <;> intro h <;> cases h
  · simp only [glue_degree_RL, OfNat.ofNat_ne_one, false_iff, not_exists]
    intro p
    cases p <;> intro h <;> cases h
  · simp only [glue_degree_RR, true_iff]
    exact ⟨.inr v, rfl⟩

/-- Glue along the common interface and pair the surviving external ports. -/
noncomputable def compose : Pairing (A ⊕ C) := by
  classical
  exact FiniteWiring.boundaryPairing (glueGraph a b) outer
    (glue_degree_le_two a b) (glue_boundary a b)

/-- Boolean boundary behavior composes as ordinary relational composition. -/
lemma compose_compatible (f : A → Bool) (g : C → Bool) :
    (compose a b).Compatible (Sum.elim f g) ↔
      ∃ k : B → Bool, a.Compatible (Sum.elim f k) ∧ b.Compatible (Sum.elim k g) := by
  classical
  rw [compose, FiniteWiring.coloring_extension]
  constructor
  · rintro ⟨c, hc, he⟩
    let k : B → Bool := fun i => c (.inl (.inr i))
    have hk (i : B) : c (.inl (.inr i)) = c (.inr (.inl i)) :=
      he _ _ (show (glueGraph a b).Adj (.inl (.inr i)) (.inr (.inl i)) from rfl)
    have hl (i : A) : c (.inl (.inl i)) = f i := hc (.inl i)
    have hr (i : C) : c (.inr (.inr i)) = g i := hc (.inr i)
    refine ⟨k, ?_, ?_⟩
    · intro x y hxy
      have hh := he (.inl x) (.inl y) hxy
      rcases x with x | x <;> rcases y with y | y <;>
        simpa only [hl, Sum.elim_inl, Sum.elim_inr] using hh
    · intro x y hxy
      have hh := he (.inr x) (.inr y) hxy
      rcases x with x | x <;> rcases y with y | y <;>
        simpa only [← hk, hr, Sum.elim_inl, Sum.elim_inr] using hh
  · rintro ⟨k, hk₁, hk₂⟩
    refine ⟨Sum.elim (Sum.elim f k) (Sum.elim k g), ?_, ?_⟩
    · intro p; cases p <;> rfl
    · intro x y hxy
      rcases x with (x | x) | (x | x) <;>
        rcases y with (y | y) | (y | y) <;>
        simp only [glueGraph, glueAdj] at hxy
      all_goals first
        | exact hk₁ _ _ hxy
        | exact hk₂ _ _ hxy
        | exact congrArg k hxy
        | exact congrArg k hxy.symm

end Pairing


namespace Pairing
variable {P Q : Type*}

/-- The perfect matching given by a fixed-point-free involution. -/
def ofInvolution (f : P → P) (hf : Function.Involutive f) (hn : ∀ p, f p ≠ p) : Pairing P where
  link x y := f x = y
  symm {x y} h := by rw [← h, hf]
  irrefl x := hn x
  unique x := ⟨f x, rfl, fun _ h => h.symm⟩

/-- Rename the ports of a pairing along an equivalence. -/
def transport (a : Pairing P) (e : P ≃ Q) : Pairing Q where
  link x y := a.link (e.symm x) (e.symm y)
  symm := a.symm
  irrefl x := a.irrefl _
  unique x := by
    obtain ⟨y, hy, hu⟩ := a.unique (e.symm x)
    refine ⟨e y, ?_, ?_⟩
    · simpa using hy
    · intro z hz
      exact (e.symm.injective (by simpa using hu (e.symm z) hz))

variable {A B C D : Type*}

/-- A rectangular permutation diagram; arbitrary equivalences also allow
renumbering finite port sets without changing the underlying diagram. -/
def bijection (e : A ≃ B) : Pairing (A ⊕ B) :=
  ofInvolution (Sum.elim (Sum.inr ∘ e) (Sum.inl ∘ e.symm))
    (by intro x; cases x <;> simp) (by intro x; cases x <;> simp)

/-- The pairing that connects each left port to its equal right port. -/
def identity (A : Type*) : Pairing (A ⊕ A) := bijection (Equiv.refl A)

lemma bijection_compatible (e : A ≃ B) (f : A → Bool) (g : B → Bool) :
    (bijection e).Compatible (Sum.elim f g) ↔ ∀ x, f x = g (e x) := by
  constructor
  · intro h x
    exact h (.inl x) (.inr (e x)) rfl
  · intro h x y hxy
    rcases x with x | x <;> rcases y with y | y
    · cases hxy
    · change Sum.inr (e x) = Sum.inr y at hxy
      cases hxy
      exact h x
    · change Sum.inl (e.symm x) = Sum.inl y at hxy
      cases hxy
      simpa using (h (e.symm x)).symm
    · cases hxy

lemma identity_compatible (f g : A → Bool) :
    (identity A).Compatible (Sum.elim f g) ↔ f = g := by
  rw [identity, bijection_compatible]
  exact funext_iff.symm

lemma ext_colors {a b : Pairing (A ⊕ B)}
    (h : ∀ f : A → Bool, ∀ g : B → Bool,
      a.Compatible (Sum.elim f g) ↔ b.Compatible (Sum.elim f g)) : a = b := by
  apply a.eq_of_compatible
  intro c
  have hc : Sum.elim (fun i => c (.inl i)) (fun i => c (.inr i)) = c := by
    funext p; cases p <;> rfl
  simpa only [hc] using h (fun i => c (.inl i)) (fun i => c (.inr i))

/-- The Boolean equality semantics is faithful even for a single pair. -/
lemma connected_of_color_eq (a : Pairing P) (x y : P)
    (h : ∀ c : P → Bool, a.Compatible c → c x = c y) : a.connected x y := by
  have he := h (a.testColor x) (a.compatible_testColor x)
  rw [testColor_self] at he
  simpa only [testColor, decide_eq_true_eq] using he.symm

lemma link_of_color_eq (a : Pairing P) {x y : P} (hne : x ≠ y)
    (h : ∀ c : P → Bool, a.Compatible c → c x = c y) : a.link x y :=
  (a.connected_of_color_eq x y h).resolve_left hne

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

lemma compose_assoc (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C))
    (c : Pairing (C ⊕ D)) : compose (compose a b) c = compose a (compose b c) := by
  apply ext_colors
  intro f g
  simp only [compose_compatible]
  aesop

lemma identity_compose (a : Pairing (A ⊕ B)) : compose (identity A) a = a := by
  apply ext_colors
  intro f g
  simp [compose_compatible, identity_compatible]

lemma compose_identity (a : Pairing (A ⊕ B)) : compose a (identity B) = a := by
  apply ext_colors
  intro f g
  simp [compose_compatible, identity_compatible]

end Pairing

end Complexity.FiniteAutomaton
