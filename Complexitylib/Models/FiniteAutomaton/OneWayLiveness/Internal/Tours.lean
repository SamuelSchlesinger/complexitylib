/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Model

/-!
# One-way-liveness proof: Tours

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Tours.lean

Module and namespace names, imports, and formatting are adapted to complexitylib.
The machine definitions are shared through `Models.FiniteAutomaton.Defs`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

/-- A finite permutation cannot leave a set without later re-entering it.
When there is only one entrance, its entrance dart lies on the same tour. -/
lemma permutation_single_entrance {D : Type*} [Finite D] (τ : Equiv.Perm D)
    (U : Set D) (a b : D) (ha : a ∈ U) (ha' : τ a ∉ U)
    (hin : ∀ d, d ∉ U → τ d ∈ U → d = b) : τ.SameCycle a b := by
  classical
  by_contra hb
  let S : Set D := {d | τ.SameCycle a d ∧ d ∉ U}
  have hm : Set.MapsTo τ S S := by
    rintro d ⟨hd, hdu⟩
    refine ⟨by simpa using hd, ?_⟩
    intro hτd
    exact hb (hin d hdu hτd ▸ hd)
  have hbij := (Set.toFinite S).injOn_iff_bijOn_of_mapsTo hm |>.mp τ.injective.injOn
  obtain ⟨c, hc, he⟩ := hbij.surjOn ⟨by simpa using (Equiv.Perm.SameCycle.refl τ a), ha'⟩
  have hca : c = a := τ.injective he
  exact hc.2 (hca ▸ ha)

/-- A cyclic order on every nonempty fiber of a finite incidence map. -/
structure CyclicOrder {D V : Type*} (vertex : D → V) where
  /-- The permutation specifying the cyclic incidence order. -/
  perm : Equiv.Perm D
  vertex_eq : ∀ d, vertex (perm d) = vertex d
  cyclic : ∀ d d', vertex d = vertex d' → perm.SameCycle d d'

/-- Choose a single cycle on each nonempty finite incidence fiber. -/
noncomputable def CyclicOrder.choose {D V : Type*} [Fintype D] (vertex : D → V) :
    CyclicOrder vertex := by
  classical
  have hex (v : V) := (Finset.univ.filter fun d => vertex d = v).exists_cycleOn
  choose p hp _hps using hex
  have hpres (v : V) (d : D) (hd : vertex d = v) : vertex (p v d) = v := by
    have := (hp v).1.mapsTo (x := d) (by simpa using hd)
    simpa using this
  have hinv (v : V) (d : D) (hd : vertex d = v) : vertex ((p v).symm d) = v := by
    have := (hp v).1.perm_inv.mapsTo (x := d) (by simpa using hd)
    simpa using this
  let τ : Equiv.Perm D := {
    toFun d := p (vertex d) d
    invFun d := (p (vertex d)).symm d
    left_inv d := by simp only [hpres _ _ rfl]; exact (p (vertex d)).symm_apply_apply d
    right_inv d := by simp only [hinv _ _ rfl]; exact (p (vertex d)).apply_symm_apply d }
  refine ⟨τ, fun d => hpres _ _ rfl, ?_⟩
  intro d d' hdd'
  have hc : (p (vertex d)).SameCycle d d' :=
    (hp (vertex d)).2 (by simp) (by simpa using hdd'.symm)
  obtain ⟨n, hn⟩ := hc.exists_nat_pow_eq
  have hpow : ∀ n : ℕ, (τ ^ n) d = (p (vertex d) ^ n) d ∧ vertex ((τ ^ n) d) = vertex d := by
    intro n
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply]
      constructor
      · change p (vertex ((τ ^ n) d)) ((τ ^ n) d) = _
        rw [ih.2, ih.1]
      · exact (hpres _ _ rfl).trans ih.2
  exact ⟨n, by simpa only [zpow_natCast, (hpow n).1] using hn⟩

lemma sameCycle_permCongr {D D' : Type*} (e : D ≃ D') (τ : Equiv.Perm D)
    {d d' : D} (h : τ.SameCycle d d') : (e.permCongrHom τ).SameCycle (e d) (e d') := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← map_zpow]
  change e ((τ ^ n) (e.symm (e d))) = e d'
  simpa only [Equiv.symm_apply_apply] using congrArg e hn

/-- Oriented edges of a finite functional graph. Loops and distinct parallel
edges are permitted a priori; the source map nevertheless is injective. -/
structure FunctionalEdges (V E : Type*) where
  /-- The source vertex of an edge. -/
  src : E → V
  /-- The destination vertex of an edge. -/
  dst : E → V
  src_injective : Function.Injective src

namespace FunctionalEdges
variable {V E : Type*} (G : FunctionalEdges V E)
/-- A directed edge from one vertex to another. -/
def Step (v w : V) : Prop := ∃ e, G.src e = v ∧ G.dst e = w
/-- Reflexive transitive closure of the functional edge relation. -/
abbrev Reach := Relation.ReflTransGen G.Step
lemma deterministic {v w z : V} (h : G.Step v w) (h' : G.Step v z) : w = z := by
  obtain ⟨e, hs, hd⟩ := h
  obtain ⟨e', hs', hd'⟩ := h'
  have he : e = e' := G.src_injective (hs.trans hs'.symm)
  exact hd.symm.trans (he ▸ hd')

lemma reach_of_terminal {t v : V} (ht : ∀ e, G.src e ≠ t) (h : G.Reach t v) : t = v := by
  rcases h.cases_head with h | ⟨w, ⟨e, he, _⟩, _⟩
  · exact h
  · exact (ht e he).elim

lemma successor_reaches {t v w : V} (ht : ∀ e, G.src e ≠ t)
    (hv : G.Reach v t) (hvw : G.Step v w) : G.Reach w t := by
  rcases hv.cases_head with rfl | ⟨z, hvz, hzt⟩
  · obtain ⟨e, he, _⟩ := hvw
    exact (ht e he).elim
  · exact G.deterministic hvw hvz ▸ hzt

lemma edge_cut {e f : E} (hne : f ≠ e) :
    G.Reach (G.src f) (G.src e) ↔ G.Reach (G.dst f) (G.src e) := by
  constructor
  · intro h
    rcases h.cases_head with heq | ⟨v, hfv, hve⟩
    · exact (hne (G.src_injective heq)).elim
    · have heq : G.dst f = v := G.deterministic ⟨f, rfl, rfl⟩ hfv
      exact heq ▸ hve
  · exact fun h => h.head ⟨f, rfl, rfl⟩

lemma edge_not_return {t : V} (ht : ∀ e, G.src e ≠ t) (e : E)
    (h : G.Reach (G.src e) t) : ¬ G.Reach (G.dst e) (G.src e) := by
  intro he
  have closed {v w : V} (hv : G.Reach v (G.src e)) (hvw : G.Step v w) :
      G.Reach w (G.src e) := by
    rcases hv.cases_head with rfl | ⟨z, hvz, hze⟩
    · have this := G.deterministic hvw (show G.Step (G.src e) (G.dst e) from ⟨e, rfl, rfl⟩)
      simpa [this] using he
    · exact G.deterministic hvw hvz ▸ hze
  have hh : G.Reach t (G.src e) := by
    clear ht
    induction h with
    | refl => exact .refl
    | tail _ hvw ih => exact closed ih hvw
  exact ht e (G.reach_of_terminal ht hh).symm

/-- An edge together with its source or destination endpoint. -/
abbrev Dart := E × Bool

/-- The involution exchanging the two endpoints of each edge. -/
def flip (_G : FunctionalEdges V E) : Equiv.Perm (E × Bool) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv d := by simp
  right_inv d := by simp

/-- The vertex incident to the selected edge endpoint. -/
def vertex (d : E × Bool) : V := if d.2 then G.dst d.1 else G.src d.1

@[simp] lemma vertex_false (e : E) : G.vertex (e, false) = G.src e := rfl
@[simp] lemma vertex_true (e : E) : G.vertex (e, true) = G.dst e := rfl
@[simp] lemma flip_apply (d : E × Bool) : G.flip d = (d.1, !d.2) := rfl

/-- Every incoming-to-outgoing cyclic order at a vertex is permitted. -/
abbrev Rotation := CyclicOrder G.vertex

namespace Rotation
variable {G} (R : G.Rotation)
/-- Traverse an edge, then advance along its vertex rotation. -/
def tour : Equiv.Perm (E × Bool) := R.perm * G.flip

lemma tour_vertex (d : E × Bool) : G.vertex (R.tour d) = G.vertex (G.flip d) := R.vertex_eq _

lemma edge_sameCycle [Finite E] {t : V} (ht : ∀ e, G.src e ≠ t) (e : E)
    (h : G.Reach (G.src e) t) : R.tour.SameCycle (e, false) (e, true) := by
  let U : Set (E × Bool) := {d | G.Reach (G.vertex d) (G.src e)}
  have hae : (e, false) ∈ U := Relation.ReflTransGen.refl
  have hae' : R.tour (e, false) ∉ U := by
    change ¬ G.Reach (G.vertex (R.tour (e, false))) (G.src e)
    rw [R.tour_vertex]
    exact G.edge_not_return ht e h
  apply permutation_single_entrance R.tour U (e, false) (e, true) hae hae'
  rintro ⟨f, b⟩ ho hi
  change G.Reach (G.vertex (R.tour (f,b))) (G.src e) at hi
  rw [R.tour_vertex] at hi
  cases b with
  | false => exact (ho (hi.head ⟨f, rfl, rfl⟩)).elim
  | true =>
    have hfe : f = e := by
      by_contra hne
      exact ho ((G.edge_cut hne).mp hi)
    exact Prod.ext hfe rfl

lemma tour_flip (d : E × Bool) : R.tour (G.flip d) = R.perm d := by
  rcases d with ⟨e, b⟩
  simp [tour, flip]

lemma flip_sameCycle [Finite E] {t : V} (ht : ∀ e, G.src e ≠ t) (d : E × Bool)
    (hd : G.Reach (G.vertex d) t) : R.tour.SameCycle d (G.flip d) := by
  rcases d with ⟨e, b⟩
  cases b with
  | false => exact R.edge_sameCycle ht e hd
  | true => exact (R.edge_sameCycle ht e (hd.head ⟨e, rfl, rfl⟩)).symm

lemma perm_sameCycle [Finite E] {t : V} (ht : ∀ e, G.src e ≠ t) (d : E × Bool)
    (hd : G.Reach (G.vertex d) t) : R.tour.SameCycle d (R.perm d) := by
  simpa only [tour_flip] using (R.flip_sameCycle ht d hd).apply_right

lemma vertex_pow (n : ℕ) (d : E × Bool) : G.vertex ((R.perm ^ n) d) = G.vertex d := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply, R.vertex_eq] using ih

lemma vertex_sameCycle [Finite E] {t : V} (ht : ∀ e, G.src e ≠ t) (d d' : E × Bool)
    (hd : G.Reach (G.vertex d) t) (he : G.vertex d = G.vertex d') :
    R.tour.SameCycle d d' := by
  obtain ⟨n, rfl⟩ := (R.cyclic d d' he).exists_nat_pow_eq
  clear he
  induction n with
  | zero => exact .refl _ _
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (R.perm_sameCycle ht _ (by simpa only [R.vertex_pow] using hd))

lemma reach_sameCycle [Finite E] {t : V} (ht : ∀ e, G.src e ≠ t) (d d' : E × Bool)
    (h : G.Reach (G.vertex d) (G.vertex d')) (ht' : G.Reach (G.vertex d') t) :
    R.tour.SameCycle d d' := by
  have aux : ∀ v, G.Reach v (G.vertex d') → ∀ u : E × Bool,
      G.vertex u = v → R.tour.SameCycle u d' := by
    intro v hv
    induction hv using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro u hu
      exact R.vertex_sameCycle ht u d' (hu ▸ ht') hu
    | @head a b hab hbe ih =>
      intro u hu
      obtain ⟨e, hs, he⟩ := hab
      have hae : G.Reach (G.src e) t := hs ▸ (hbe.head ⟨e, hs, he⟩).trans ht'
      exact (R.vertex_sameCycle ht u (e, false) (hu ▸ hs ▸ hae) (hu.trans hs.symm)).trans
        ((R.edge_sameCycle ht e hae).trans (ih (e, true) he))
  exact aux _ h d rfl

/-- All incidences in the basin of a terminal vertex lie on its one tour. -/
lemma basin_sameCycle [Finite E] {t : V} (ht : ∀ e, G.src e ≠ t) (d d' r : E × Bool)
    (hd : G.Reach (G.vertex d) t) (hd' : G.Reach (G.vertex d') t)
    (hr : G.vertex r = t) : R.tour.SameCycle d d' := by
  exact (R.reach_sameCycle ht d r (hr ▸ hd) (hr ▸ .refl)).trans
    (R.reach_sameCycle ht d' r (hr ▸ hd') (hr ▸ .refl)).symm

lemma color_eq_of_sameCycle {D C : Type*} [Finite D] (τ : Equiv.Perm D)
    (color : D → C) (hc : ∀ d, color (τ d) = color d)
    {d d' : D} (h : τ.SameCycle d d') : color d = color d' := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply, hc] using ih

end Rotation
end FunctionalEdges
end Complexity.FiniteAutomaton
