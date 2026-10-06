/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Concentrator.Internal

/-!
# Proofs for acyclic concentrators

Let `G` be an acyclic `(n, m)`-concentrator whose inputs are sources (in-degree zero), with
`2 ≤ m < n`.

* **Elimination** (`exists_eliminate`). Removing at least two edges, `G` turns into an acyclic
  `(n - 1, m)`-concentrator on the same vertices, with sources as inputs. Every input has an edge
  leaving it. If some input has two, remove its edges and drop it: the other walks never visit a
  source. Otherwise every input `x` has one edge, to its *head*, and distinct inputs have distinct
  heads, since two inputs with a common head cannot be routed together. If some head `u` of `x`
  is entered by that edge only, remove it and make `u` an input in place of `x`: `u` is neither an
  input nor an output, as every output is reached from inputs other than `x`. Otherwise let `w` be
  a first vertex, in the topological order, among the non-input vertices that meet an edge. The
  edges entering `w` come from inputs whose head is `w`, so there is at most one, and then `w`
  would be a head entered only by it; so no edge enters `w`. Then `w` is no output, and its edges
  can be removed. The last two steps keep `n` and remove an edge, so induction on the number of
  edges applies.
* Eliminating `n - 2 m` inputs leaves a `(2 m, m)`-concentrator with at least `2 (n - 2 m)` fewer
  edges, and the concentrator bound applies to it. For `h = min(m, n - m)` this gives
  `h ≤ (A + η) (M - 2 n + h)⁺ + 3 log₂ (2 M) + C` and the baseline `M ≥ 2 n - h - 1`.
-/

@[expose] public section

open scoped Classical

namespace Algebraic.Cutwidth.Concentrator.Internal

open Multigraph Relation Filter Superconcentrator.Internal

variable {V E : Type} {G : Multigraph V E}

/-! ### Removing the edges at a vertex -/

/-- The multigraph with the edges at `x` removed. -/
def removeEdgesAt (G : Multigraph V E) (x : V) :
    Multigraph V {e : E // G.fst e ≠ x ∧ G.snd e ≠ x} where
  fst e := G.fst e.1
  snd e := G.snd e.1

/-- Walks avoiding `x` survive the removal of the edges at `x`. -/
theorem isDirWalk_removeEdgesAt {x : V} {p : List V} {u v : V} (hp : G.IsDirWalk p u v)
    (hx : ∀ z ∈ p, z ≠ x) : (removeEdgesAt G x).IsDirWalk p u v := by
  refine ⟨hp.1, hp.2.1, hp.2.2.imp_of_mem_imp fun a b ha hb ⟨e, he₁, he₂⟩ => ?_⟩
  exact ⟨⟨e, he₁ ▸ hx a ha, he₂ ▸ hx b hb⟩, he₁, he₂⟩

/-- Removing edges does not increase in-degrees. -/
theorem inDegree_removeEdgesAt_le [Fintype E] (x v : V) :
    (removeEdgesAt G x).inDegree v ≤ G.inDegree v := by
  unfold inDegree
  exact Finset.card_le_card_of_injOn Subtype.val
    (fun e he => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he ⊢
      exact he) Subtype.val_injective.injOn

/-- Removing edges keeps a multigraph acyclic. -/
theorem acyclic_removeEdgesAt (hG : G.Acyclic) (x : V) : (removeEdgesAt G x).Acyclic := by
  obtain ⟨rank, hrank⟩ := hG
  exact ⟨rank, fun e => hrank e.1⟩

/-- The edges kept and the edges at `x` partition the edges. -/
theorem card_removeEdgesAt_add [Fintype E] (x : V) :
    Fintype.card {e : E // G.fst e ≠ x ∧ G.snd e ≠ x} +
      (Finset.univ.filter fun e => ¬ (G.fst e ≠ x ∧ G.snd e ≠ x)).card = Fintype.card E := by
  rw [Fintype.card_subtype, Finset.card_filter_add_card_filter_not, Finset.card_univ]

/-! ### Walks and sources -/

/-- Every vertex of a chain after its first is entered by an edge. -/
theorem exists_dirAdj_of_mem_tail :
    ∀ {u : V} {l : List V}, (u :: l).IsChain G.DirAdj → ∀ z ∈ l, ∃ y, G.DirAdj y z
  | _, [], _, z, hz => by simp at hz
  | u, w :: l, hc, z, hz => by
    rw [List.isChain_cons_cons] at hc
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨u, hc.1⟩
    · exact exists_dirAdj_of_mem_tail hc.2 z hz

/-- A vertex entered by an edge has positive in-degree. -/
theorem inDegree_pos_of_dirAdj [Fintype E] {y z : V} (h : G.DirAdj y z) : 0 < G.inDegree z := by
  obtain ⟨e, -, he⟩ := h
  exact Finset.card_pos.2 ⟨e, by simp [he]⟩

/-- **Walks avoid sources.** A directed walk visits a vertex of in-degree zero only at its
start. -/
theorem not_mem_of_inDegree_eq_zero [Fintype E] {p : List V} {u v x : V}
    (hp : G.IsDirWalk p u v) (hx : G.inDegree x = 0) (hux : u ≠ x) : x ∉ p := by
  obtain ⟨l, rfl, hc, -⟩ := exists_eq_cons_of_isDirWalk hp
  intro hmem
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact hux rfl
  · obtain ⟨y, hy⟩ := exists_dirAdj_of_mem_tail hc x hmem
    have := inDegree_pos_of_dirAdj hy
    omega

/-- A directed walk from a vertex of in-degree zero to another vertex continues along an edge
leaving it, and the rest of the walk avoids it. -/
theorem exists_tail_of_isDirWalk [Fintype E] {p : List V} {x v : V} (hp : G.IsDirWalk p x v)
    (hx : G.inDegree x = 0) (hxv : x ≠ v) :
    ∃ e q, G.fst e = x ∧ G.IsDirWalk q (G.snd e) v ∧ (∀ z ∈ q, z ∈ p) ∧ x ∉ q := by
  obtain ⟨l, rfl, hc, hlast⟩ := exists_eq_cons_of_isDirWalk hp
  rcases l with _ | ⟨w, l⟩
  · exact absurd hlast hxv
  rw [List.isChain_cons_cons] at hc
  obtain ⟨⟨e, he₁, he₂⟩, hc⟩ := hc
  subst he₂
  rw [List.getLast_cons_cons] at hlast
  refine ⟨e, G.snd e :: l, he₁, hlast ▸ isDirWalk_of_isChain hc,
    fun z hz => List.mem_cons_of_mem _ hz, fun hmem => ?_⟩
  rcases List.mem_cons.1 hmem with hw | hmem
  · have : 0 < G.inDegree x := inDegree_pos_of_dirAdj (y := x) ⟨e, he₁, hw.symm⟩
    omega
  · obtain ⟨y, hy⟩ := exists_dirAdj_of_mem_tail hc x hmem
    have := inDegree_pos_of_dirAdj hy
    omega

/-! ### The three elimination steps -/

section Steps

variable [Fintype E] {n m : ℕ} {output : Fin m → V}

/-- Removing the edges at a vertex keeps the inputs sources. -/
theorem inDegree_removeEdgesAt_eq_zero {x v : V} (hv : G.inDegree v = 0) :
    (removeEdgesAt G x).inDegree v = 0 :=
  Nat.eq_zero_of_le_zero ((inDegree_removeEdgesAt_le x v).trans hv.le)

/-- **Dropping an input.** Removing the edges at a source input leaves a concentrator on the
other inputs. -/
theorem concentrator_drop {input : Fin (n + 1) → V} (h : G.Concentrator input output)
    (hsrc : ∀ i, G.inDegree (input i) = 0) (i₀ : Fin (n + 1)) :
    (removeEdgesAt G (input i₀)).Concentrator (fun j => input (i₀.succAbove j)) output where
  input_injective := h.input_injective.comp Fin.succAbove_right_injective
  output_injective := h.output_injective
  input_ne_output _ _ := h.input_ne_output _ _
  exists_walks X hX := by
    obtain ⟨target, walk, hwalk, hdisj⟩ :=
      h.exists_walks (X.map ⟨i₀.succAbove, Fin.succAbove_right_injective⟩)
        (by rw [Finset.card_map]; exact hX)
    have hmem : ∀ j ∈ X, i₀.succAbove j ∈ X.map ⟨i₀.succAbove, Fin.succAbove_right_injective⟩ :=
      fun j hj => Finset.mem_map_of_mem _ hj
    refine ⟨fun j => target (i₀.succAbove j), fun j => walk (i₀.succAbove j),
      fun j hj => ?_, fun j hj j' hj' hjj' => ?_⟩
    · have hp := hwalk _ (hmem j hj)
      have hnot := not_mem_of_inDegree_eq_zero hp (hsrc i₀)
        (h.input_injective.ne (Fin.succAbove_ne i₀ j))
      exact isDirWalk_removeEdgesAt hp fun z hz hzx => hnot (hzx ▸ hz)
    · exact hdisj _ (hmem j hj) _ (hmem j' hj')
        (Fin.succAbove_right_injective.ne hjj')

/-- **Contracting an input into its head.** Let the input `input i₀` be a source whose only
edge `e₀` leads to a vertex `u` entered by no other edge, and let every other input be a
source. Removing `e₀` and making `u` an input in place of `input i₀` leaves a concentrator,
provided `m` inputs other than `input i₀` exist. -/
theorem concentrator_contract {input : Fin (n + 1) → V} (h : G.Concentrator input output)
    (hsrc : ∀ i, G.inDegree (input i) = 0) (hmn : m ≤ n) {i₀ : Fin (n + 1)} {e₀ : E}
    (he₀ : G.fst e₀ = input i₀) (hout : ∀ e, G.fst e = input i₀ → e = e₀)
    (hin : ∀ e, G.snd e = G.snd e₀ → e = e₀) :
    (removeEdgesAt G (input i₀)).Concentrator (Function.update input i₀ (G.snd e₀)) output ∧
      ∀ i, (removeEdgesAt G (input i₀)).inDegree (Function.update input i₀ (G.snd e₀) i) = 0 := by
  set u := G.snd e₀ with hu
  have hupos : 0 < G.inDegree u := inDegree_pos_of_dirAdj ⟨e₀, rfl, rfl⟩
  have hu_input : ∀ i, input i ≠ u := fun i hi => by
    have := hsrc i
    rw [hi] at this
    omega
  -- `u` is no output: the outputs are reached from inputs other than `input i₀`
  have hu_output : ∀ j, u ≠ output j := by
    intro j hj
    obtain ⟨X, hXsub, hXcard⟩ := Finset.exists_subset_card_eq
      (s := Finset.univ.erase i₀) (n := m)
      (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]; omega)
    obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X hXcard.le
    obtain ⟨i, hi, hij⟩ := exists_target_eq_of_walks hwalk hdisj (Y := Finset.univ)
      (fun _ _ => Finset.mem_univ _) (by simp [hXcard]) (Finset.mem_univ j)
    have hp := hwalk i hi
    rw [hij, ← hj] at hp
    obtain ⟨e, hep, -, he⟩ := exists_cross_of_isDirWalk hp (L := {z | z ≠ u}) (hu_input i)
      (by simp)
    have he' : G.snd e = u := by simpa using he
    have := hin e he'
    subst this
    have hii₀ : i ≠ i₀ := Finset.ne_of_mem_erase (hXsub hi)
    exact not_mem_of_inDegree_eq_zero hp (hsrc i₀) (h.input_injective.ne hii₀) (he₀ ▸ hep)
  have hinj : Function.Injective (Function.update input i₀ u) := by
    intro a b hab
    by_cases ha : a = i₀ <;> by_cases hb : b = i₀
    · rw [ha, hb]
    · subst ha
      rw [Function.update_self, Function.update_of_ne hb] at hab
      exact absurd hab.symm (hu_input b)
    · subst hb
      rw [Function.update_self, Function.update_of_ne ha] at hab
      exact absurd hab (hu_input a)
    · rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab
      exact h.input_injective hab
  refine ⟨⟨hinj, h.output_injective, fun i j => ?_, fun X hX => ?_⟩, fun i => ?_⟩
  · by_cases hi : i = i₀
    · subst hi
      rw [Function.update_self]
      exact hu_output j
    · rw [Function.update_of_ne hi]
      exact h.input_ne_output i j
  · obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X hX
    -- the walk from `input i₀` continues from `u`
    have htail : ∀ i ∈ X, i = i₀ → ∃ q, G.IsDirWalk q u (output (target i)) ∧
        (∀ z ∈ q, z ∈ walk i) ∧ input i₀ ∉ q := by
      rintro i hi rfl
      obtain ⟨e, q, he, hq, hqsub, hqx⟩ := exists_tail_of_isDirWalk (hwalk i hi) (hsrc i)
        (h.input_ne_output _ _)
      rw [hout e he] at hq
      exact ⟨q, hq, hqsub, hqx⟩
    choose! q hq using htail
    refine ⟨target, fun i => if i = i₀ then q i else walk i, fun i hi => ?_,
      fun i hi j hj hij => ?_⟩
    · by_cases hii₀ : i = i₀
      · obtain ⟨hqw, -, hqx⟩ := hq i hi hii₀
        simp only [hii₀, ite_true]
        subst hii₀
        rw [Function.update_self]
        exact isDirWalk_removeEdgesAt hqw fun z hz hzx => hqx (hzx ▸ hz)
      · simp only [hii₀, ite_false]
        rw [Function.update_of_ne hii₀]
        have hp := hwalk i hi
        have hnot := not_mem_of_inDegree_eq_zero hp (hsrc i₀) (h.input_injective.ne hii₀)
        exact isDirWalk_removeEdgesAt hp fun z hz hzx => hnot (hzx ▸ hz)
    · have hsub : ∀ k ∈ X, ∀ z ∈ (if k = i₀ then q k else walk k), z ∈ walk k := by
        intro k hk z hz
        by_cases hk₀ : k = i₀
        · simp only [hk₀, ite_true] at hz
          exact (hq k hk hk₀).2.1 z (hk₀ ▸ hz)
        · simpa only [hk₀, ite_false] using hz
      exact fun z hzi hzj => hdisj i hi j hj hij (hsub i hi z hzi) (hsub j hj z hzj)
  · by_cases hi : i = i₀
    · subst hi
      rw [Function.update_self]
      unfold inDegree
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      have : e.1 = e₀ := hin e.1 he
      exact e.2.1 (this ▸ he₀)
    · rw [Function.update_of_ne hi]
      exact inDegree_removeEdgesAt_eq_zero (hsrc i)

/-- **Removing a dead vertex.** Removing the edges at a non-input vertex entered by no edge
leaves a concentrator with the same inputs and outputs. -/
theorem concentrator_removeDead {input : Fin n → V} (h : G.Concentrator input output) {w : V}
    (hw : G.inDegree w = 0) (hwin : ∀ i, input i ≠ w) :
    (removeEdgesAt G w).Concentrator input output where
  input_injective := h.input_injective
  output_injective := h.output_injective
  input_ne_output := h.input_ne_output
  exists_walks X hX := by
    obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X hX
    refine ⟨target, walk, fun i hi => ?_, hdisj⟩
    have hnot := not_mem_of_inDegree_eq_zero (hwalk i hi) hw (hwin i)
    exact isDirWalk_removeEdgesAt (hwalk i hi) fun z hz hzx => hnot (hzx ▸ hz)

end Steps

/-! ### Elimination -/

/-- The head of the only edge leaving a source lies on every walk from it to another vertex. -/
theorem snd_mem_of_isDirWalk [Fintype E] {p : List V} {x v : V} {e : E}
    (hp : G.IsDirWalk p x v) (hx : G.inDegree x = 0) (hxv : x ≠ v)
    (huniq : ∀ e', G.fst e' = x → e' = e) : G.snd e ∈ p := by
  obtain ⟨e', q, he', hq, hqsub, -⟩ := exists_tail_of_isDirWalk hp hx hxv
  rw [huniq e' he'] at hq
  exact hqsub _ (mem_of_isDirWalk_left hq)

/-- An edge leaves a source input that reaches an output. -/
theorem exists_fst_eq_input [Fintype E] {n m : ℕ} {input : Fin n → V} {output : Fin m → V}
    (h : G.Concentrator input output) (hsrc : ∀ i, G.inDegree (input i) = 0) (hm : 1 ≤ m)
    (i : Fin n) : ∃ e, G.fst e = input i := by
  obtain ⟨target, walk, hwalk, -⟩ := h.exists_walks {i} (by simpa using hm)
  obtain ⟨e, -, he, -, -⟩ := exists_tail_of_isDirWalk (hwalk i (Finset.mem_singleton_self i))
    (hsrc i) (h.input_ne_output _ _)
  exact ⟨e, he⟩

/-- **Elimination.** An acyclic `(n + 1, m)`-concentrator whose inputs are sources, with
`2 ≤ m ≤ n`, turns into an acyclic `(n, m)`-concentrator on the same vertices and outputs, whose
inputs are sources, with at least two fewer edges. -/
theorem exists_eliminate {m : ℕ} {output : Fin m → V} (hm : 2 ≤ m) :
    ∀ (k : ℕ) {E : Type} [Fintype E] (G : Multigraph V E) {n : ℕ} (input : Fin (n + 1) → V),
      Fintype.card E ≤ k → G.Concentrator input output → G.Acyclic →
        (∀ i, G.inDegree (input i) = 0) → m ≤ n →
          ∃ (E' : Type) (_ : Fintype E') (G' : Multigraph V E') (input' : Fin n → V),
            G'.Concentrator input' output ∧ G'.Acyclic ∧ (∀ i, G'.inDegree (input' i) = 0) ∧
              Fintype.card E' + 2 ≤ Fintype.card E := by
  intro k
  induction k with
  | zero =>
    intro E _ G n input hk h _ hsrc _
    obtain ⟨e, -⟩ := exists_fst_eq_input h hsrc (by omega) 0
    have : 0 < Fintype.card E := Fintype.card_pos_iff.2 ⟨e⟩
    omega
  | succ k ih =>
    intro E _ G n input hk h hacyc hsrc hmn
    -- an input with two edges is dropped
    by_cases hA : ∃ i e₁ e₂, e₁ ≠ e₂ ∧ G.fst e₁ = input i ∧ G.fst e₂ = input i
    · obtain ⟨i₀, e₁, e₂, hne, he₁, he₂⟩ := hA
      refine ⟨_, inferInstance, removeEdgesAt G (input i₀), fun j => input (i₀.succAbove j),
        concentrator_drop h hsrc i₀, acyclic_removeEdgesAt hacyc _,
        fun j => inDegree_removeEdgesAt_eq_zero (hsrc _), ?_⟩
      have hcard := card_removeEdgesAt_add (G := G) (input i₀)
      have h2 : 1 < (Finset.univ.filter
          fun e => ¬ (G.fst e ≠ input i₀ ∧ G.snd e ≠ input i₀)).card :=
        Finset.one_lt_card.2 ⟨e₁, by simp [he₁], e₂, by simp [he₂], hne⟩
      omega
    have hout : ∀ i e e', G.fst e = input i → G.fst e' = input i → e = e' :=
      fun i e e' he he' => by
        by_contra hne
        exact hA ⟨i, e, e', hne, he, he'⟩
    -- an input whose head is entered by its edge only is contracted into the head
    by_cases hB : ∃ i e₀, G.fst e₀ = input i ∧ ∀ e, G.snd e = G.snd e₀ → e = e₀
    · obtain ⟨i₀, e₀, he₀, hin⟩ := hB
      obtain ⟨hconc, hsrc'⟩ := concentrator_contract h hsrc hmn he₀
        (fun e he => hout i₀ e e₀ he he₀) hin
      have hcard := card_removeEdgesAt_add (G := G) (input i₀)
      have h1 : 0 < (Finset.univ.filter
          fun e => ¬ (G.fst e ≠ input i₀ ∧ G.snd e ≠ input i₀)).card :=
        Finset.card_pos.2 ⟨e₀, by simp [he₀]⟩
      obtain ⟨E', _, G', input', hconc', hacyc', hsrc'', hcard'⟩ :=
        ih (removeEdgesAt G (input i₀)) (Function.update input i₀ (G.snd e₀)) (by omega) hconc
          (acyclic_removeEdgesAt hacyc _) hsrc' hmn
      exact ⟨E', inferInstance, G', input', hconc', hacyc', hsrc'', by omega⟩
    have hB' : ∀ i e₀, G.fst e₀ = input i → ∃ e, G.snd e = G.snd e₀ ∧ e ≠ e₀ :=
      fun i e₀ he₀ => by
        by_contra hcon
        push Not at hcon
        exact hB ⟨i, e₀, he₀, hcon⟩
    -- otherwise a first non-input vertex at an edge is dead
    obtain ⟨rank, hrank⟩ := hacyc
    set S := (Finset.univ.image G.fst ∪ Finset.univ.image G.snd).filter
      fun v => ∀ i, input i ≠ v with hSdef
    have hS : S.Nonempty := by
      obtain ⟨e, he⟩ := exists_fst_eq_input h hsrc (by omega) 0
      refine ⟨G.snd e, Finset.mem_filter.2 ⟨Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ e)), fun i hi => ?_⟩⟩
      have := inDegree_pos_of_dirAdj (G := G) ⟨e, rfl, hi.symm⟩
      have := hsrc i
      omega
    obtain ⟨w, hwS, hwmin⟩ := S.exists_min_image rank hS
    have hwin : ∀ i, input i ≠ w := (Finset.mem_filter.1 hwS).2
    have hfrom : ∀ e, G.snd e = w → ∃ i, G.fst e = input i := by
      intro e he
      by_contra hne
      push Not at hne
      have hmem : G.fst e ∈ S := Finset.mem_filter.2 ⟨Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ e)), fun i hi => hne i hi.symm⟩
      have h₁ := hwmin _ hmem
      have h₂ := hrank e
      rw [he] at h₂
      omega
    have hw0 : G.inDegree w = 0 := by
      unfold inDegree
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      obtain ⟨i, hi⟩ := hfrom e he
      obtain ⟨e', he', hne⟩ := hB' i e hi
      obtain ⟨i', hi'⟩ := hfrom e' (he'.trans he)
      by_cases hii' : i = i'
      · subst hii'
        exact hne (hout i e' e hi' hi)
      · -- two inputs share the head `w`, so they cannot be routed together
        obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks {i, i'}
          (by rw [Finset.card_pair hii']; exact hm)
        have hp := hwalk i (by simp)
        have hp' := hwalk i' (by simp)
        have hwi := snd_mem_of_isDirWalk hp (hsrc i) (h.input_ne_output _ _)
          fun e'' he'' => hout i e'' e he'' hi
        have hwi' := snd_mem_of_isDirWalk hp' (hsrc i') (h.input_ne_output _ _)
          fun e'' he'' => hout i' e'' e' he'' hi'
        rw [he] at hwi
        rw [he', he] at hwi'
        exact hdisj i (by simp) i' (by simp) hii' hwi hwi'
    have hwfst : ∃ e, G.fst e = w := by
      rcases Finset.mem_union.1 (Finset.mem_filter.1 hwS).1 with hw | hw
      · obtain ⟨e, -, he⟩ := Finset.mem_image.1 hw
        exact ⟨e, he⟩
      · obtain ⟨e, -, he⟩ := Finset.mem_image.1 hw
        have := inDegree_pos_of_dirAdj (G := G) ⟨e, rfl, he⟩
        omega
    obtain ⟨e₀, he₀⟩ := hwfst
    have hcard := card_removeEdgesAt_add (G := G) w
    have h1 : 0 < (Finset.univ.filter fun e => ¬ (G.fst e ≠ w ∧ G.snd e ≠ w)).card :=
      Finset.card_pos.2 ⟨e₀, by simp [he₀]⟩
    obtain ⟨E', _, G', input', hconc', hacyc', hsrc'', hcard'⟩ :=
      ih (removeEdgesAt G w) input (by omega) (concentrator_removeDead h hw0 hwin)
        (acyclic_removeEdgesAt ⟨rank, hrank⟩ _) (fun i => inDegree_removeEdgesAt_eq_zero (hsrc i))
        hmn
    exact ⟨E', inferInstance, G', input', hconc', hacyc', hsrc'', by omega⟩

/-- **Repeated elimination.** Eliminating `j` inputs from an acyclic `(n, m)`-concentrator whose
inputs are sources, with `2 ≤ m` and `m + j ≤ n`, removes at least `2 j` edges. -/
theorem exists_eliminate_iter {m : ℕ} {output : Fin m → V} (hm : 2 ≤ m) :
    ∀ (j : ℕ) {E : Type} [Fintype E] (G : Multigraph V E) {n : ℕ} (input : Fin n → V),
      m + j ≤ n → G.Concentrator input output → G.Acyclic →
        (∀ i, G.inDegree (input i) = 0) →
          ∃ (n' : ℕ) (E' : Type) (_ : Fintype E') (G' : Multigraph V E') (input' : Fin n' → V),
            n' + j = n ∧ G'.Concentrator input' output ∧ G'.Acyclic ∧
              (∀ i, G'.inDegree (input' i) = 0) ∧ Fintype.card E' + 2 * j ≤ Fintype.card E := by
  intro j
  induction j with
  | zero =>
    intro E _ G n input _ h hacyc hsrc
    exact ⟨n, E, inferInstance, G, input, rfl, h, hacyc, hsrc, le_rfl⟩
  | succ j ih =>
    intro E _ G n input hj h hacyc hsrc
    obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by omega⟩
    obtain ⟨E₁, _, G₁, input₁, h₁, hacyc₁, hsrc₁, hcard₁⟩ :=
      exists_eliminate hm _ G input le_rfl h hacyc hsrc (by omega)
    obtain ⟨n', E', _, G', input', hn', h', hacyc', hsrc', hcard'⟩ :=
      ih G₁ input₁ (by omega) h₁ hacyc₁ hsrc₁
    exact ⟨n', E', inferInstance, G', input', by omega, h', hacyc', hsrc', by omega⟩

/-! ### Acyclicity -/

/-- Ranks increase along directed walks of positive length. -/
theorem rank_lt_of_transGen {rank : V → ℕ} (hrank : ∀ e, rank (G.fst e) < rank (G.snd e))
    {u v : V} (h : TransGen G.DirAdj u v) : rank u < rank v := by
  induction h with
  | single huv =>
    obtain ⟨e, rfl, rfl⟩ := huv
    exact hrank e
  | tail _ hbc ih =>
    obtain ⟨e, rfl, rfl⟩ := hbc
    exact ih.trans (hrank e)

/-- **Acyclicity is the absence of directed cycles.** A finite multigraph has a vertex numbering
increasing along every edge exactly when no vertex reaches itself along a directed walk of
positive length. -/
theorem acyclic_iff_forall_not_transGen [Fintype V] :
    G.Acyclic ↔ ∀ v, ¬ TransGen G.DirAdj v v := by
  constructor
  · rintro ⟨rank, hrank⟩ v hv
    exact lt_irrefl _ (rank_lt_of_transGen hrank hv)
  · intro hcyc
    refine ⟨fun v => (Finset.univ.filter fun w => TransGen G.DirAdj w v).card, fun e => ?_⟩
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun w hw => ?_).2
      ⟨G.fst e, ?_, ?_⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw.tail ⟨e, rfl, rfl⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact .single ⟨e, rfl, rfl⟩
    · simpa using hcyc (G.fst e)

/-! ### Bounds -/

variable [Fintype V] [Fintype E] {n m : ℕ} {input : Fin n → V} {output : Fin m → V}

/-- **The edge baseline for acyclic concentrators.** For `h = min(m, n - m)`, an acyclic
`(n, m)`-concentrator with `M` edges whose inputs are sources, with `2 ≤ m < n`, has
`2 n ≤ M + h + 1`. -/
theorem two_mul_le_card_add_min_of_acyclic (h : G.Concentrator input output)
    (hacyc : G.Acyclic) (hsrc : ∀ i, G.inDegree (input i) = 0) (hm : 2 ≤ m) (hmn : m < n) :
    2 * n ≤ Fintype.card E + min m (n - m) + 1 := by
  by_cases hcase : n ≤ 2 * m
  · have := add_le_card_add_one h (by omega) hmn
    omega
  · obtain ⟨n', E', _, G', input', hn', h', -, -, hcard'⟩ :=
      exists_eliminate_iter hm (n - 2 * m) G input (by omega) h hacyc hsrc
    have := add_le_card_add_one h' (by omega) (by omega)
    omega

/-- **The finite bound for acyclic concentrators.** For `h = min(m, n - m)`, an acyclic
`(n, m)`-concentrator with `M` edges whose inputs are sources, with `2 ≤ m < n`, satisfies
`h ≤ (A + η) (M - (2 n - h))⁺ + 3 log₂ (2 M) + C`. -/
theorem le_of_orderingBound_of_acyclic {A η C : ℝ} (hord : OrderingBound A η C)
    (hAη : 0 ≤ A + η) (h : G.Concentrator input output) (hacyc : G.Acyclic)
    (hsrc : ∀ i, G.inDegree (input i) = 0) (hm : 2 ≤ m) (hmn : m < n) :
    ((min m (n - m) : ℕ) : ℝ) ≤ (A + η) * max ((Fintype.card E : ℝ) -
        (2 * n - ((min m (n - m) : ℕ) : ℝ))) 0 + 3 * Real.logb 2 (2 * Fintype.card E) + C := by
  by_cases hcase : n ≤ 2 * m
  · -- no elimination is needed
    have hmin : min m (n - m) = n - m := min_eq_right (by omega)
    have hb := le_of_orderingBound hord hAη h (by omega) hmn
    rw [hmin] at hb ⊢
    have e : (2 * (n : ℝ) - ((n - m : ℕ) : ℝ)) = n + m := by
      rw [Nat.cast_sub hmn.le]
      ring
    rwa [e]
  · -- eliminate down to `2 m` inputs
    have hmin : min m (n - m) = m := min_eq_left (by omega)
    obtain ⟨n', E', _, G', input', hn', h', -, -, hcard'⟩ :=
      exists_eliminate_iter hm (n - 2 * m) G input (by omega) h hacyc hsrc
    have hn'' : n' = 2 * m := by omega
    subst hn''
    have hb := le_of_orderingBound hord hAη h' (by omega) (by omega)
    have hbase := add_le_card_add_one h' (by omega) (by omega)
    rw [hmin]
    rw [show min m (2 * m - m) = m by omega] at hb
    have hE' : (Fintype.card E' : ℝ) + 2 * ((n - 2 * m : ℕ) : ℝ) ≤ Fintype.card E := by
      exact_mod_cast hcard'
    have hsub : ((n - 2 * m : ℕ) : ℝ) = n - 2 * m := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hsub] at hE'
    have hE'pos : (0 : ℝ) < Fintype.card E' := by
      have : 0 < Fintype.card E' := by omega
      exact_mod_cast this
    have hmax : max ((Fintype.card E' : ℝ) - ((2 * m : ℕ) + m)) 0 ≤
        max ((Fintype.card E : ℝ) - (2 * n - m)) 0 := by
      refine max_le_max ?_ le_rfl
      push_cast
      linarith
    have hlog : Real.logb 2 (2 * Fintype.card E') ≤ Real.logb 2 (2 * Fintype.card E) :=
      Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
    have := mul_le_mul_of_nonneg_left hmax hAη
    linarith

omit [Fintype V] [Fintype E] in
/-- **The asymptotic edge bound for acyclic concentrators**, for a general ordering
coefficient. -/
theorem eventually_le_card_edges_of_acyclic_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 2 ≤ m → m < n → ∀ (V E : Type) [Fintype V] [Fintype E]
      (G : Multigraph V E) (input : Fin n → V) (output : Fin m → V),
        G.Concentrator input output → G.Acyclic → (∀ i, G.inDegree (input i) = 0) →
          2 * (n : ℝ) + (1 / A - 1) * ((min m (n - m) : ℕ) : ℝ) - ε * n ≤ Fintype.card E := by
  obtain ⟨C, hC⟩ := hord (A ^ 2 * ε / 2) (by positivity)
  filter_upwards [eventually_le_of_bound_of_baseline hA hε (D := 2) (B := 2) (by norm_num)
    (by norm_num) C] with n hn
  intro m hm hmn V E _ _ G input output h hacyc hsrc
  have hb := le_of_orderingBound_of_acyclic hC (by positivity) h hacyc hsrc hm hmn
  have hbase := two_mul_le_card_add_min_of_acyclic h hacyc hsrc hm hmn
  have hmin : min m (n - m) ≤ n := by omega
  have hminR : ((min m (n - m) : ℕ) : ℝ) ≤ n := by exact_mod_cast hmin
  have key := hn _ _ _ (by positivity) hminR (by
      have : (0 : ℝ) ≤ ((min m (n - m) : ℕ) : ℝ) := by positivity
      linarith)
    (by
      have : ((2 * n : ℕ) : ℝ) ≤ ((Fintype.card E + min m (n - m) + 1 : ℕ) : ℝ) := by
        exact_mod_cast hbase
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at this
      linarith) (by positivity) hb
  have e : 2 * (n : ℝ) - ((min m (n - m) : ℕ) : ℝ) + ((min m (n - m) : ℕ) : ℝ) / A =
      2 * (n : ℝ) + (1 / A - 1) * ((min m (n - m) : ℕ) : ℝ) := by
    ring
  linarith

end Algebraic.Cutwidth.Concentrator.Internal
