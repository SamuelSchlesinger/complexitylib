/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Superconcentrator.Defs

/-!
# Every vertex ordering of a superconcentrator has a large prefix cut

Take a prefix `S` of the ordering containing exactly `N` of the `2 N` terminals, say `a`
inputs and `N - a` outputs. The complement contains `N - a` inputs and `a` outputs. The
superconcentrator joins the `a` inputs in `S` to the `a` outputs outside `S` by
vertex-disjoint walks, each of which leaves `S` along an edge directed out of `S`; it also
joins the `N - a` inputs outside `S` to the `N - a` outputs in `S`, each walk entering `S`
along an edge directed into `S`. Since the walks of one family are vertex-disjoint, their
crossing edges are distinct, so the cut of `S` has at least `N` edges.
-/

@[expose] public section

open scoped Classical

namespace Algebraic.Cutwidth.Superconcentrator.Internal

open Multigraph

variable {V E : Type} {G : Multigraph V E}

/-- A directed walk is a nonempty chain of directed adjacencies from its first to its last
vertex. -/
theorem exists_eq_cons_of_isDirWalk {p : List V} {u v : V} (h : G.IsDirWalk p u v) :
    ∃ l, p = u :: l ∧ (u :: l).IsChain G.DirAdj ∧
      (u :: l).getLast (List.cons_ne_nil u l) = v := by
  obtain ⟨hhead, hlast, hchain⟩ := h
  rcases p with _ | ⟨a, l⟩
  · simp at hhead
  · simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    refine ⟨l, rfl, hchain, ?_⟩
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a l)] at hlast
    exact Option.some.inj hlast

/-- A chain of vertices is a directed walk from its first to its last vertex. -/
theorem isDirWalk_of_isChain {u : V} {l : List V} (h : (u :: l).IsChain G.DirAdj) :
    G.IsDirWalk (u :: l) u ((u :: l).getLast (List.cons_ne_nil u l)) :=
  ⟨rfl, List.getLast?_eq_some_getLast _, h⟩

/-- A chain of directed adjacencies that starts in `L` and ends outside `L` leaves `L` along
some step. -/
theorem exists_cross_of_isChain {L : Set V} :
    ∀ (u : V) (l : List V), (u :: l).IsChain G.DirAdj → u ∈ L →
      (u :: l).getLast (List.cons_ne_nil u l) ∉ L →
        ∃ x ∈ u :: l, ∃ y, x ∈ L ∧ y ∉ L ∧ G.DirAdj x y
  | u, [], _, hu, hv => absurd hu (by simpa using hv)
  | u, w :: l, hc, hu, hv => by
    rw [List.isChain_cons_cons] at hc
    by_cases hw : w ∈ L
    · obtain ⟨x, hx, y, hxL, hyL, hxy⟩ :=
        exists_cross_of_isChain w l hc.2 hw (by simpa [List.getLast_cons_cons] using hv)
      exact ⟨x, List.mem_cons_of_mem _ hx, y, hxL, hyL, hxy⟩
    · exact ⟨u, List.mem_cons_self, w, hu, hw, hc.1⟩

/-- A directed walk from inside `L` to outside `L` uses an edge directed out of `L` whose
first endpoint lies on the walk. -/
theorem exists_cross_of_isDirWalk {p : List V} {u v : V} (h : G.IsDirWalk p u v) {L : Set V}
    (hu : u ∈ L) (hv : v ∉ L) : ∃ e, G.fst e ∈ p ∧ G.fst e ∈ L ∧ G.snd e ∉ L := by
  obtain ⟨l, rfl, hchain, hlast⟩ := exists_eq_cons_of_isDirWalk h
  obtain ⟨x, hx, y, hxL, hyL, e, rfl, rfl⟩ :=
    exists_cross_of_isChain u l hchain hu (hlast ▸ hv)
  exact ⟨e, hx, hxL, hyL⟩

/-- The edges directed from `L` to its complement. -/
noncomputable def outCut [Fintype E] (G : Multigraph V E) (L : Set V) : Finset E :=
  Finset.univ.filter fun e => G.fst e ∈ L ∧ G.snd e ∉ L

/-- The edges directed out of `L` and those directed into `L` together lie in its cut. -/
theorem card_outCut_add_card_outCut_compl_le [Fintype E] (L : Finset V) :
    (outCut G L).card + (outCut G (L : Set V)ᶜ).card ≤ (G.cut L).card := by
  have hsub : outCut G L ∪ outCut G (L : Set V)ᶜ ⊆ G.cut L := by
    intro e he
    simp only [outCut, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_coe, Set.mem_compl_iff, not_not] at he
    rw [mem_cut]
    tauto
  have hdisj : Disjoint (outCut G L) (outCut G (L : Set V)ᶜ) := by
    rw [Finset.disjoint_left]
    intro e h₁ h₂
    simp only [outCut, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_compl_iff,
      not_not] at h₁ h₂
    exact h₂.1 h₁.1
  have := Finset.card_le_card hsub
  rwa [Finset.card_union_of_disjoint hdisj] at this

/-! ### Families of vertex-disjoint walks -/

/-- The first vertex of a directed walk lies on it. -/
theorem mem_of_isDirWalk_left {p : List V} {u v : V} (h : G.IsDirWalk p u v) : u ∈ p :=
  List.mem_of_mem_head? h.1

/-- The last vertex of a directed walk lies on it. -/
theorem mem_of_isDirWalk_right {p : List V} {u v : V} (h : G.IsDirWalk p u v) : v ∈ p :=
  List.mem_of_mem_getLast? h.2.1

/-- **Disjoint walks end apart.** Vertex-disjoint directed walks ending at the outputs
`output (target i)` of an injective labelling have distinct targets. -/
theorem injOn_target_of_walks {ι κ : Type*} {X : Finset ι} {walk : ι → List V} {src : ι → V}
    {output : κ → V} {target : ι → κ}
    (hwalk : ∀ i ∈ X, G.IsDirWalk (walk i) (src i) (output (target i)))
    (hdisj : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → (walk i).Disjoint (walk j)) :
    Set.InjOn target X := by
  intro i hi j hj hij
  by_contra hne
  exact hdisj i hi j hj hne (mem_of_isDirWalk_right (hwalk i hi))
    (by rw [hij]; exact mem_of_isDirWalk_right (hwalk j hj))

/-- **Disjoint walks leave along distinct edges.** If vertex-disjoint directed walks indexed by
`X` start in `L` and end outside `L`, then at least `|X|` edges are directed out of `L`. -/
theorem card_le_card_outCut_of_walks [Fintype E] {ι : Type*} (L : Set V) {X : Finset ι}
    {walk : ι → List V} {src dst : ι → V} (hwalk : ∀ i ∈ X, G.IsDirWalk (walk i) (src i) (dst i))
    (hdisj : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → (walk i).Disjoint (walk j))
    (hsrc : ∀ i ∈ X, src i ∈ L) (hdst : ∀ i ∈ X, dst i ∉ L) :
    X.card ≤ (outCut G L).card := by
  have H : ∀ i ∈ X, ∃ e, G.fst e ∈ walk i ∧ G.fst e ∈ L ∧ G.snd e ∉ L := fun i hi =>
    exists_cross_of_isDirWalk (hwalk i hi) (hsrc i hi) (hdst i hi)
  rcases X.eq_empty_or_nonempty with hX0 | ⟨i₀, hi₀⟩
  · simp [hX0]
  have : Nonempty E := ⟨(H i₀ hi₀).choose⟩
  choose! f hf using H
  refine Finset.card_le_card_of_injOn f (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simpa [outCut] using (hf i hi).2
  · by_contra hne
    exact hdisj i hi j hj hne (hf i hi).1 (hij ▸ (hf j hj).1)

/-- **Disjoint walks onto a set of outputs.** If vertex-disjoint walks indexed by `X` end at
outputs with labels in `Y`, and `Y` has at most `|X|` labels, then every label in `Y` is the
target of one of the walks. -/
theorem exists_target_eq_of_walks {ι κ : Type*} {X : Finset ι} {Y : Finset κ}
    {walk : ι → List V} {src : ι → V} {output : κ → V} {target : ι → κ}
    (hwalk : ∀ i ∈ X, G.IsDirWalk (walk i) (src i) (output (target i)))
    (hdisj : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → (walk i).Disjoint (walk j))
    (hY : ∀ i ∈ X, target i ∈ Y) (hcard : Y.card ≤ X.card) {j : κ} (hj : j ∈ Y) :
    ∃ i ∈ X, target i = j := by
  have himg : X.image target = Y := Finset.eq_of_subset_of_card_le
    (fun j hj => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
      exact hY i hi)
    (by rw [Finset.card_image_of_injOn (injOn_target_of_walks hwalk hdisj)]; exact hcard)
  exact Finset.mem_image.1 (himg ▸ hj)

/-- **Walks leaving `L`.** If vertex-disjoint walks indexed by `X` start in `L` and end at
outputs with labels in `Y`, then `|X|` is at most the number of edges directed out of `L` plus
the number of labels in `Y` whose outputs lie in `L`. -/
theorem card_le_card_outCut_add_card_filter [Fintype E] {ι κ : Type*} (L : Set V)
    {X : Finset ι} {Y : Finset κ} {walk : ι → List V} {src : ι → V} {output : κ → V}
    {target : ι → κ} (hwalk : ∀ i ∈ X, G.IsDirWalk (walk i) (src i) (output (target i)))
    (hdisj : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → (walk i).Disjoint (walk j))
    (hsrc : ∀ i ∈ X, src i ∈ L) (hY : ∀ i ∈ X, target i ∈ Y) :
    X.card ≤ (outCut G L).card + (Y.filter fun j => output j ∈ L).card := by
  have hin : (X.filter fun i => output (target i) ∈ L).card ≤
      (Y.filter fun j => output j ∈ L).card := by
    refine Finset.card_le_card_of_injOn target (fun i hi => ?_)
      ((injOn_target_of_walks hwalk hdisj).mono (Finset.filter_subset _ _))
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi ⊢
    exact ⟨hY i hi.1, hi.2⟩
  have hout : (X.filter fun i => output (target i) ∉ L).card ≤ (outCut G L).card :=
    card_le_card_outCut_of_walks L (fun i hi => hwalk i (Finset.mem_of_mem_filter i hi))
      (fun i hi j hj => hdisj i (Finset.mem_of_mem_filter i hi) j (Finset.mem_of_mem_filter j hj))
      (fun i hi => hsrc i (Finset.mem_of_mem_filter i hi)) fun i hi => (Finset.mem_filter.1 hi).2
  have := Finset.card_filter_add_card_filter_not (s := X) fun i => output (target i) ∈ L
  omega

/-- **Walks entering `L`.** If vertex-disjoint walks indexed by `X` start outside `L` and end at
outputs with labels in `Y`, and `Y` has at most `|X|` labels, then at least as many edges are
directed into `L` as there are labels in `Y` whose outputs lie in `L`. -/
theorem card_filter_le_card_outCut_compl [Fintype E] {ι κ : Type*} (L : Set V)
    {X : Finset ι} {Y : Finset κ} {walk : ι → List V} {src : ι → V} {output : κ → V}
    {target : ι → κ} (hwalk : ∀ i ∈ X, G.IsDirWalk (walk i) (src i) (output (target i)))
    (hdisj : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → (walk i).Disjoint (walk j))
    (hsrc : ∀ i ∈ X, src i ∉ L) (hY : ∀ i ∈ X, target i ∈ Y) (hcard : Y.card ≤ X.card) :
    (Y.filter fun j => output j ∈ L).card ≤ (outCut G Lᶜ).card := by
  set X' := X.filter fun i => output (target i) ∈ L
  have hsub : Y.filter (fun j => output j ∈ L) ⊆ X'.image target := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨i, hi, rfl⟩ := exists_target_eq_of_walks hwalk hdisj hY hcard hj.1
    exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hi, hj.2⟩, rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  exact card_le_card_outCut_of_walks Lᶜ (fun i hi => hwalk i (Finset.mem_of_mem_filter i hi))
    (fun i hi j hj => hdisj i (Finset.mem_of_mem_filter i hi) j (Finset.mem_of_mem_filter j hj))
    (fun i hi => hsrc i (Finset.mem_of_mem_filter i hi))
    fun i hi => by simpa using (Finset.mem_filter.1 hi).2

/-- **One walk family.** If `X` and `Y` are equally large, the inputs in `X` lie in `L`, and
the outputs in `Y` lie outside `L`, then at least `|X|` edges are directed out of `L`. -/
theorem card_le_card_cross [Fintype E] {N : ℕ} {input output : Fin N → V}
    (h : G.Superconcentrator input output) (L : Set V) {X Y : Finset (Fin N)}
    (hXY : X.card = Y.card) (hX : ∀ i ∈ X, input i ∈ L) (hY : ∀ j ∈ Y, output j ∉ L) :
    X.card ≤ (outCut G L).card := by
  obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X Y hXY
  exact card_le_card_outCut_of_walks L (fun i hi => (hwalk i hi).2) hdisj hX
    fun i hi => hY _ (hwalk i hi).1

/-! ### Lower sets with a prescribed number of chosen vertices -/

/-- **Prefixes of a chosen set.** In a linear order, for every `k` at most the size of a set
`T`, some lower set contains exactly `k` elements of `T`. -/
theorem exists_isLowerSet_card_filter [Fintype V] [LinearOrder V] (T : Finset V) {k : ℕ}
    (hk : k ≤ T.card) :
    ∃ L : Finset V, IsLowerSet (L : Set V) ∧ (T.filter (· ∈ L)).card = k := by
  rcases hk.lt_or_eq with hk | rfl
  · set f := T.orderEmbOfFin rfl
    set t := f ⟨k, hk⟩
    refine ⟨Finset.univ.filter (· < t), ?_, ?_⟩
    · intro a b hba ha
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at ha ⊢
      exact lt_of_le_of_lt hba ha
    have : T.filter (· ∈ Finset.univ.filter (· < t)) =
        (Finset.Iio (⟨k, hk⟩ : Fin T.card)).map f.toEmbedding := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Finset.mem_Iio, RelEmbedding.coe_toEmbedding]
      constructor
      · rintro ⟨hxT, hxt⟩
        have hx : x ∈ Set.range f := by rw [Finset.range_orderEmbOfFin]; exact hxT
        obtain ⟨i, rfl⟩ := hx
        exact ⟨i, f.lt_iff_lt.mp hxt, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        refine ⟨?_, f.lt_iff_lt.mpr hi⟩
        have : f i ∈ Set.range f := ⟨i, rfl⟩
        rwa [Finset.range_orderEmbOfFin] at this
    rw [this, Finset.card_map, Fin.card_Iio]
  · exact ⟨Finset.univ, by simpa using isLowerSet_univ, by simp⟩

/-- **The cut lemma.** Every linear order of the vertices of an `N`-superconcentrator has a
lower set whose cut has at least `N` edges. -/
theorem exists_le_card_cut [Fintype V] [Fintype E] [LinearOrder V] {N : ℕ}
    {input output : Fin N → V} (h : G.Superconcentrator input output) :
    ∃ L : Finset V, IsLowerSet (L : Set V) ∧ N ≤ (G.cut L).card := by
  set T : Finset V := Finset.univ.image input ∪ Finset.univ.image output with hTdef
  have hdisjT : Disjoint (Finset.univ.image input) (Finset.univ.image output) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    exact h.input_ne_output i j hj.symm
  have hT : T.card = 2 * N := by
    rw [hTdef, Finset.card_union_of_disjoint hdisjT,
      Finset.card_image_of_injective _ h.input_injective,
      Finset.card_image_of_injective _ h.output_injective, Finset.card_univ, Fintype.card_fin]
    ring
  obtain ⟨L, hL, hTL⟩ := exists_isLowerSet_card_filter T (k := N) (by omega)
  refine ⟨L, hL, ?_⟩
  set X := Finset.univ.filter fun i => input i ∈ L
  set X' := Finset.univ.filter fun i => input i ∉ L
  set Y := Finset.univ.filter fun j => output j ∉ L
  set Y' := Finset.univ.filter fun j => output j ∈ L
  have hsplit : (T.filter (· ∈ L)).card = X.card + Y'.card := by
    rw [hTdef, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisjT), Finset.filter_image, Finset.filter_image,
      Finset.card_image_of_injective _ h.input_injective,
      Finset.card_image_of_injective _ h.output_injective]
  have hX : X.card + X'.card = N := by
    simpa using Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => input i ∈ L)
  have hY : Y'.card + Y.card = N := by
    simpa using Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j => output j ∈ L)
  have hfwd := card_le_card_cross h (L : Set V) (X := X) (Y := Y) (by omega)
    (fun i hi => by simpa [X] using hi) (fun j hj => by simpa [Y] using hj)
  have hbwd := card_le_card_cross h ((L : Set V)ᶜ) (X := X') (Y := Y') (by omega)
    (fun i hi => by simpa [X'] using hi) (fun j hj => by simpa [Y'] using hj)
  have := card_outCut_add_card_outCut_compl_le (G := G) L
  omega

end Algebraic.Cutwidth.Superconcentrator.Internal
