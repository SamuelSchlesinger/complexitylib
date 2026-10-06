/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Concentrator.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Superconcentrator.Internal.Bound

/-!
# Proofs for concentrators

Let `G` be an `(n, m)`-concentrator with `1 ≤ m < n` and `h = min(m, n - m)`.

* **The cut lemma** (`exists_le_card_cut`). In a linear order of the vertices, take a lower
  set `L` with exactly `h` inputs, and let `b` outputs lie in `L`. Since `h ≤ m`, the `h` inputs
  in `L` are joined to distinct outputs; at most `b` of the walks end in `L`, and each of the
  others leaves `L` along an edge of its own. Since `n - h ≥ m`, some `m` inputs outside `L`
  are joined to `m` distinct outputs, that is, to all outputs, and each of the `b` walks ending
  in `L` enters it along an edge of its own. So the cut of `L` has at least `h` edges.
* **Connectivity** (`reflTransGen_root`). A set of vertices closed under adjacency holding `a`
  inputs holds at least `min(a, m)` outputs, as the walks from its inputs stay in it. If both
  the component of the first input and its complement held fewer than `m` outputs, each would
  hold no more inputs than outputs, so `n ≤ m`. Hence the component holds all `m` outputs, and
  then its complement holds no input.
* Every input is joined to an output and every output is reached from an input, so all
  terminals have a slot in the split graph of the component, which is again a concentrator
  (`split_concentrator`). The core inequality of `Superconcentrator.Internal` then gives
  `h ≤ (A + η) (M - n - m)⁺ + 3 log₂ (2 M) + C`, and the connected split graph gives the
  baseline `n + m ≤ M + 1`.
-/

@[expose] public section

open scoped Classical

namespace Algebraic.Cutwidth.Concentrator.Internal

open Multigraph Relation Filter Superconcentrator.Internal

variable {V E : Type} {G : Multigraph V E} {n m : ℕ} {input : Fin n → V} {output : Fin m → V}

/-! ### The cut lemma -/

/-- **The cut lemma.** Every linear order of the vertices of an `(n, m)`-concentrator has a
lower set whose cut has at least `min(m, n - m)` edges. -/
theorem exists_le_card_cut [Fintype V] [Fintype E] [LinearOrder V]
    (h : G.Concentrator input output) :
    ∃ L : Finset V, IsLowerSet (L : Set V) ∧ min m (n - m) ≤ (G.cut L).card := by
  set k := min m (n - m) with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · exact ⟨∅, by simpa using isLowerSet_empty, by omega⟩
  obtain ⟨L, hL, hcard⟩ := exists_isLowerSet_card_filter (Finset.univ.image input) (k := k)
    (by
      rw [Finset.card_image_of_injective _ h.input_injective, Finset.card_univ,
        Fintype.card_fin]
      omega)
  refine ⟨L, hL, ?_⟩
  set X := Finset.univ.filter fun i => input i ∈ L with hXdef
  have hX : X.card = k := by
    rw [← hcard, Finset.filter_image, Finset.card_image_of_injective _ h.input_injective]
  -- the inputs in `L` leave it, except those whose walks end at outputs in `L`
  obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X (by omega)
  have hfwd := card_le_card_outCut_add_card_filter (L : Set V) (Y := Finset.univ) hwalk hdisj
    (fun i hi => (Finset.mem_filter.1 hi).2) fun i _ => Finset.mem_univ _
  -- some `m` inputs outside `L` reach every output, entering `L` at each output in it
  have hX' : m ≤ Xᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨X', hX'sub, hX'card⟩ := Finset.exists_subset_card_eq hX'
  obtain ⟨target', walk', hwalk', hdisj'⟩ := h.exists_walks X' hX'card.le
  have hbwd := card_filter_le_card_outCut_compl (L : Set V) (Y := Finset.univ) hwalk' hdisj'
    (fun i hi => by simpa [X] using hX'sub hi) (fun i _ => Finset.mem_univ _)
    (by rw [Finset.card_univ, Fintype.card_fin, hX'card])
  have := card_outCut_add_card_outCut_compl_le (G := G) L
  omega

/-! ### The terminals lie in one component -/

/-- A predicate constant along edges is constant along undirected walks. -/
theorem iff_of_reflTransGen {P : V → Prop} (hP : ∀ u v, G.Adj u v → (P u ↔ P v)) {u v : V}
    (huv : ReflTransGen G.Adj u v) : P u ↔ P v := by
  induction huv with
  | refl => exact Iff.rfl
  | tail _ hstep ih => exact ih.trans (hP _ _ hstep)

/-- **Walks stay in closed sets.** If `P` is constant along edges and holds at the inputs of a
set `X` of at most `m` inputs, then at least `|X|` outputs satisfy `P`: every set `Y` containing
the outputs that satisfy `P` has at least `|X|` elements. -/
theorem card_le_card_of_closed (h : G.Concentrator input output) {P : V → Prop}
    (hP : ∀ u v, G.Adj u v → (P u ↔ P v)) {X : Finset (Fin n)} (hXm : X.card ≤ m)
    (hX : ∀ i ∈ X, P (input i)) {Y : Finset (Fin m)} (hY : ∀ j, P (output j) → j ∈ Y) :
    X.card ≤ Y.card := by
  obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X hXm
  refine Finset.card_le_card_of_injOn target (fun i hi => ?_)
    (injOn_target_of_walks hwalk hdisj)
  exact Finset.mem_coe.2
    (hY _ ((iff_of_reflTransGen hP (reflTransGen_of_isDirWalk (hwalk i hi))).1 (hX i hi)))

/-- A closed set holding the inputs of `S` holds at least `min(|S|, m)` outputs. -/
theorem min_card_le_card_of_closed (h : G.Concentrator input output) {P : V → Prop}
    (hP : ∀ u v, G.Adj u v → (P u ↔ P v)) {S : Finset (Fin n)} (hS : ∀ i ∈ S, P (input i))
    {Y : Finset (Fin m)} (hY : ∀ j, P (output j) → j ∈ Y) : min S.card m ≤ Y.card := by
  obtain ⟨X, hXsub, hXcard⟩ := Finset.exists_subset_card_eq (min_le_left S.card m)
  rw [← hXcard]
  exact card_le_card_of_closed h hP (hXcard ▸ min_le_right _ _) (fun i hi => hS i (hXsub hi)) hY

/-- **All terminals lie in one component.** If `1 ≤ m < n`, every input and every output of an
`(n, m)`-concentrator is joined to the first input by an undirected walk. -/
theorem reflTransGen_root (h : G.Concentrator input output) (hm : 1 ≤ m) (hmn : m < n) :
    (∀ i, ReflTransGen G.Adj (input i) (input ⟨0, by omega⟩)) ∧
      ∀ j, ReflTransGen G.Adj (output j) (input ⟨0, by omega⟩) := by
  set r := input ⟨0, by omega⟩
  let P : V → Prop := fun v => ReflTransGen G.Adj v r
  have hP : ∀ u v, G.Adj u v → (P u ↔ P v) := fun u v huv =>
    ⟨fun hu => (ReflTransGen.single huv.symm).trans hu,
      fun hv => (ReflTransGen.single huv).trans hv⟩
  have hQ : ∀ u v, G.Adj u v → (¬ P u ↔ ¬ P v) := fun u v huv => not_congr (hP u v huv)
  set I := Finset.univ.filter fun i => P (input i) with hIdef
  set O := Finset.univ.filter fun j => P (output j) with hOdef
  have h₁ := min_card_le_card_of_closed h hP (S := I) (Y := O)
    (fun i hi => (Finset.mem_filter.1 hi).2) fun j hj => Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩
  have h₂ := min_card_le_card_of_closed h hQ (S := Iᶜ) (Y := Oᶜ)
    (fun i hi => by simpa [I] using hi) fun j hj => by simpa [O] using hj
  rw [Finset.card_compl, Finset.card_compl, Fintype.card_fin, Fintype.card_fin] at h₂
  have hIn : I.card ≤ n := by simpa using Finset.card_le_univ I
  have hOm : O.card ≤ m := by simpa using Finset.card_le_univ O
  have hr : 1 ≤ I.card :=
    Finset.card_pos.2 ⟨⟨0, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, .refl⟩⟩
  have hO : O.card = m := by omega
  have hI : I.card = n := by omega
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have : I = Finset.univ := Finset.eq_univ_of_card I (by rw [hI, Fintype.card_fin])
    exact (Finset.mem_filter.1 (this ▸ Finset.mem_univ i : i ∈ I)).2
  · have : O = Finset.univ := Finset.eq_univ_of_card O (by rw [hO, Fintype.card_fin])
    exact (Finset.mem_filter.1 (this ▸ Finset.mem_univ j : j ∈ O)).2

/-! ### The split graph -/

variable [Fintype E]

/-- Every input has a kept edge leaving it. -/
theorem slots_input_pos (h : G.Concentrator input output) (hm : 1 ≤ m) (hmn : m < n)
    (i : Fin n) : 0 < slots G (compEdges G (input ⟨0, by omega⟩)) (input i) := by
  obtain ⟨target, walk, hwalk, -⟩ := h.exists_walks {i} (by simpa using hm)
  exact slots_pos_of_isDirWalk_left (hwalk i (Finset.mem_singleton_self i))
    (h.input_ne_output _ _) ((reflTransGen_root h hm hmn).1 i)

/-- Every output has a kept edge entering it. -/
theorem slots_output_pos (h : G.Concentrator input output) (hm : 1 ≤ m) (hmn : m < n)
    (j : Fin m) : 0 < slots G (compEdges G (input ⟨0, by omega⟩)) (output j) := by
  obtain ⟨X, -, hXcard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := m) (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X hXcard.le
  obtain ⟨i, hi, rfl⟩ := exists_target_eq_of_walks hwalk hdisj (Y := Finset.univ)
    (fun _ _ => Finset.mem_univ _) (by simp [hXcard]) (Finset.mem_univ j)
  exact slots_pos_of_isDirWalk_right (hwalk i hi) (h.input_ne_output _ _)
    ((reflTransGen_root h hm hmn).1 i)

/-- **The split graph of a concentrator.** If all inputs lie in the component of `r`, every
input has a slot, and every output has a slot, then the split graph of the component is a
concentrator with inputs at first slots and outputs at last slots. -/
theorem split_concentrator (h : G.Concentrator input output) {r : V}
    (hr : ∀ i, ReflTransGen G.Adj (input i) r)
    (hin : ∀ i, 0 < slots G (compEdges G r) (input i))
    (hout : ∀ j, 0 < slots G (compEdges G r) (output j)) :
    (split G (compEdges G r)).Concentrator (fun i => ⟨input i, ⟨0, hin i⟩⟩)
      (fun j => ⟨output j, ⟨slots G (compEdges G r) (output j) - 1,
        Nat.sub_lt (hout j) one_pos⟩⟩) where
  input_injective _ _ hij := h.input_injective (sigma_fin_eq_iff.1 hij).1
  output_injective _ _ hij := h.output_injective (sigma_fin_eq_iff.1 hij).1
  input_ne_output i j hij := h.input_ne_output i j (sigma_fin_eq_iff.1 hij).1
  exists_walks X hX := by
    obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X hX
    obtain ⟨walk', hwalk', hdisj'⟩ := exists_lift_walks hr hin hout hwalk hdisj
    exact ⟨target, walk', hwalk', hdisj'⟩

variable [Fintype V]

/-- The cut lemma holds in the split graph of the component of the first input. -/
theorem exists_le_card_cut_split (h : G.Concentrator input output) (hm : 1 ≤ m)
    (hmn : m < n) [LinearOrder (SplitVertex G (compEdges G (input ⟨0, by omega⟩)))] :
    ∃ L : Finset (SplitVertex G (compEdges G (input ⟨0, by omega⟩))),
      IsLowerSet (L : Set (SplitVertex G (compEdges G (input ⟨0, by omega⟩)))) ∧
        min m (n - m) ≤ ((split G (compEdges G (input ⟨0, by omega⟩))).cut L).card :=
  exists_le_card_cut (split_concentrator h (reflTransGen_root h hm hmn).1
    (slots_input_pos h hm hmn) (slots_output_pos h hm hmn))

/-- The `n + m` terminals have a slot. -/
theorem add_le_card_slotted (h : G.Concentrator input output) (hm : 1 ≤ m) (hmn : m < n) :
    n + m ≤
      (Finset.univ.filter fun w => slots G (compEdges G (input ⟨0, by omega⟩)) w ≠ 0).card := by
  have hdisj : Disjoint (Finset.univ.image input) (Finset.univ.image output) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    exact h.input_ne_output i j hj.symm
  have hcard : (Finset.univ.image input ∪ Finset.univ.image output).card = n + m := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ h.input_injective,
      Finset.card_image_of_injective _ h.output_injective, Finset.card_univ, Fintype.card_fin,
      Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  refine Finset.card_le_card fun w hw => ?_
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hw with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact (slots_input_pos h hm hmn i).ne'
  · exact (slots_output_pos h hm hmn j).ne'

/-- **The edge baseline.** An `(n, m)`-concentrator with `1 ≤ m < n` has at least `n + m - 1`
edges. -/
theorem add_le_card_add_one (h : G.Concentrator input output) (hm : 1 ≤ m) (hmn : m < n) :
    n + m ≤ Fintype.card E + 1 :=
  le_card_add_one_of_le_slotted (slots_input_pos h hm hmn _) (add_le_card_slotted h hm hmn)

/-- **The finite bound.** -/
theorem le_of_orderingBound {A η C : ℝ} (hord : OrderingBound A η C) (hAη : 0 ≤ A + η)
    (h : G.Concentrator input output) (hm : 1 ≤ m) (hmn : m < n) :
    ((min m (n - m) : ℕ) : ℝ) ≤ (A + η) * max ((Fintype.card E : ℝ) - (n + m)) 0 +
      3 * Real.logb 2 (2 * Fintype.card E) + C := by
  have := le_of_orderingBound_split_card hord hAη (slots_input_pos h hm hmn _)
    (exists_le_card_cut_split h hm hmn) (add_le_card_slotted h hm hmn)
  rwa [Nat.cast_add] at this

/-! ### Asymptotics -/

/-- **The asymptotic edge bound for a general ordering coefficient.** -/
theorem eventually_le_card_edges_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 1 ≤ m → m < n → ∀ (V E : Type) [Fintype V] [Fintype E]
      (G : Multigraph V E) (input : Fin n → V) (output : Fin m → V),
        G.Concentrator input output →
          (n : ℝ) + m + ((min m (n - m) : ℕ) : ℝ) / A - ε * n ≤ Fintype.card E := by
  obtain ⟨C, hC⟩ := hord (A ^ 2 * ε / 2) (by positivity)
  filter_upwards [eventually_le_of_bound_of_baseline hA hε (D := 2) (B := 2) (by norm_num)
    (by norm_num) C] with n hn
  intro m hm hmn V E _ _ G input output h
  have hb := le_of_orderingBound hC (by positivity) h hm hmn
  have hbase := add_le_card_add_one h hm hmn
  have hmin : min m (n - m) ≤ n := by omega
  refine hn _ _ _ (by positivity) (by exact_mod_cast hmin) ?_ ?_ (by positivity) hb
  · have : (m : ℝ) ≤ n := by exact_mod_cast hmn.le
    linarith
  · have : ((n + m : ℕ) : ℝ) ≤ Fintype.card E + 1 := by exact_mod_cast hbase
    push_cast at this
    linarith

/-- **The balanced asymptotic edge bound for a general ordering coefficient.** With `⌊n/2⌋`
outputs, at least `(3/2 + 1/(2A) - ε) n` edges. -/
theorem eventually_le_card_edges_half_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input : Fin n → V) (output : Fin (n / 2) → V), G.Concentrator input output →
        (3 / 2 + 1 / (2 * A) - ε) * n ≤ Fintype.card E := by
  filter_upwards [eventually_le_card_edges_of_orderingBound hA hord (half_pos hε),
    eventually_ge_atTop 2, eventually_ge_atTop ⌈(1 + 1 / A) / ε⌉₊] with n hn hn2 hnε
  intro V E _ _ G input output h
  have key := hn (n / 2) (by omega) (by omega) V E G input output h
  have hmin : min (n / 2) (n - n / 2) = n / 2 := min_eq_left (by omega)
  rw [hmin] at key
  have hhalf : ((n : ℝ) - 1) / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hnε' : (1 + 1 / A) / ε ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnε)
  have hnε'' : 1 + 1 / A ≤ ε * n := by
    rwa [div_le_iff₀ hε, mul_comm] at hnε'
  have hA' : 0 < 1 / A := by positivity
  have hdiv : ((n : ℝ) - 1) / 2 / A ≤ ((n / 2 : ℕ) : ℝ) / A :=
    div_le_div_of_nonneg_right hhalf hA.le
  have e₁ : ((n : ℝ) - 1) / 2 / A = 1 / (2 * A) * n - 1 / (2 * A) := by
    field_simp
  have e₂ : 1 / (2 * A) = 1 / A / 2 := by field_simp
  rw [e₁] at hdiv
  nlinarith

end Algebraic.Cutwidth.Concentrator.Internal
