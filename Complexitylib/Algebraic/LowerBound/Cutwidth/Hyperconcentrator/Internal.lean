/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Hyperconcentrator.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Superconcentrator.Internal.Bound

/-!
# Proofs for hyperconcentrators

Let `G` be an `N`-hyperconcentrator and `h = ⌊N/2⌋`.

* **The cut lemma** (`exists_le_card_cut`). In a linear order of the vertices, take a lower
  set `L` with exactly `h` inputs, and let `c` of the first `h` outputs lie in `L`. The `h`
  inputs in `L` are joined to the first `h` outputs; at most `c` of the walks end in `L`, and
  each of the others leaves `L` along an edge of its own. The `N - h ≥ h` inputs outside `L` are
  joined to the first `N - h` outputs, among them the first `h`, and each of the `c` walks ending
  in `L` enters it along an edge of its own. So the cut of `L` has at least `h` edges.
* **Connectivity** (`reflTransGen_root`). Every input is joined to the first output, and every
  output is reached when all inputs are routed, so all terminals lie in one component.
* The split graph of that component is again a hyperconcentrator (`split_hyperconcentrator`),
  and the core inequalities of `Superconcentrator.Internal` give
  `h ≤ (A + η) (M - 2 N)⁺ + 3 log₂ (2 M) + C`, and, when the inputs are sources and every vertex
  has in-degree at most two, `h ≤ (A + η) ((V - N) - N)⁺ + 3 log₂ (4 (V - N)) + C`.
-/

@[expose] public section

open scoped Classical

namespace Algebraic.Cutwidth.Hyperconcentrator.Internal

open Multigraph Relation Filter Superconcentrator.Internal

variable {V E : Type} {G : Multigraph V E} {N : ℕ} {input output : Fin N → V}

/-- Every superconcentrator is a hyperconcentrator. -/
theorem hyperconcentrator_of_superconcentrator (h : G.Superconcentrator input output) :
    G.Hyperconcentrator input output where
  input_injective := h.input_injective
  output_injective := h.output_injective
  input_ne_output := h.input_ne_output
  exists_walks X := by
    have hcard : (Finset.univ.filter fun j : Fin N => (j : ℕ) < X.card).card = X.card := by
      have hX : X.card ≤ N := by simpa using Finset.card_le_univ X
      have : (Finset.univ.filter fun j : Fin N => (j : ℕ) < X.card) =
          (Finset.range X.card).attachFin fun j hj => by
            rw [Finset.mem_range] at hj
            omega := by
        ext j
        simp
      rw [this, Finset.card_attachFin, Finset.card_range]
    obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X _ hcard.symm
    exact ⟨target, walk, fun i hi => ⟨(Finset.mem_filter.1 (hwalk i hi).1).2, (hwalk i hi).2⟩,
      hdisj⟩

/-! ### The cut lemma -/

/-- The first `k` labels number at most `k`. -/
theorem card_filter_lt_le (k : ℕ) : (Finset.univ.filter fun j : Fin N => (j : ℕ) < k).card ≤ k :=
  (Finset.card_le_card_of_injOn (t := Finset.range k) (fun j : Fin N => (j : ℕ)) (fun j hj => by
    simpa using (Finset.mem_filter.1 hj).2) Fin.val_injective.injOn).trans (by simp)

/-- **The cut lemma.** Every linear order of the vertices of an `N`-hyperconcentrator has a
lower set whose cut has at least `⌊N/2⌋` edges. -/
theorem exists_le_card_cut [Fintype V] [Fintype E] [LinearOrder V]
    (h : G.Hyperconcentrator input output) :
    ∃ L : Finset V, IsLowerSet (L : Set V) ∧ N / 2 ≤ (G.cut L).card := by
  set k := N / 2 with hk
  obtain ⟨L, hL, hcard⟩ := exists_isLowerSet_card_filter (Finset.univ.image input) (k := k)
    (by
      rw [Finset.card_image_of_injective _ h.input_injective, Finset.card_univ,
        Fintype.card_fin]
      omega)
  refine ⟨L, hL, ?_⟩
  set X := Finset.univ.filter fun i => input i ∈ L with hXdef
  have hX : X.card = k := by
    rw [← hcard, Finset.filter_image, Finset.card_image_of_injective _ h.input_injective]
  -- the inputs in `L` are joined to the first `k` outputs
  obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X
  have hfwd := card_le_card_outCut_add_card_filter (L : Set V)
    (Y := Finset.univ.filter fun j : Fin N => (j : ℕ) < k) (fun i hi => (hwalk i hi).2) hdisj
    (fun i hi => (Finset.mem_filter.1 hi).2)
    fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, hX ▸ (hwalk i hi).1⟩
  -- the inputs outside `L` are joined to the first `N - k` outputs
  obtain ⟨target', walk', hwalk', hdisj'⟩ := h.exists_walks Xᶜ
  have hXc : Xᶜ.card = N - k := by rw [Finset.card_compl, Fintype.card_fin, hX]
  have hbwd := card_filter_le_card_outCut_compl (L : Set V)
    (Y := Finset.univ.filter fun j : Fin N => (j : ℕ) < Xᶜ.card) (fun i hi => (hwalk' i hi).2)
    hdisj' (fun i hi => by simpa [X] using hi)
    (fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, (hwalk' i hi).1⟩)
    (card_filter_lt_le _)
  calc k = X.card := hX.symm
    _ ≤ _ := hfwd
    _ ≤ (outCut G L).card + (outCut G (L : Set V)ᶜ).card := by
        refine Nat.add_le_add_left (le_trans ?_ hbwd) _
        refine Finset.card_le_card fun j hj => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact ⟨by omega, hj.2⟩
    _ ≤ (G.cut L).card := card_outCut_add_card_outCut_compl_le L

/-! ### The terminals lie in one component -/

/-- Every input is joined to the first output by a directed walk. -/
theorem exists_isDirWalk_first (h : G.Hyperconcentrator input output) (hN : 0 < N)
    (i : Fin N) : ∃ p, G.IsDirWalk p (input i) (output ⟨0, hN⟩) := by
  obtain ⟨target, walk, hwalk, -⟩ := h.exists_walks {i}
  obtain ⟨hlt, hw⟩ := hwalk i (Finset.mem_singleton_self i)
  rw [Finset.card_singleton] at hlt
  have : target i = ⟨0, hN⟩ := Fin.ext (by simp only; omega)
  exact ⟨walk i, this ▸ hw⟩

/-- Every output is reached from some input by a directed walk. -/
theorem exists_isDirWalk_output (h : G.Hyperconcentrator input output) (j : Fin N) :
    ∃ i p, G.IsDirWalk p (input i) (output j) := by
  obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks Finset.univ
  obtain ⟨i, hi, rfl⟩ := exists_target_eq_of_walks (fun i hi => (hwalk i hi).2) hdisj
    (Y := Finset.univ) (fun _ _ => Finset.mem_univ _) le_rfl (Finset.mem_univ j)
  exact ⟨i, walk i, (hwalk i hi).2⟩

/-- **All terminals lie in one component.** Every input and every output of an
`N`-hyperconcentrator with `N > 0` is joined to the first input by an undirected walk. -/
theorem reflTransGen_root (h : G.Hyperconcentrator input output) (hN : 0 < N) :
    (∀ i, ReflTransGen G.Adj (input i) (input ⟨0, hN⟩)) ∧
      ∀ j, ReflTransGen G.Adj (output j) (input ⟨0, hN⟩) := by
  have hin : ∀ i, ReflTransGen G.Adj (input i) (input ⟨0, hN⟩) := fun i => by
    obtain ⟨p, hp⟩ := exists_isDirWalk_first h hN i
    obtain ⟨q, hq⟩ := exists_isDirWalk_first h hN ⟨0, hN⟩
    exact (reflTransGen_of_isDirWalk hp).trans
      (reflTransGen_adj_symm (reflTransGen_of_isDirWalk hq))
  refine ⟨hin, fun j => ?_⟩
  obtain ⟨i, p, hp⟩ := exists_isDirWalk_output h j
  exact (reflTransGen_adj_symm (reflTransGen_of_isDirWalk hp)).trans (hin i)

/-! ### The split graph -/

variable [Fintype E]

/-- Every input has a kept edge leaving it. -/
theorem slots_input_pos (h : G.Hyperconcentrator input output) (hN : 0 < N) (i : Fin N) :
    0 < slots G (compEdges G (input ⟨0, hN⟩)) (input i) := by
  obtain ⟨p, hp⟩ := exists_isDirWalk_first h hN i
  exact slots_pos_of_isDirWalk_left hp (h.input_ne_output _ _) ((reflTransGen_root h hN).1 i)

/-- Every output has a kept edge entering it. -/
theorem slots_output_pos (h : G.Hyperconcentrator input output) (hN : 0 < N) (j : Fin N) :
    0 < slots G (compEdges G (input ⟨0, hN⟩)) (output j) := by
  obtain ⟨i, p, hp⟩ := exists_isDirWalk_output h j
  exact slots_pos_of_isDirWalk_right hp (h.input_ne_output _ _) ((reflTransGen_root h hN).1 i)

/-- **The split graph of a hyperconcentrator.** If all inputs lie in the component of `r`,
every input has a slot, and every output has a slot, then the split graph of the component is
a hyperconcentrator with inputs at first slots and outputs at last slots. -/
theorem split_hyperconcentrator (h : G.Hyperconcentrator input output) {r : V}
    (hr : ∀ i, ReflTransGen G.Adj (input i) r)
    (hin : ∀ i, 0 < slots G (compEdges G r) (input i))
    (hout : ∀ j, 0 < slots G (compEdges G r) (output j)) :
    (split G (compEdges G r)).Hyperconcentrator (fun i => ⟨input i, ⟨0, hin i⟩⟩)
      (fun j => ⟨output j, ⟨slots G (compEdges G r) (output j) - 1,
        Nat.sub_lt (hout j) one_pos⟩⟩) where
  input_injective _ _ hij := h.input_injective (sigma_fin_eq_iff.1 hij).1
  output_injective _ _ hij := h.output_injective (sigma_fin_eq_iff.1 hij).1
  input_ne_output i j hij := h.input_ne_output i j (sigma_fin_eq_iff.1 hij).1
  exists_walks X := by
    obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X
    obtain ⟨walk', hwalk', hdisj'⟩ := exists_lift_walks hr hin hout (X := X) (target := target)
      (fun i hi => (hwalk i hi).2) hdisj
    exact ⟨target, walk', fun i hi => ⟨(hwalk i hi).1, hwalk' i hi⟩, hdisj'⟩

variable [Fintype V]

/-- The cut lemma holds in the split graph of the component of the first input. -/
theorem exists_le_card_cut_split (h : G.Hyperconcentrator input output) (hN : 0 < N)
    [LinearOrder (SplitVertex G (compEdges G (input ⟨0, hN⟩)))] :
    ∃ L : Finset (SplitVertex G (compEdges G (input ⟨0, hN⟩))),
      IsLowerSet (L : Set (SplitVertex G (compEdges G (input ⟨0, hN⟩)))) ∧
        N / 2 ≤ ((split G (compEdges G (input ⟨0, hN⟩))).cut L).card :=
  exists_le_card_cut (split_hyperconcentrator h (reflTransGen_root h hN).1
    (slots_input_pos h hN) (slots_output_pos h hN))

omit [Fintype E] [Fintype V] in
/-- The `2 N` terminals are distinct vertices. -/
theorem card_terminals (h : G.Hyperconcentrator input output) :
    (Finset.univ.image input ∪ Finset.univ.image output).card = 2 * N := by
  have hdisj : Disjoint (Finset.univ.image input) (Finset.univ.image output) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    exact h.input_ne_output i j hj.symm
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ h.input_injective,
    Finset.card_image_of_injective _ h.output_injective, Finset.card_univ, Fintype.card_fin]
  ring

omit [Fintype E] in
/-- A hyperconcentrator has at least `2 N` vertices. -/
theorem two_mul_le_card_vertices (h : G.Hyperconcentrator input output) :
    2 * N ≤ Fintype.card V := by
  rw [← card_terminals h]
  exact Finset.card_le_univ _

/-- The `2 N` terminals have a slot. -/
theorem two_mul_le_card_slotted (h : G.Hyperconcentrator input output) (hN : 0 < N) :
    2 * N ≤ (Finset.univ.filter fun w => slots G (compEdges G (input ⟨0, hN⟩)) w ≠ 0).card := by
  rw [← card_terminals h]
  refine Finset.card_le_card fun w hw => ?_
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hw with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact (slots_input_pos h hN i).ne'
  · exact (slots_output_pos h hN j).ne'

/-- **The edge baseline.** An `N`-hyperconcentrator has at least `2 N - 1` edges. -/
theorem two_mul_le_card_add_one (h : G.Hyperconcentrator input output) (hN : 0 < N) :
    2 * N ≤ Fintype.card E + 1 :=
  le_card_add_one_of_le_slotted (slots_input_pos h hN _) (two_mul_le_card_slotted h hN)

/-- **The finite edge bound.** -/
theorem le_of_orderingBound {A η C : ℝ} (hord : OrderingBound A η C) (hAη : 0 ≤ A + η)
    (h : G.Hyperconcentrator input output) (hN : 0 < N) :
    ((N / 2 : ℕ) : ℝ) ≤ (A + η) * max ((Fintype.card E : ℝ) - 2 * N) 0 +
      3 * Real.logb 2 (2 * Fintype.card E) + C := by
  have := le_of_orderingBound_split_card hord hAη (slots_input_pos h hN _)
    (exists_le_card_cut_split h hN) (two_mul_le_card_slotted h hN)
  rwa [Nat.cast_mul, Nat.cast_ofNat] at this

/-- **The finite vertex bound under in-degree two.** -/
theorem le_of_orderingBound_of_inDegree {A η C : ℝ} (hord : OrderingBound A η C)
    (hAη : 0 ≤ A + η) (h : G.Hyperconcentrator input output) (hN : 0 < N)
    (hsrc : ∀ i, G.inDegree (input i) = 0) (hdeg : ∀ w, G.inDegree w ≤ 2) :
    ((N / 2 : ℕ) : ℝ) ≤ (A + η) * max (((Fintype.card V : ℝ) - N) - N) 0 +
      3 * Real.logb 2 (4 * ((Fintype.card V : ℝ) - N)) + C :=
  le_of_orderingBound_split_inDegree hord hAη (slots_input_pos h hN _)
    (exists_le_card_cut_split h hN) h.input_injective (slots_input_pos h hN) hsrc hdeg

/-! ### Asymptotics -/

omit [Fintype E] [Fintype V] in
/-- `⌊N/2⌋/A` is at least `N/(2A)` minus `ε N/2` once `N ≥ 1/(A ε)`. -/
theorem half_div_ge {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) {n : ℕ}
    (hn : ⌈1 / (A * ε)⌉₊ ≤ n) :
    1 / (2 * A) * n - ε / 2 * n ≤ ((n / 2 : ℕ) : ℝ) / A := by
  have hhalf : ((n : ℝ) - 1) / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hn' : 1 / (A * ε) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn'' : 1 ≤ A * ε * n := by
    rwa [div_le_iff₀ (by positivity), mul_comm] at hn'
  have hdiv : ((n : ℝ) - 1) / 2 / A ≤ ((n / 2 : ℕ) : ℝ) / A :=
    div_le_div_of_nonneg_right hhalf hA.le
  have e : ((n : ℝ) - 1) / 2 / A = 1 / (2 * A) * n - 1 / (2 * A) := by
    field_simp
  have h₁ : 1 / (2 * A) ≤ ε / 2 * n := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

omit [Fintype E] [Fintype V] in
/-- **The asymptotic edge bound for a general ordering coefficient.** -/
theorem eventually_le_card_edges_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Hyperconcentrator input output →
        (2 + 1 / (2 * A) - ε) * N ≤ Fintype.card E := by
  obtain ⟨C, hC⟩ := hord (A ^ 2 * (ε / 2) / 2) (by positivity)
  filter_upwards [eventually_le_of_bound_of_baseline hA (half_pos hε) (D := 2) (B := 2)
    (by norm_num) (by norm_num) C, eventually_ge_atTop 1,
    eventually_ge_atTop ⌈1 / (A * ε)⌉₊] with N hn hN1 hNε
  intro V E _ _ G input output h
  have hb := le_of_orderingBound hC (by positivity) h hN1
  have hbase := two_mul_le_card_add_one h hN1
  have key := hn ((N / 2 : ℕ) : ℝ) (2 * N) (Fintype.card E) (by positivity)
    (by exact_mod_cast Nat.div_le_self N 2) le_rfl
    (by
      have : ((2 * N : ℕ) : ℝ) ≤ Fintype.card E + 1 := by exact_mod_cast hbase
      push_cast at this
      linarith) (by positivity) hb
  have := half_div_ge hA hε hNε
  nlinarith

omit [Fintype E] [Fintype V] in
/-- **The asymptotic vertex bound under in-degree two, for a general ordering coefficient.** -/
theorem eventually_le_card_vertices_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Hyperconcentrator input output →
        (∀ i, G.inDegree (input i) = 0) → (∀ w, G.inDegree w ≤ 2) →
          (1 + 1 / (2 * A) - ε) * N ≤ (Fintype.card V : ℝ) - N := by
  obtain ⟨C, hC⟩ := hord (A ^ 2 * (ε / 2) / 2) (by positivity)
  filter_upwards [eventually_le_of_bound_of_baseline hA (half_pos hε) (D := 1) (B := 4)
    (by norm_num) (by norm_num) C, eventually_ge_atTop 1,
    eventually_ge_atTop ⌈1 / (A * ε)⌉₊] with N hn hN1 hNε
  intro V E _ _ G input output h hsrc hdeg
  have hb := le_of_orderingBound_of_inDegree hC (by positivity) h hN1 hsrc hdeg
  have hV : (2 * N : ℝ) ≤ Fintype.card V := by exact_mod_cast two_mul_le_card_vertices h
  have key := hn ((N / 2 : ℕ) : ℝ) N ((Fintype.card V : ℝ) - N) (by positivity)
    (by exact_mod_cast Nat.div_le_self N 2) (by linarith) (by linarith) (by linarith) hb
  have := half_div_ge hA hε hNε
  nlinarith

end Algebraic.Cutwidth.Hyperconcentrator.Internal
