/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Superconcentrator.Internal.Lift
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics

/-!
# Superconcentrator lower bounds from the graph-ordering hypothesis

Root the component at the first input and split it. The split graph is a connected loopless
multigraph of maximum degree three and a superconcentrator, so the graph-ordering hypothesis
gives an ordering whose prefix cuts are small while the cut lemma gives a prefix cut with at
least `N` edges. Its edges minus vertices are the kept edges minus the vertices with a slot,
and it has twice as many vertices as there are kept edges. This gives
`N ≤ (A + η) (K - n)⁺ + 3 log₂ (2 K) + C` for `K` kept edges and `n` vertices with a slot.

All `2 N` terminals have a slot, so `K - n ≤ M - 2 N` for `M` edges. When the graph is
connected, `K - n = M - V`. When the inputs are sources and every vertex has in-degree at most
two, the kept edges enter non-input vertices with a slot, at most two each, which gives
`K - n ≤ (V - N) - N`.

A numeric lemma turns each of these bounds into an asymptotic one: if `Q` is less than
`(D + 1/A - ε) N`, the log term must absorb `(A ε / 2) N`, which fails for large `N`.
-/

@[expose] public section

open scoped Classical

namespace Algebraic.Cutwidth.Superconcentrator.Internal

open Multigraph Relation Filter

variable {V E : Type} {G : Multigraph V E} {N : ℕ} {input output : Fin N → V}

/-! ### The terminals -/

/-- The `2 N` terminals are distinct. -/
theorem card_terminals (h : G.Superconcentrator input output) :
    (Finset.univ.image input ∪ Finset.univ.image output).card = 2 * N := by
  have hdisj : Disjoint (Finset.univ.image input) (Finset.univ.image output) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    exact h.input_ne_output i j hj.symm
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ h.input_injective,
    Finset.card_image_of_injective _ h.output_injective, Finset.card_univ, Fintype.card_fin]
  ring

/-- Every input is joined to the first input by an undirected walk. -/
theorem reflTransGen_input_root (h : G.Superconcentrator input output) (hN : 0 < N)
    (i : Fin N) : ReflTransGen G.Adj (input i) (input ⟨0, hN⟩) := by
  obtain ⟨p, hp⟩ := exists_isDirWalk h i ⟨0, hN⟩
  obtain ⟨q, hq⟩ := exists_isDirWalk h ⟨0, hN⟩ ⟨0, hN⟩
  exact (reflTransGen_of_isDirWalk hp).trans
    (reflTransGen_adj_symm (reflTransGen_of_isDirWalk hq))

theorem slots_le_two_mul_card (K : Finset E) (w : V) : slots G K w ≤ 2 * K.card := by
  unfold slots inEdges outEdges
  have := Finset.card_filter_le K fun e => G.snd e = w
  have := Finset.card_filter_le K fun e => G.fst e = w
  omega

variable [Fintype E]

/-- Every input has a kept edge leaving it. -/
theorem slots_input_pos (h : G.Superconcentrator input output) (hN : 0 < N) (i : Fin N) :
    0 < slots G (compEdges G (input ⟨0, hN⟩)) (input i) := by
  obtain ⟨p, hp⟩ := exists_isDirWalk h i ⟨0, hN⟩
  obtain ⟨e, -, he₁, -⟩ := exists_cross_of_isDirWalk hp (L := {z | z = input i}) rfl
    fun h' => h.input_ne_output i _ h'.symm
  have he₁ : G.fst e = input i := he₁
  have heK : e ∈ compEdges G (input ⟨0, hN⟩) :=
    mem_compEdges.2 (he₁ ▸ reflTransGen_input_root h hN i)
  have hmem : e ∈ outEdges G (compEdges G (input ⟨0, hN⟩)) (input i) := by
    simp only [outEdges, Finset.mem_filter]
    exact ⟨heK, he₁⟩
  have := Finset.card_pos.2 ⟨e, hmem⟩
  unfold slots
  omega

/-- Every output has a kept edge entering it. -/
theorem slots_output_pos (h : G.Superconcentrator input output) (hN : 0 < N) (j : Fin N) :
    0 < slots G (compEdges G (input ⟨0, hN⟩)) (output j) := by
  obtain ⟨p, hp⟩ := exists_isDirWalk h ⟨0, hN⟩ j
  obtain ⟨e, hep, -, he₂⟩ := exists_cross_of_isDirWalk hp (L := {z | z ≠ output j})
    (h.input_ne_output _ j) (by simp)
  have he₂ : G.snd e = output j := by simpa using he₂
  have heK : e ∈ compEdges G (input ⟨0, hN⟩) :=
    mem_compEdges.2 (reflTransGen_adj_symm (reflTransGen_of_mem_isDirWalk hp hep))
  have hmem : e ∈ inEdges G (compEdges G (input ⟨0, hN⟩)) (output j) := by
    simp only [inEdges, Finset.mem_filter]
    exact ⟨heK, he₂⟩
  have := Finset.card_pos.2 ⟨e, hmem⟩
  unfold slots
  omega

/-! ### The core inequality -/

/-- The component of the first input has a kept edge. -/
theorem card_compEdges_pos (h : G.Superconcentrator input output) (hN : 0 < N) :
    0 < (compEdges G (input ⟨0, hN⟩)).card := by
  have := slots_input_pos h hN ⟨0, hN⟩
  have := slots_le_two_mul_card (G := G) (compEdges G (input ⟨0, hN⟩)) (input ⟨0, hN⟩)
  omega

variable [Fintype V]

/-- **Core inequality.** For `K` the kept edges of the component of the first input and `n`
the vertices with a slot, `N ≤ (A + η) (K - n)⁺ + 3 log₂ (2 K) + C`. -/
theorem le_of_orderingBound_core {A η C : ℝ} (hord : OrderingBound A η C)
    (h : G.Superconcentrator input output) (hN : 0 < N) :
    (N : ℝ) ≤ (A + η) * max (((compEdges G (input ⟨0, hN⟩)).card : ℝ) -
        (Finset.univ.filter fun w => slots G (compEdges G (input ⟨0, hN⟩)) w ≠ 0).card) 0 +
      3 * Real.logb 2 (2 * (compEdges G (input ⟨0, hN⟩)).card) + C := by
  obtain ⟨inst, bound⟩ := hord _ _ (split G (compEdges G (input ⟨0, hN⟩))) split_loopless
    split_maxDegreeLE (split_connected (slots_input_pos h hN _))
  obtain ⟨L, hL, hcut⟩ := exists_le_card_cut (split_superconcentrator h
    (reflTransGen_input_root h hN) (slots_input_pos h hN) (slots_output_pos h hN))
  have hb := bound L hL
  have h₁ := card_splitEdge_add (G := G) (K := compEdges G (input ⟨0, hN⟩))
  have h₂ := card_splitVertex (G := G) (K := compEdges G (input ⟨0, hN⟩))
  have h₁' : (Fintype.card (SplitEdge G (compEdges G (input ⟨0, hN⟩))) : ℝ) -
      Fintype.card (SplitVertex G (compEdges G (input ⟨0, hN⟩))) =
        ((compEdges G (input ⟨0, hN⟩)).card : ℝ) -
          (Finset.univ.filter fun w => slots G (compEdges G (input ⟨0, hN⟩)) w ≠ 0).card := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h₁
    push_cast at this
    linarith
  rw [h₁', h₂] at hb
  push_cast at hb
  have : (N : ℝ) ≤ ((split G (compEdges G (input ⟨0, hN⟩))).cut L).card := by
    exact_mod_cast hcut
  linarith

/-- **The finite bound.** -/
theorem le_of_orderingBound {A η C : ℝ} (hord : OrderingBound A η C) (hAη : 0 ≤ A + η)
    (h : G.Superconcentrator input output) (hN : 0 < N) :
    (N : ℝ) ≤ (A + η) * max ((Fintype.card E : ℝ) - 2 * N) 0 +
      3 * Real.logb 2 (2 * Fintype.card E) + C := by
  have core := le_of_orderingBound_core hord h hN
  have hK : (compEdges G (input ⟨0, hN⟩)).card ≤ Fintype.card E := Finset.card_le_univ _
  have hK0 := card_compEdges_pos h hN
  have hn : 2 * N ≤
      (Finset.univ.filter fun w => slots G (compEdges G (input ⟨0, hN⟩)) w ≠ 0).card := by
    rw [← card_terminals h]
    refine Finset.card_le_card fun w hw => ?_
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact (slots_input_pos h hN i).ne'
    · exact (slots_output_pos h hN j).ne'
  have hmax : max (((compEdges G (input ⟨0, hN⟩)).card : ℝ) -
      (Finset.univ.filter fun w => slots G (compEdges G (input ⟨0, hN⟩)) w ≠ 0).card) 0 ≤
        max ((Fintype.card E : ℝ) - 2 * N) 0 := by
    refine max_le_max ?_ le_rfl
    have hK' : ((compEdges G (input ⟨0, hN⟩)).card : ℝ) ≤ Fintype.card E := by exact_mod_cast hK
    have hn' : (2 * N : ℝ) ≤
        (Finset.univ.filter fun w => slots G (compEdges G (input ⟨0, hN⟩)) w ≠ 0).card := by
      exact_mod_cast hn
    linarith
  have hlog : Real.logb 2 (2 * (compEdges G (input ⟨0, hN⟩)).card) ≤
      Real.logb 2 (2 * Fintype.card E) := by
    have hK0' : (0 : ℝ) < (compEdges G (input ⟨0, hN⟩)).card := by exact_mod_cast hK0
    have hK' : ((compEdges G (input ⟨0, hN⟩)).card : ℝ) ≤ Fintype.card E := by exact_mod_cast hK
    exact Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
  have := mul_le_mul_of_nonneg_left hmax hAη
  linarith

/-- **The finite bound for connected superconcentrators.** -/
theorem le_of_orderingBound_of_connected {A η C : ℝ} (hord : OrderingBound A η C)
    (h : G.Superconcentrator input output) (hN : 0 < N) (hconn : G.Connected) :
    (N : ℝ) ≤ (A + η) * max ((Fintype.card E : ℝ) - Fintype.card V) 0 +
      3 * Real.logb 2 (2 * Fintype.card E) + C := by
  have core := le_of_orderingBound_core hord h hN
  have hK : compEdges G (input ⟨0, hN⟩) = Finset.univ := by
    ext e
    simp only [Finset.mem_univ, iff_true]
    exact mem_compEdges.2 (hconn _ _)
  have hn : (Finset.univ.filter fun w => slots G (compEdges G (input ⟨0, hN⟩)) w ≠ 0) =
      Finset.univ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases (hconn w (input ⟨0, hN⟩)).cases_head with hw | ⟨c, ⟨e, he⟩, -⟩
    · exact hw ▸ (slots_input_pos h hN _).ne'
    · have heK : e ∈ compEdges G (input ⟨0, hN⟩) := by rw [hK]; exact Finset.mem_univ e
      unfold slots
      rcases he with ⟨he, -⟩ | ⟨-, he⟩
      · have : e ∈ outEdges G (compEdges G (input ⟨0, hN⟩)) w := by
          simp only [outEdges, Finset.mem_filter]
          exact ⟨heK, he⟩
        have := Finset.card_pos.2 ⟨e, this⟩
        omega
      · have : e ∈ inEdges G (compEdges G (input ⟨0, hN⟩)) w := by
          simp only [inEdges, Finset.mem_filter]
          exact ⟨heK, he⟩
        have := Finset.card_pos.2 ⟨e, this⟩
        omega
  rw [hn, hK, Finset.card_univ, Finset.card_univ] at core
  exact core

/-- **The finite bound under in-degree two.** If the inputs have in-degree zero and every
vertex has in-degree at most two, then `N ≤ (A + η) ((V - N) - N)⁺ + 3 log₂ (4 (V - N)) + C`. -/
theorem le_of_orderingBound_of_inDegree {A η C : ℝ} (hord : OrderingBound A η C)
    (hAη : 0 ≤ A + η) (h : G.Superconcentrator input output) (hN : 0 < N)
    (hsrc : ∀ i, G.inDegree (input i) = 0) (hdeg : ∀ w, G.inDegree w ≤ 2) :
    (N : ℝ) ≤ (A + η) * max (((Fintype.card V : ℝ) - N) - N) 0 +
      3 * Real.logb 2 (4 * ((Fintype.card V : ℝ) - N)) + C := by
  have core := le_of_orderingBound_core hord h hN
  set K := compEdges G (input ⟨0, hN⟩) with hKdef
  set S := Finset.univ.filter fun w => (∀ i, input i ≠ w) ∧ slots G K w ≠ 0 with hSdef
  set n := (Finset.univ.filter fun w => slots G K w ≠ 0).card with hndef
  have hK0 := card_compEdges_pos h hN
  -- the kept edges enter non-input vertices with a slot, at most two each
  have hKS : K.card ≤ 2 * S.card := by
    rw [← sum_card_inEdges (G := G) (K := K)]
    rw [← Finset.sum_subset (Finset.subset_univ S) fun w _ hw => ?_]
    · calc ∑ w ∈ S, (inEdges G K w).card ≤ ∑ _w ∈ S, 2 :=
            Finset.sum_le_sum fun w _ => (Finset.card_le_card
              (Finset.filter_subset_filter _ (Finset.subset_univ K))).trans (hdeg w)
        _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    · simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_forall,
        not_not] at hw
      rcases hw with ⟨i, rfl⟩ | hw
      · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro e he
        simp only [inEdges, Finset.mem_filter] at he
        have := Finset.card_eq_zero.1 (hsrc i)
        rw [Finset.eq_empty_iff_forall_notMem] at this
        exact this e (by simpa using he.2)
      · have : (inEdges G K w).card ≤ slots G K w := Nat.le_add_right _ _
        omega
  -- the inputs and `S` are disjoint sets of vertices with a slot
  have hdisj : Disjoint (Finset.univ.image input) S := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, hSdef, Finset.mem_filter]
    rintro _ ⟨i, rfl⟩ hS
    exact hS.1 i rfl
  have himage : (Finset.univ.image input).card = N := by
    rw [Finset.card_image_of_injective _ h.input_injective, Finset.card_univ, Fintype.card_fin]
  have hnS : N + S.card ≤ n := by
    rw [← himage, ← Finset.card_union_of_disjoint hdisj]
    refine Finset.card_le_card fun w hw => ?_
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, hSdef,
      Finset.mem_filter] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with ⟨i, rfl⟩ | hw
    · exact (slots_input_pos h hN i).ne'
    · exact hw.2
  have hSV : N + S.card ≤ Fintype.card V := by
    rw [← himage, ← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ _
  have hKS' : (K.card : ℝ) ≤ 2 * S.card := by exact_mod_cast hKS
  have hnS' : (N : ℝ) + S.card ≤ n := by exact_mod_cast hnS
  have hSV' : (N : ℝ) + S.card ≤ Fintype.card V := by exact_mod_cast hSV
  have hmax : max ((K.card : ℝ) - n) 0 ≤ max (((Fintype.card V : ℝ) - N) - N) 0 :=
    max_le_max (by linarith) le_rfl
  have hlog : Real.logb 2 (2 * K.card) ≤ Real.logb 2 (4 * ((Fintype.card V : ℝ) - N)) := by
    have hK0' : (0 : ℝ) < K.card := by exact_mod_cast hK0
    exact Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
  have := mul_le_mul_of_nonneg_left hmax hAη
  linarith

/-! ### Asymptotics -/

/-- **Numeric core.** If `N ≤ (A + A² ε/2) (Q - D N)⁺ + 3 log₂ (B Q) + C`, then
`(D + 1/A - ε) N ≤ Q` for all large `N`. -/
theorem eventually_le_of_bound {A ε D B : ℝ} (hA : 0 < A) (hε : 0 < ε) (hεA : ε * A ≤ 1)
    (hD : 1 ≤ D) (hB : 1 ≤ B) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℝ, 0 ≤ Q →
      (N : ℝ) ≤ (A + A ^ 2 * ε / 2) * max (Q - D * N) 0 + 3 * Real.logb 2 (B * Q) + C →
        (D + 1 / A - ε) * N ≤ Q := by
  have hc : 1 ≤ D + 1 / A := by have : 0 < 1 / A := by positivity
                                linarith
  have hBc : 1 ≤ B * (D + 1 / A) := by nlinarith
  have hδ : 0 < A * ε / 2 := by positivity
  filter_upwards [eventually_mul_logb_add_lt 3 (3 * Real.logb 2 (B * (D + 1 / A)) + C) hδ,
    eventually_ge_atTop 1] with N hlogN hN1 Q hQ hbound
  by_contra hlt
  rw [not_le] at hlt
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hεA' : 0 ≤ 1 / A - ε := by
    rw [sub_nonneg, le_div_iff₀ hA]
    exact hεA
  have h₁ : max (Q - D * N) 0 ≤ (1 / A - ε) * N :=
    max_le (by linarith) (by positivity)
  have h₂ : (A + A ^ 2 * ε / 2) * ((1 / A - ε) * N) ≤ (1 - A * ε / 2) * N := by
    have : (A + A ^ 2 * ε / 2) * (1 / A - ε) = 1 - A * ε / 2 - A ^ 2 * ε ^ 2 / 2 := by
      field_simp
      ring
    rw [← mul_assoc, this]
    have : 0 ≤ A ^ 2 * ε ^ 2 / 2 * N := by positivity
    nlinarith
  have h₃ : Real.logb 2 (B * Q) ≤ Real.logb 2 (B * (D + 1 / A)) + Real.logb 2 N := by
    have hlogBc : 0 ≤ Real.logb 2 (B * (D + 1 / A)) := Real.logb_nonneg one_lt_two hBc
    have hlogN : 0 ≤ Real.logb 2 N := Real.logb_nonneg one_lt_two hN
    rcases hQ.eq_or_lt with hQ0 | hQ0
    · rw [← hQ0, mul_zero, Real.logb_zero]
      linarith
    · rw [← Real.logb_mul (by positivity) (by positivity)]
      refine Real.logb_le_logb_of_le one_lt_two (by positivity) ?_
      have : Q ≤ (D + 1 / A) * N := by nlinarith
      nlinarith
  have := mul_le_mul_of_nonneg_left h₁ (by positivity : (0 : ℝ) ≤ A + A ^ 2 * ε / 2)
  nlinarith

/-- **The asymptotic edge bound for a general ordering coefficient.** -/
theorem eventually_le_card_edges_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Superconcentrator input output →
        (2 + 1 / A - ε) * N ≤ Fintype.card E := by
  set ε' := min ε (1 / A)
  have hε' : 0 < ε' := lt_min hε (by positivity)
  have hε'A : ε' * A ≤ 1 := by
    calc ε' * A ≤ 1 / A * A := mul_le_mul_of_nonneg_right (min_le_right _ _) hA.le
      _ = 1 := by field_simp
  obtain ⟨C, hC⟩ := hord (A ^ 2 * ε' / 2) (by positivity)
  filter_upwards [eventually_le_of_bound hA hε' hε'A (D := 2) (B := 2) (by norm_num)
    (by norm_num) C, eventually_ge_atTop 1] with N hN hN1
  intro V E _ _ G input output h
  have hb := le_of_orderingBound hC (by positivity) h hN1
  have := hN (Fintype.card E) (by positivity) hb
  have : (2 + 1 / A - ε) * N ≤ (2 + 1 / A - ε') * N :=
    mul_le_mul_of_nonneg_right (by linarith [min_le_left ε (1 / A)]) (by positivity)
  linarith

/-- **The asymptotic vertex bound under in-degree two, for a general ordering coefficient.** -/
theorem eventually_le_card_vertices_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Superconcentrator input output →
        (∀ i, G.inDegree (input i) = 0) → (∀ w, G.inDegree w ≤ 2) →
          (1 + 1 / A - ε) * N ≤ (Fintype.card V : ℝ) - N := by
  set ε' := min ε (1 / A)
  have hε' : 0 < ε' := lt_min hε (by positivity)
  have hε'A : ε' * A ≤ 1 := by
    calc ε' * A ≤ 1 / A * A := mul_le_mul_of_nonneg_right (min_le_right _ _) hA.le
      _ = 1 := by field_simp
  obtain ⟨C, hC⟩ := hord (A ^ 2 * ε' / 2) (by positivity)
  filter_upwards [eventually_le_of_bound hA hε' hε'A (D := 1) (B := 4) le_rfl
    (by norm_num) C, eventually_ge_atTop 1] with N hN hN1
  intro V E _ _ G input output h hsrc hdeg
  have hb := le_of_orderingBound_of_inDegree hC (by positivity) h hN1 hsrc hdeg
  have hV : (N : ℝ) ≤ Fintype.card V := by
    have := Fintype.card_le_of_injective input h.input_injective
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have := hN ((Fintype.card V : ℝ) - N) (by linarith) (by simpa using hb)
  have : (1 + 1 / A - ε) * N ≤ (1 + 1 / A - ε') * N :=
    mul_le_mul_of_nonneg_right (by linarith [min_le_left ε (1 / A)]) (by positivity)
  linarith

end Algebraic.Cutwidth.Superconcentrator.Internal
