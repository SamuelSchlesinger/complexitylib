/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.Statement
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.PolynomialDegree
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Tactic

/-!
# Gotsman--Linial: SignParity

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/SignParity.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# Removing threshold zeros and turning sensitive edges into constant-sign edges

All graph pairs are ordered. The cube coordinates are the real
signs encoded by `Bool` in the public statement.
-/

open scoped BigOperators

namespace BooleanAnalysis.PolynomialThreshold.Internal

/-- Full parity, with values in the reals. -/
noncomputable def fullParity {n : ℕ} (x : Cube n) : ℝ :=
  ∏ i : Fin n, cubeCoord x i

/-- Two cube vertices differ by a single coordinate flip. -/
def CubeAdjacent {n : ℕ} (x y : Cube n) : Prop :=
  ∃ i : Fin n, flip i x = y

/-- All ordered pairs of neighboring vertices. -/
noncomputable def orderedNeighborPairs (n : ℕ) : Finset (Cube n × Cube n) := by
  classical
  exact Finset.univ.filter fun e => hammingDist e.1 e.2 = 1

/-- Ordered neighboring pairs at which a real function has equal values. -/
noncomputable def orderedConstantEdges {n : ℕ} (h : Cube n → ℝ) :
    Finset (Cube n × Cube n) := by
  classical
  exact (orderedNeighborPairs n).filter fun e => h e.1 = h e.2

private theorem exists_pos_lt_finset {α : Type*} (s : Finset α) (a : α → ℝ)
    (ha : ∀ x ∈ s, 0 < a x) : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s, ε < a x := by
  classical
  revert ha
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨1, by norm_num, by simp⟩
  | @insert x s hx ih =>
      intro ha
      obtain ⟨ε, hε, hεa⟩ := ih (fun y hy => ha y (Finset.mem_insert_of_mem hy))
      have hax : 0 < a x := ha x (Finset.mem_insert_self x s)
      refine ⟨min ε (a x / 2), lt_min hε (by linarith), ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_left _ _) (hεa y hy)

/-- A positive constant removes all zeros of a real function on a finite set
without changing its threshold signs, including the convention `sign(0)=1`. -/
theorem exists_pos_shift_nonzero_preserves_sign {α : Type*} [Fintype α]
    (v : α → ℝ) : ∃ ε : ℝ, 0 < ε ∧ (∀ x, v x + ε ≠ 0) ∧
      (∀ x, thresholdSign (v x + ε) = thresholdSign (v x)) := by
  classical
  let a : α → ℝ := fun x => if v x < 0 then -v x else 1
  have ha : ∀ x ∈ (Finset.univ : Finset α), 0 < a x := by
    intro x _
    by_cases hx : v x < 0
    · simp [a, hx, neg_pos.mpr hx]
    · simp [a, hx]
  obtain ⟨ε, hε, hεa⟩ := exists_pos_lt_finset Finset.univ a ha
  have hneg : ∀ x, v x < 0 → v x + ε < 0 := by
    intro x hx
    have he : ε < -v x := by simpa [a, hx] using hεa x (Finset.mem_univ x)
    linarith
  refine ⟨ε, hε, ?_, ?_⟩
  · intro x
    by_cases hx : v x < 0
    · exact ne_of_lt (hneg x hx)
    · exact ne_of_gt (add_pos_of_nonneg_of_pos (le_of_not_gt hx) hε)
  · intro x
    by_cases hx : v x < 0
    · simp [thresholdSign, not_le.mpr hx, not_le.mpr (hneg x hx)]
    · have hv : 0 ≤ v x := le_of_not_gt hx
      simp [thresholdSign, hv, add_nonneg hv hε.le]

@[simp] theorem fullParity_sq {n : ℕ} (x : Cube n) : fullParity x ^ 2 = 1 := by
  rw [fullParity, ← Finset.prod_pow]
  simp

theorem fullParity_cases {n : ℕ} (x : Cube n) :
    fullParity x = 1 ∨ fullParity x = -1 :=
  sq_eq_one_iff.mp (fullParity_sq x)

/-- Reversing one coordinate reverses full parity. -/
@[simp] theorem fullParity_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    fullParity (flip i x) = -fullParity x := by
  classical
  have hc : cubeCoord (flip i x) = Function.update (cubeCoord x) i (-cubeCoord x i) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [cubeCoord_flip_ne x i j hj, Function.update_of_ne hj]
  unfold fullParity
  rw [hc, Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase, neg_mul,
    Finset.mul_prod_erase Finset.univ (cubeCoord x) (Finset.mem_univ i)]

@[simp] theorem hammingDist_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    hammingDist x (flip i x) = 1 := by
  classical
  have hset : (Finset.univ.filter fun j => x j ≠ flip i x j) = {i} := by
    ext j
    by_cases hj : j = i
    · subst j
      cases hx : x i <;> simp [flip, hx]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      simp [flip, hj]
  simp only [hammingDist, hset, Finset.card_singleton]

/-- The flip definition of adjacency agrees with Hamming distance one. -/
theorem adjacent_iff_hammingDist_eq_one {n : ℕ} (x y : Cube n) :
    CubeAdjacent x y ↔ hammingDist x y = 1 := by
  classical
  constructor
  · rintro ⟨i, rfl⟩
    exact hammingDist_flip i x
  · intro hxy
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hxy
    refine ⟨i, ?_⟩
    funext j
    by_cases hj : j = i
    · subst j
      have hmem : i ∈ Finset.univ.filter (fun j => x j ≠ y j) := by rw [hi]; simp
      have hneq : x i ≠ y i := (Finset.mem_filter.mp hmem).2
      rw [flip_apply_same]
      cases hx : x i <;> cases hy : y i <;> simp_all
    · have heq : x j = y j := by
        by_contra hneq
        have hmem : j ∈ Finset.univ.filter (fun j => x j ≠ y j) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hneq⟩
        rw [hi] at hmem
        exact hj (Finset.mem_singleton.mp hmem)
      rw [flip_apply_ne i x j hj, heq]

/-- A vertex and a direction identify a unique ordered cube edge. -/
def directedEdgeEmbedding (n : ℕ) : (Fin n × Cube n) ↪ (Cube n × Cube n) where
  toFun e := (e.2, flip e.1 e.2)
  inj' := by
    rintro ⟨i, x⟩ ⟨j, y⟩ heq
    have hxy : x = y := congrArg Prod.fst heq
    subst y
    have hij : i = j := flip_injective_direction x (congrArg Prod.snd heq)
    subst j
    rfl

theorem orderedNeighborPairs_eq_map {n : ℕ} :
    orderedNeighborPairs n = Finset.univ.map (directedEdgeEmbedding n) := by
  classical
  ext e
  constructor
  · intro he
    have hd : hammingDist e.1 e.2 = 1 := (Finset.mem_filter.mp he).2
    obtain ⟨i, hi⟩ := (adjacent_iff_hammingDist_eq_one e.1 e.2).mpr hd
    exact Finset.mem_map.mpr ⟨(i, e.1), Finset.mem_univ _, Prod.ext rfl hi⟩
  · intro he
    obtain ⟨⟨i, x⟩, _, rfl⟩ := Finset.mem_map.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hammingDist_flip i x⟩

/-- The `n * 2^n` count includes both orientations of every cube edge. -/
theorem card_orderedNeighborPairs (n : ℕ) :
    (orderedNeighborPairs n).card = n * 2 ^ n := by
  rw [orderedNeighborPairs_eq_map]
  simp

theorem card_orderedConstantEdges {n : ℕ} (h : Cube n → ℝ) :
    (orderedConstantEdges h).card =
      ∑ i : Fin n, (Finset.univ.filter fun x => h x = h (flip i x)).card := by
  classical
  unfold orderedConstantEdges
  rw [orderedNeighborPairs_eq_map, Finset.filter_map, Finset.card_map]
  change (Finset.univ.filter fun e : Fin n × Cube n => h e.2 = h (flip e.1 e.2)).card = _
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Fintype.sum_prod_type _

/-- Twisting a sign-valued function by parity changes sensitivity into
equality across a coordinate flip. -/
theorem parity_twist_eq_iff {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) (i : Fin n) (x : Cube n) :
    fullParity x * f x = fullParity (flip i x) * f (flip i x) ↔
      f x ≠ f (flip i x) := by
  rw [fullParity_flip]
  rcases fullParity_cases x with hp | hp <;>
    rcases hf x with hx | hx <;>
    rcases hf (flip i x) with hy | hy <;> norm_num [hp, hx, hy]

theorem parity_twist_cases {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) (x : Cube n) :
    fullParity x * f x = 1 ∨ fullParity x * f x = -1 := by
  rcases fullParity_cases x with hp | hp <;>
    rcases hf x with hx | hx <;> simp [hp, hx]

theorem card_orderedConstantEdges_parity {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) :
    (orderedConstantEdges (fun x => fullParity x * f x)).card = sensitiveEdgeCount f := by
  classical
  rw [card_orderedConstantEdges]
  unfold sensitiveEdgeCount
  apply Finset.sum_congr rfl
  intro i _
  unfold sensitiveVertices
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x _
  exact parity_twist_eq_iff hf i x

/-- Exact uniform normalization: both sides count each sensitive undirected
edge twice, once in each direction. -/
theorem averageSensitivity_eq_parity_edges {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) :
    averageSensitivity f =
      ((orderedConstantEdges (fun x => fullParity x * f x)).card : ℝ) / (2 : ℝ) ^ n := by
  rw [averageSensitivity_eq_count, card_orderedConstantEdges_parity hf]

theorem polynomialThreshold_sensitivity_eq_parity_edges {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) :
    averageSensitivity (polynomialThreshold p) =
      ((orderedConstantEdges (fun x => fullParity x * polynomialThreshold p x)).card : ℝ) /
        (2 : ℝ) ^ n :=
  averageSensitivity_eq_parity_edges (fun x => thresholdSign_cases (polynomialValue p x))

/-- The real parity used for threshold signs is exactly the full complex
Walsh character under the standard real embedding. -/
@[simp] theorem ofReal_fullParity {n : ℕ} (x : Cube n) :
    (fullParity x : ℂ) = walshChar Finset.univ x := by
  simp only [fullParity, Complex.ofReal_prod, walshChar]

@[simp] theorem polynomialValue_add_C {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (ε : ℝ) (x : Cube n) :
    polynomialValue (p + MvPolynomial.C ε) x = polynomialValue p x + ε := by
  simp [polynomialValue]

/-- The zero-removal reduction preserves multilinearity, the degree bound,
and the entire threshold function. -/
theorem exists_nonzero_polynomial_same_threshold {n d : ℕ}
    {p : MvPolynomial (Fin n) ℝ} (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    ∃ q : MvPolynomial (Fin n) ℝ,
      IsMultilinear q ∧ q.totalDegree ≤ d ∧
        (∀ x : Cube n, polynomialValue q x ≠ 0) ∧
        polynomialThreshold q = polynomialThreshold p := by
  obtain ⟨ε, _hε, hnonzero, hsign⟩ :=
    exists_pos_shift_nonzero_preserves_sign (polynomialValue p)
  refine ⟨p + MvPolynomial.C ε, hp.add_C ε, totalDegree_add_C_le hd ε, ?_, ?_⟩
  · intro x
    simpa only [polynomialValue_add_C] using hnonzero x
  · funext x
    simpa only [polynomialThreshold, polynomialValue_add_C] using hsign x

end BooleanAnalysis.PolynomialThreshold.Internal

end Complexity
