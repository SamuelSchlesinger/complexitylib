/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Correlation.Internal.Lindsey
public import Complexitylib.Circuits.Frontier.AverageCase.Bias
import Mathlib.Tactic.Ring

/-!
# Quadratic forms are balanced on rectangles of large cut rank

Cut the coordinates into `X` and `Xᶜ`. On an input glued from an `X`-part `p` and an
`Xᶜ`-part `q`, the quadratic form of `Q` is a function of `p`, plus a function of `q`, plus
`p · B q` for the block `B` of `Q + Qᵀ` with rows `X` and columns `Xᶜ`. Lindsey's lemma then
bounds the signed sum of the form over every rectangle `R` for the cut `X`:

`(∑_{x ∈ R} (-1)^{f(x)})² · 2^{cutRank Q X} ≤ |R| · 2^n`.
-/

@[expose] public section

namespace Complexity.Correlation

open Finset Complexity.Frontier

variable {ι : Type*}

theorem bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- The sign of a quadratic form is the negated sign of its value in `ZMod 2`. -/
theorem boolSign_quadForm [Fintype ι] (Q : Matrix ι ι (ZMod 2)) (x : ι → Bool) :
    boolSign (quadForm Q x) = -zsign (∑ i, ∑ j, Q i j * bit (x i) * bit (x j)) := by
  unfold quadForm
  rcases zmod_two_eq_zero_or_one (∑ i, ∑ j, Q i j * bit (x i) * bit (x j)) with h | h <;>
    rw [h] <;> norm_num [boolSign, zsign]

section Merge

variable (X : Set ι) [DecidablePred (· ∈ X)]

/-- The input whose part on `X` is `p` and whose part on `Xᶜ` is `q`. -/
def merge {γ : Type*} (p : X → γ) (q : ↥Xᶜ → γ) : ι → γ :=
  fun i => if h : i ∈ X then p ⟨i, h⟩ else q ⟨i, h⟩

variable {X}

@[simp] theorem merge_coe_left {γ : Type*} (p : X → γ) (q : ↥Xᶜ → γ) (i : X) :
    merge X p q i = p i := by
  simp [merge, i.2]

@[simp] theorem merge_coe_right {γ : Type*} (p : X → γ) (q : ↥Xᶜ → γ) (i : ↥Xᶜ) :
    merge X p q i = q i := by
  have : (i : ι) ∉ X := i.2
  simp [merge, this]

theorem domRestrict_merge {γ : Type*} (p : X → γ) (q : ↥Xᶜ → γ) :
    X.domRestrict (merge X p q) = p :=
  funext fun i => merge_coe_left p q i

theorem domRestrict_compl_merge {γ : Type*} (p : X → γ) (q : ↥Xᶜ → γ) :
    Xᶜ.domRestrict (merge X p q) = q :=
  funext fun i => merge_coe_right p q i

theorem merge_domRestrict {γ : Type*} (x : ι → γ) :
    merge X (X.domRestrict x) (Xᶜ.domRestrict x) = x := by
  funext i
  by_cases h : i ∈ X <;> simp [merge, h]

theorem comp_merge {γ δ : Type*} (f : γ → δ) (p : X → γ) (q : ↥Xᶜ → γ) :
    f ∘ merge X p q = merge X (f ∘ p) (f ∘ q) := by
  funext i
  by_cases h : i ∈ X <;> simp [merge, h]

/-- A sum over all coordinates splits into the coordinates of `X` and of `Xᶜ`. -/
theorem sum_eq_sum_add_sum_compl [Fintype ι] [Fintype X] [Fintype ↥Xᶜ] {M : Type*}
    [AddCommMonoid M] (f : ι → M) : ∑ i, f i = ∑ i : X, f i + ∑ i : ↥Xᶜ, f i := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ X)]
  congr 1
  · exact Finset.sum_subtype _ (by simp) f
  · exact Finset.sum_subtype (p := (· ∈ Xᶜ)) _ (by simp) f

/-- A sum over a rectangle is a double sum over its two sides. -/
theorem sum_eq_sum_sum_merge {γ : Type*} {s : Finset (ι → γ)}
    {A : Finset (X → γ)} {B : Finset (↥Xᶜ → γ)}
    (hs : ∀ x, x ∈ s ↔ X.domRestrict x ∈ A ∧ Xᶜ.domRestrict x ∈ B) (w : (ι → γ) → ℝ) :
    ∑ x ∈ s, w x = ∑ p ∈ A, ∑ q ∈ B, w (merge X p q) := by
  rw [← Finset.sum_product' (f := fun p q => w (merge X p q))]
  refine Finset.sum_nbij' (fun x => (X.domRestrict x, Xᶜ.domRestrict x))
    (fun pq => merge X pq.1 pq.2) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_product.mpr ((hs x).mp hx)
  · intro pq hpq
    rw [hs, domRestrict_merge, domRestrict_compl_merge]
    exact Finset.mem_product.mp hpq
  · intro x _
    exact merge_domRestrict x
  · intro pq _
    rw [domRestrict_merge, domRestrict_compl_merge]
  · intro x _
    rw [merge_domRestrict]

/-- The block of the polar matrix `Q + Qᵀ` with rows `X` and columns `Xᶜ`. -/
def cutMatrix (Q : Matrix ι ι (ZMod 2)) (X : Set ι) : Matrix X ↥Xᶜ (ZMod 2) :=
  fun i j => Q i j + Q j i

omit [DecidablePred (· ∈ X)] in
theorem rank_cutMatrix [Fintype ↥Xᶜ] [Finite ι] (Q : Matrix ι ι (ZMod 2)) :
    (cutMatrix Q X).rank = cutRank Q X := by
  have : Finite X := inferInstance
  rw [Matrix.rank_eq_finrank_span_row]
  rfl

/-- **The polarization of a quadratic form across a cut.** -/
theorem quad_merge [Fintype ι] [Fintype X] [Fintype ↥Xᶜ] (Q : Matrix ι ι (ZMod 2))
    (u : X → ZMod 2) (v : ↥Xᶜ → ZMod 2) :
    ∑ i, ∑ j, Q i j * merge X u v i * merge X u v j =
      (∑ i : X, ∑ j : X, Q i j * u i * u j) + (∑ i : ↥Xᶜ, ∑ j : ↥Xᶜ, Q i j * v i * v j) +
        u ⬝ᵥ (cutMatrix Q X).mulVec v := by
  have hcross : u ⬝ᵥ (cutMatrix Q X).mulVec v =
      (∑ i : X, ∑ j : ↥Xᶜ, Q i j * u i * v j) + ∑ i : ↥Xᶜ, ∑ j : X, Q i j * v i * u j := by
    simp only [dotProduct, Matrix.mulVec, cutMatrix, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun (i : ↥Xᶜ) (j : X) => Q i j * v i * u j),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hcross, sum_eq_sum_add_sum_compl (X := X)]
  simp only [sum_eq_sum_add_sum_compl (X := X) (f := fun j => Q _ j * _ * merge X u v j),
    merge_coe_left, merge_coe_right, Finset.sum_add_distrib]
  ring

variable [Fintype ι] [DecidableEq ι]

/-- **Lindsey's lemma for quadratic forms.** Over any rectangle `s` for the cut `X`, the
signed sum of the quadratic form of `Q` satisfies `(∑_s (-1)^f)² · 2^{cutRank Q X} ≤ |s| 2^n`. -/
theorem sq_sum_boolSign_quadForm_mul_le (Q : Matrix ι ι (ZMod 2)) {s : Finset (ι → Bool)}
    {A : Finset (X → Bool)} {B : Finset (↥Xᶜ → Bool)}
    (hs : ∀ x, x ∈ s ↔ X.domRestrict x ∈ A ∧ Xᶜ.domRestrict x ∈ B) :
    (∑ x ∈ s, boolSign (quadForm Q x)) ^ 2 * 2 ^ cutRank Q X ≤
      s.card * 2 ^ Fintype.card ι := by
  classical
  -- The sides, read as vectors over `ZMod 2`.
  let eX : (X → Bool) ↪ (X → ZMod 2) := ⟨fun p => bit ∘ p, bit_injective.comp_left⟩
  let eY : (↥Xᶜ → Bool) ↪ (↥Xᶜ → ZMod 2) := ⟨fun q => bit ∘ q, bit_injective.comp_left⟩
  let g : (X → ZMod 2) → ℝ := fun u => zsign (∑ i : X, ∑ j : X, Q i j * u i * u j)
  let h : (↥Xᶜ → ZMod 2) → ℝ := fun v => zsign (∑ i : ↥Xᶜ, ∑ j : ↥Xᶜ, Q i j * v i * v j)
  have hcard : s.card = A.card * B.card := by
    have H := sum_eq_sum_sum_merge hs (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at H
    exact_mod_cast H
  have hsum : ∑ x ∈ s, boolSign (quadForm Q x) =
      -∑ u ∈ A.map eX, ∑ v ∈ B.map eY, g u * h v * zsign (u ⬝ᵥ (cutMatrix Q X).mulVec v) := by
    rw [sum_eq_sum_sum_merge hs, Finset.sum_map, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_map, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [boolSign_quadForm]
    have hq := quad_merge Q (bit ∘ p) (bit ∘ q)
    rw [← comp_merge] at hq
    simp only [Function.comp_apply] at hq
    rw [hq, zsign_add, zsign_add]
    rfl
  have hL := sq_sum_bilinear_mul_two_pow_rank_le (cutMatrix Q X) (A.map eX) (B.map eY) g h
    (fun _ => (abs_zsign _).le) (fun _ => (abs_zsign _).le)
  rw [rank_cutMatrix, Finset.card_map, Finset.card_map] at hL
  have hn : Fintype.card X + Fintype.card ↥Xᶜ = Fintype.card ι := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_add_ncard_compl X
  rw [hsum, neg_sq, hcard, ← hn, pow_add]
  push_cast
  linarith

end Merge

end Complexity.Correlation
