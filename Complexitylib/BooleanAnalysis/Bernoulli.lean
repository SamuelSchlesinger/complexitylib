/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Bernoulli.Defs
public import Complexitylib.BooleanAnalysis.Bernoulli.Internal

/-!
# Bernoulli coordinate sampling and transference

Boolean masks represent subsets of coordinates, ordered by inclusion. Increasing
the sampling rate decreases expectations of antitone functions. Unions of
independently sampled masks yield the downward-closed transference principle
used in Section 4 of Oliver Korten, *Top-Down Lower Bounds for All Depths*,
ECCC TR26-221 (2026), https://eccc.weizmann.ac.il/report/2026/221/.
Korten attributes this principle to Yufei Zhao, *Probabilistic Methods in
Combinatorics*, Lemma 4.3.7.
-/

public section

namespace Complexity.BooleanAnalysis

open scoped Classical

/-- Product Bernoulli weights sum to one. This identity holds algebraically
for every `p`; they are nonnegative when `p ∈ [0, 1]`. -/
theorem bernoulliAverage_const {ι : Type*} [Fintype ι] [DecidableEq ι] (p c : ℝ) :
    bernoulliAverage p (fun _ : ι → Bool => c) = c := bernoulliAverage_const_internal p c

/-- Bernoulli expectation preserves pointwise inequalities at probability rates. -/
theorem bernoulliAverage_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {f g : (ι → Bool) → ℝ}
    (hfg : ∀ x, f x ≤ g x) : bernoulliAverage p f ≤ bernoulliAverage p g :=
  bernoulliAverage_mono_internal hp hp' hfg

/-- An equivalence of coordinate types preserves Bernoulli expectations. -/
theorem bernoulliAverage_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (p : ℝ) (f : (κ → Bool) → ℝ) :
    bernoulliAverage p (fun x => f (fun j => x (e.symm j))) = bernoulliAverage p f :=
  bernoulliAverage_reindex_internal e p f

/-- Restricting a Bernoulli mask to fixed coordinates preserves its product law. -/
theorem bernoulliAverage_restrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (s : ι → Bool) (f : ({i // s i = true} → Bool) → ℝ) :
    bernoulliAverage p (fun x : ι → Bool => f (fun i => x i)) = bernoulliAverage p f :=
  bernoulliAverage_restrict_internal p s f

/-- Sampling at rate zero selects the empty coordinate set. -/
theorem bernoulliAverage_zero {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    bernoulliAverage 0 f = f (fun _ => false) := bernoulliAverage_zero_internal f

/-- Increasing the sampling rate decreases the expectation of an antitone function. -/
theorem bernoulliAverage_bias_antitone {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : Antitone f) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    bernoulliAverage q f ≤ bernoulliAverage p f :=
  bernoulliAverage_bias_antitone_internal hf hp hpq hq

/-- The union of independent masks of rates `p` and `q` has rate `p + q - p * q`. -/
theorem bernoulliAverage_union {n : ℕ} (p q : ℝ) (f : (Fin n → Bool) → ℝ) :
    bernoulliAverage p (fun r => bernoulliAverage q (fun s =>
      f (fun i => r i || s i))) = bernoulliAverage (p + q - p * q) f :=
  bernoulliAverage_union_internal p q f

/-- Integer repetition form of downward-closed transference. If `h` independent
rate-`p` masks have union rate at most `q`, membership at rate `q` forces every
mask to belong to the downward-closed family. The hypothesis `h * p ≤ q`
bounds that union rate. No nonemptiness assumption is needed. -/
theorem bernoulliAverage_lowerSet_pow_le {n : ℕ} {A : Set (Fin n → Bool)}
    (hA : IsLowerSet A) {p q : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : q ≤ 1)
    (h : ℕ) (hh : (h : ℝ) * p ≤ q) :
    bernoulliAverage q (fun x => if x ∈ A then (1 : ℝ) else 0) ≤
      bernoulliAverage p (fun x => if x ∈ A then (1 : ℝ) else 0) ^ h :=
  bernoulliAverage_lowerSet_pow_le_internal hA hp hp' hq h hh

/-- The `1/4`-to-sparse transfer inequality used in Korten's Lemma 10.
Nonemptiness covers the endpoint `r = 0`, where the right side is one. -/
theorem bernoulliAverage_lowerSet_transfer {n : ℕ} {A : Set (Fin n → Bool)}
    (hA : IsLowerSet A) (hA' : A.Nonempty) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1 / 20) :
    (bernoulliAverage (1 / 4) (fun x => if x ∈ A then (1 : ℝ) else 0)) ^ (5 * r) ≤
      bernoulliAverage r (fun x => if x ∈ A then (1 : ℝ) else 0) :=
  bernoulliAverage_lowerSet_transfer_internal hA hA' hr hr'

end Complexity.BooleanAnalysis
