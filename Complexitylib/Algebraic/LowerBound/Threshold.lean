/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Threshold.Defs
import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Corollaries
import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Activation
import Mathlib.Tactic.Ring

/-!
# One-dimensional capacity of threshold circuits of unbounded depth

The model is `Program n s`: a straight-line program of `s` weighted threshold gates on `n`
Boolean inputs, with arbitrary real weights (integer weights are a special case), arbitrary
depth, and arbitrary fan-in and fan-out. Gate `j` is `1` exactly when
`∑ i, inputWeight j i * x i + ∑_{k < j} gateWeight j k * (gate k) + bias j ≥ 0`
(`Program.eval_eq`). The bounds count only the *input-reading* gates `Program.inputGates`,
those with a nonzero input weight vector; gates that read only other gates are free.

Let `f` be *two-sided `K`-rectangle-free* (`TwoSidedRectangleFree`): under every split of the
coordinates, every rectangle on which `f` is constant has a side with fewer than `K` elements.

## Main results

* `exists_sorted_group` (Lemma 1): sorting a set by a real key and cutting it into `G`
  consecutive groups, some group is good for all but a `T / G` fraction of a family of functions
  of the key that each change at most `T` times (`ChangesAtMost`). Each such function is
  nonconstant on at most `T` groups (`ChangesAtMost.card_nonconstant_groups_le`).
* `Program.piecesAtMost_evalFrom`, `Program.changesAtMost_evalFrom` (Lemma 2): a run of
  threshold gates whose input contributions are `λ_j t` for one real parameter `t` has at most
  `2 ^ r` pieces in `t`, where `r` counts the gates with `λ_j ≠ 0`.
* `TwoSidedRectangleFree.two_pow_lt_mul_cost` (Theorem U, one-dimensional capacity): every
  `BlockDecomposition` of `f` has `2ⁿ < 4 K² · cost`, where the cost multiplies `4T` over the
  one-dimensional blocks with `T ≥ 1` changes and `V` over the summary blocks.
* `TwoSidedRectangleFree.two_pow_lt_of_directionRuns`: Theorem U for threshold programs split
  into consecutive runs along single directions, with run costs `4 (2 ^ rᵢ - 1)`.
* `TwoSidedRectangleFree.two_pow_lt_four_pow_inputGates`,
  `TwoSidedRectangleFree.lt_two_mul_add_two_mul_inputGates` (C1): every threshold program
  computing `f` has `2ⁿ < 4 K² · 4 ^ s_in`; with `K ≤ 2 ^ k`, `n < 2k + 2 + 2 s_in`.
* `TwoSidedRectangleFree.two_pow_lt_of_direction`, `TwoSidedRectangleFree.lt_of_direction` (C2):
  if all input weight vectors are multiples of one vector, `2ⁿ < 16 K² · 2 ^ s_in` and
  `n < 2k + 4 + s_in`.
* `TwoSidedRectangleFree.two_pow_lt_of_runs`, `TwoSidedRectangleFree.lt_of_runs` (C3): with
  `B` runs along single directions, `2ⁿ < 4 K² · 4 ^ B · 2 ^ s_in` and `n < 2k + 2 + 2B + s_in`.
* `TwoSidedRectangleFree.two_pow_lt_of_multilevel`,
  `TwoSidedRectangleFree.two_pow_sub_lt_of_multilevel` (C2′): if `f = F(⟨w, x⟩)` for a function
  `F` with `T` transitions, `2ⁿ < 4 K² · max 1 (4T)`, and `T > 2 ^ (n - 2k - 4)`.
* `TwoSidedRectangleFree.two_pow_lt_of_activations` (C4, mixed gate costs): in an
  `ActivationProgram` whose input-reading gate `j` has an activation changing at most `T j`
  times, `2ⁿ < 4 K² · ∏ⱼ max 1 (4 T j)`; a threshold gate costs `4`, an exact-threshold or
  interval gate `8`, and gates reading only gates are free.

The explicit polynomial-time family `sourceReductionHardFamily` is two-sided rectangle-free with
`log₂ K = o(n)`; the asymptotic bounds for it are in
`Complexitylib.Algebraic.LowerBound.Threshold.Family`.
-/

public section

namespace Algebraic.Threshold

variable {n s : ℕ} {β : Type*}

/-- A function with at most `M` pieces changes at most `M - 1` times. -/
theorem PiecesAtMost.changesAtMost {Φ : ℝ → β} {M : ℕ} (h : PiecesAtMost Φ M) :
    ChangesAtMost Φ (M - 1) :=
  changesAtMost_of_piecesAtMost_internal h

open scoped Classical in
/-- **Each function is nonconstant on few groups.** Cut the positions into consecutive groups of
`L`. A function changing at most `T` times along the nondecreasing sequence `z` is nonconstant
on at most `T` of the first `G` groups. -/
theorem ChangesAtMost.card_nonconstant_groups_le {Ψ : ℝ → β} {T : ℕ} (h : ChangesAtMost Ψ T)
    {z : ℕ → ℝ} (hz : Monotone z) (L G : ℕ) :
    ((Finset.range G).filter fun g =>
      ∃ j < L, ∃ j' < L, Ψ (z (g * L + j)) ≠ Ψ (z (g * L + j'))).card ≤ T :=
  card_nonconstant_groups_le_internal h hz L G

/-- **Lemma 1 (sorted groups).** Sort `P` by the real key `α` and cut it into `G` consecutive
groups of `⌊|P| / G⌋` elements. If every `Ψ q` changes at most `T` times, some group `P'` has
the functions `p ↦ Ψ q (α p)` constant on `P'` for every `q ∈ Q` outside a set `Qbad` with
`G |Qbad| ≤ T |Q|`. -/
theorem exists_sorted_group {ι κ : Type*} (P : Finset ι) (Q : Finset κ) (α : ι → ℝ)
    (Ψ : κ → ℝ → β) {T G : ℕ} (hG : 0 < G) (hΨ : ∀ q ∈ Q, ChangesAtMost (Ψ q) T) :
    ∃ P' ⊆ P, ∃ Qbad ⊆ Q, P.card / G ≤ P'.card ∧ G * Qbad.card ≤ T * Q.card ∧
      ∀ q ∈ Q, q ∉ Qbad → ∀ p ∈ P', ∀ p' ∈ P', Ψ q (α p) = Ψ q (α p') :=
  exists_sorted_group_internal P Q α Ψ hG hΨ

namespace Program

/-- **Gate semantics.** Gate `j` is `1` exactly when its weighted input sum, plus the weighted
values of the earlier gates, plus its bias, is nonnegative. -/
theorem eval_eq (C : Program n s) (x : Fin n → Bool) (j : Fin s) :
    C.eval x j = decide (0 ≤ weightedSum (C.inputWeight j) x + (∑ k : Fin s,
        if k < j then C.gateWeight j k * (C.eval x k).toNat else 0) + C.bias j) :=
  C.eval_eq_internal x j

open scoped Classical in
/-- **Lemma 2 (pieces of a run).** If every gate outside `fixed` receives the input contribution
`slope j * t`, and the gates in `fixed` are set by `η`, the gate values have at most `2 ^ r`
pieces as functions of `t`, where `r` counts the gates outside `fixed` with a nonzero slope. -/
theorem piecesAtMost_evalFrom (C : Program n s) (fixed : Finset (Fin s)) (η : Fin s → Bool)
    (slope : Fin s → ℝ) :
    PiecesAtMost (fun t => C.evalFrom fixed η (fun j => slope j * t))
      (2 ^ (Finset.univ.filter fun j => j ∉ fixed ∧ slope j ≠ 0).card) :=
  C.piecesAtMost_evalFrom_internal fixed η slope

open scoped Classical in
/-- **Lemma 2, change form.** The same run of gates changes at most `2 ^ r - 1` times. -/
theorem changesAtMost_evalFrom (C : Program n s) (fixed : Finset (Fin s)) (η : Fin s → Bool)
    (slope : Fin s → ℝ) :
    ChangesAtMost (fun t => C.evalFrom fixed η (fun j => slope j * t))
      (2 ^ (Finset.univ.filter fun j => j ∉ fixed ∧ slope j ≠ 0).card - 1) :=
  changesAtMost_of_piecesAtMost_internal (C.piecesAtMost_evalFrom_internal fixed η slope)

end Program

/-- **Gate semantics of activation programs.** Gate `j` applies its activation to its weighted
input sum plus the weighted values of the earlier gates. -/
theorem ActivationProgram.eval_eq (C : ActivationProgram n s) (x : Fin n → Bool) (j : Fin s) :
    C.eval x j = C.activation j (weightedSum (C.inputWeight j) x + ∑ k : Fin s,
      if k < j then C.gateWeight j k * (C.eval x k).toNat else 0) :=
  C.eval_eq_internal x j

namespace TwoSidedRectangleFree

variable {f : Cslib.BooleanFunction n} {K : ℕ}

/-- **Theorem U (one-dimensional capacity).** If `f` is two-sided `K`-rectangle-free, every block
decomposition of `f` satisfies `2ⁿ < 4 K² · cost`: the product of `4T` over its one-dimensional
blocks with `T ≥ 1` changes and of `V` over its summary blocks is more than `2ⁿ / (4 K²)`. -/
theorem two_pow_lt_mul_cost (hf : TwoSidedRectangleFree f K) {H : Type*}
    (D : BlockDecomposition f H) : 2 ^ n < 4 * K ^ 2 * D.cost :=
  two_pow_lt_mul_cost_internal hf D

/-- **Theorem U for threshold programs.** Split the gates of a threshold program computing `f`
into `B` consecutive runs along single directions, with `rᵢ` input-reading gates in run `i`.
Then `2ⁿ < 4 K² · ∏ᵢ cᵢ`, where `cᵢ = 4 (2 ^ rᵢ - 1)` if `rᵢ ≥ 1` and `cᵢ = 1` otherwise. -/
theorem two_pow_lt_of_directionRuns (hf : TwoSidedRectangleFree f K) {C : Program n s}
    (hC : C.Computes f) {B : ℕ} (R : C.DirectionRuns B) :
    2 ^ n < 4 * K ^ 2 * ∏ i ∈ Finset.range B, (BlockKind.oneDim (2 ^ R.size i - 1)).cost :=
  two_pow_lt_of_directionRuns_internal hf hC R

/-- **C1: input-reading gates of threshold circuits.** Every weighted threshold program computing
a two-sided `K`-rectangle-free function has `2ⁿ < 4 K² · 4 ^ s_in`, where `s_in` counts the gates
with a nonzero input weight vector; gates reading only gates are free. -/
theorem two_pow_lt_four_pow_inputGates (hf : TwoSidedRectangleFree f K) {C : Program n s}
    (hC : C.Computes f) : 2 ^ n < 4 * K ^ 2 * 4 ^ C.inputGates.card :=
  (two_pow_lt_of_directionRuns_internal hf hC C.gateRuns).trans_le
    (Nat.mul_le_mul_left _ C.gateRuns.prod_cost_le_four_pow)

/-- **C1, logarithmic form.** With `K ≤ 2 ^ k`, every threshold program computing `f` has
`n < 2k + 2 + 2 s_in`, that is, more than `(n - 2k - 2) / 2` input-reading gates. -/
theorem lt_two_mul_add_two_mul_inputGates (hf : TwoSidedRectangleFree f K) {k : ℕ}
    (hK : K ≤ 2 ^ k) {C : Program n s} (hC : C.Computes f) :
    n < 2 * k + 2 + 2 * C.inputGates.card :=
  lt_of_two_pow_lt_mul hK (by rw [pow_mul]; norm_num) (hf.two_pow_lt_four_pow_inputGates hC)

/-- **C2: one direction.** If every input weight vector of a threshold program computing `f` is a
real multiple of one vector `w`, then `2ⁿ < 16 K² · 2 ^ s_in`. -/
theorem two_pow_lt_of_direction (hf : TwoSidedRectangleFree f K) {C : Program n s}
    (hC : C.Computes f) (w : Fin n → ℝ) (along : ∀ j, ∃ c : ℝ, C.inputWeight j = c • w) :
    2 ^ n < 16 * K ^ 2 * 2 ^ C.inputGates.card := by
  have h := (two_pow_lt_of_directionRuns_internal hf hC (C.singleRun w along)).trans_le
    (Nat.mul_le_mul_left _ (C.singleRun w along).prod_cost_le_four_pow_mul)
  calc 2 ^ n < 4 * K ^ 2 * (4 ^ 1 * 2 ^ C.inputGates.card) := h
    _ = 16 * K ^ 2 * 2 ^ C.inputGates.card := by ring

/-- **C2, logarithmic form.** With `K ≤ 2 ^ k`, a threshold program computing `f` whose input
weight vectors are all multiples of one vector has `n < 2k + 4 + s_in`. -/
theorem lt_of_direction (hf : TwoSidedRectangleFree f K) {k : ℕ} (hK : K ≤ 2 ^ k)
    {C : Program n s} (hC : C.Computes f) (w : Fin n → ℝ)
    (along : ∀ j, ∃ c : ℝ, C.inputWeight j = c • w) :
    n < 2 * k + 4 + C.inputGates.card := by
  have h := hf.two_pow_lt_of_direction hC w along
  have := lt_of_two_pow_lt_mul (n := n) (X := 4 * 2 ^ C.inputGates.card)
    (e := C.inputGates.card + 2) hK (by rw [pow_add]; omega) (h.trans_eq (by ring))
  omega

/-- **C3: direction runs.** If the gates of a threshold program computing `f` split into `B`
consecutive runs along single directions, then `2ⁿ < 4 K² · 4 ^ B · 2 ^ s_in`. -/
theorem two_pow_lt_of_runs (hf : TwoSidedRectangleFree f K) {C : Program n s}
    (hC : C.Computes f) {B : ℕ} (R : C.DirectionRuns B) :
    2 ^ n < 4 * K ^ 2 * 4 ^ B * 2 ^ C.inputGates.card := by
  have h := (two_pow_lt_of_directionRuns_internal hf hC R).trans_le
    (Nat.mul_le_mul_left _ R.prod_cost_le_four_pow_mul)
  calc 2 ^ n < 4 * K ^ 2 * (4 ^ B * 2 ^ C.inputGates.card) := h
    _ = 4 * K ^ 2 * 4 ^ B * 2 ^ C.inputGates.card := by ring

/-- **C3, logarithmic form.** With `K ≤ 2 ^ k` and `B` direction runs,
`n < 2k + 2 + 2B + s_in`. -/
theorem lt_of_runs (hf : TwoSidedRectangleFree f K) {k : ℕ} (hK : K ≤ 2 ^ k)
    {C : Program n s} (hC : C.Computes f) {B : ℕ} (R : C.DirectionRuns B) :
    n < 2 * k + 2 + 2 * B + C.inputGates.card := by
  have h := hf.two_pow_lt_of_runs hC R
  have := lt_of_two_pow_lt_mul (n := n) (X := 4 ^ B * 2 ^ C.inputGates.card)
    (e := 2 * B + C.inputGates.card) hK (by rw [pow_add, pow_mul]; norm_num)
    (h.trans_eq (by ring))
  omega

/-- **C2′: multilevel threshold representations.** If `f x = F (⟨w, x⟩)` for a function `F`
changing at most `T` times, then `2ⁿ < 4 K² · max 1 (4T)`. -/
theorem two_pow_lt_of_multilevel (hf : TwoSidedRectangleFree f K) (w : Fin n → ℝ)
    (F : ℝ → Bool) {T : ℕ} (hF : ChangesAtMost F T) (hfF : ∀ x, f x = F (weightedSum w x)) :
    2 ^ n < 4 * K ^ 2 * max 1 (4 * T) :=
  two_pow_lt_of_multilevel_internal hf w F hF hfF

/-- **C2′, logarithmic form.** With `K ≤ 2 ^ k` and `2k + 4 ≤ n`, a multilevel threshold
representation `f = F(⟨w, x⟩)` needs more than `2 ^ (n - 2k - 4)` transitions. -/
theorem two_pow_sub_lt_of_multilevel (hf : TwoSidedRectangleFree f K) {k : ℕ}
    (hK : K ≤ 2 ^ k) (w : Fin n → ℝ) (F : ℝ → Bool) {T : ℕ} (hF : ChangesAtMost F T)
    (hfF : ∀ x, f x = F (weightedSum w x)) (hn : 2 * k + 4 ≤ n) :
    2 ^ (n - (2 * k + 4)) < T :=
  two_pow_sub_lt_of_multilevel_internal hf hK w F hF hfF hn

/-- **C4: mixed gate costs.** In an activation program computing `f` whose input-reading gate
`j` has an activation changing at most `T j` times, `2ⁿ < 4 K² · ∏ⱼ max 1 (4 T j)`, the product
ranging over the input-reading gates; gates reading only gates are free. -/
theorem two_pow_lt_of_activations (hf : TwoSidedRectangleFree f K) {C : ActivationProgram n s}
    (hC : C.Computes f) (T : Fin s → ℕ)
    (hT : ∀ j ∈ C.inputGates, ChangesAtMost (C.activation j) (T j)) :
    2 ^ n < 4 * K ^ 2 * ∏ j ∈ C.inputGates, max 1 (4 * T j) :=
  two_pow_lt_of_activations_internal hf hC T hT

end TwoSidedRectangleFree

end Algebraic.Threshold
