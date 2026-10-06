/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DepthThree.Defs
public import Complexitylib.Circuits.KCNF.Basic
public import Complexitylib.Circuits.Frontier.Rectangle
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexitylib.Circuits.DepthThree.Internal.Basic

/-!
# Depth-three lower bounds for subcube dispersers

A `Σ₃^k` formula is an OR of `k`-CNFs (`IsSigmaThree`), and `Σ₃^k(f)` is the least number of
`k`-CNFs in one computing `f` (`sigmaThreeSize`); `Π₃^k(f) = Σ₃^k(¬f)` (`piThreeSize`). If the
accepted inputs of `f` contain no subcube of dimension `D`, neither do those of any `k`-CNF in an
OR computing `f`, so Theorem A (`CNF.card_accepting_le_of_not_containsSubcube`) gives

  `|f⁻¹(1)| ≤ Σ₃^k(f) · 2 ^ ((1 - 1/k + ε) N + C D)`.

For a family of functions that accept at least `2 ^ (n - o(n))` inputs and whose accepted sets
contain no subcube of dimension `o(n)` (a *subcube disperser*), this is
`Σ₃^k(f) ≥ 2 ^ ((1/k - o(1)) n)` for every fixed `k`. Rectangle-free sets with threshold
`2 ^ o(n)`, such as those of the frontier method (`Complexity.Frontier.RectangleFree`), are subcube
dispersers. `Complexitylib.Circuits.DepthThree.Explicit` applies this to an explicit family in `P`.

The exponent `1/k` cannot be improved for subcube dispersers: parity accepts no subcube of
dimension one, and when `k` divides `n` it is the OR of `2 ^ (n/k - 1)` `k`-CNFs, one for each
even-weight pattern of the parities of `n/k` blocks of `k` variables (Paturi, Pudlák and Zane).
For comparison, Frankl, Gryaznov and Talebanfard (ITCS 2022) prove `Σ₃^3 ≥ 2 ^ (0.064 n)` and
`Σ₃^k ≥ 2 ^ (n/(10k))` for affine dispersers through the switching lemma. A subcube is an affine
subspace, so an affine disperser for sublinear dimension that accepts `2 ^ (n - o(n))` inputs is
a subcube disperser, and the bound here has exponent `1/k - o(1)` for it.

## Main results

* `exists_isSigmaThree_length_eq_sigmaThreeSize`, `sigmaThreeSize_le_length`: `Σ₃^k(f)` is
  attained for `k ≥ 1`.
* `piThreeSize_eq_sigmaThreeSize_not`: De Morgan duality.
* `card_accepting_le_sigmaThreeSize`: the finite bound.
* `eventually_two_rpow_le_sigmaThreeSize`, `eventually_two_rpow_le_piThreeSize`: the asymptotic
  bounds for subcube dispersers.
* `not_containsSubcube_of_rectangleFree`, `eventually_two_rpow_le_sigmaThreeSize_of_rectangleFree`:
  rectangle-free families.
-/

@[expose] public section

namespace Complexity

open Filter Asymptotics

variable {N : ℕ}

/-- For `k ≥ 1` every function has a `Σ₃^k` formula: the OR of the minterms of its accepted
inputs. -/
theorem exists_isSigmaThree {k : ℕ} (hk : 1 ≤ k) (f : BitString N → Bool) :
    ∃ Fs, IsSigmaThree k f Fs :=
  DepthThree.exists_isSigmaThree hk f

/-- For `k ≥ 1`, `Σ₃^k(f)` is the size of some `Σ₃^k` formula for `f`. -/
theorem exists_isSigmaThree_length_eq_sigmaThreeSize {k : ℕ} (hk : 1 ≤ k)
    (f : BitString N → Bool) : ∃ Fs, IsSigmaThree k f Fs ∧ Fs.length = sigmaThreeSize k f :=
  DepthThree.sigmaThreeSize_spec hk f

/-- `Σ₃^k(f)` is at most the size of every `Σ₃^k` formula for `f`. -/
theorem sigmaThreeSize_le_length {k : ℕ} {f : BitString N → Bool} {Fs : List (CNF N)}
    (h : IsSigmaThree k f Fs) : sigmaThreeSize k f ≤ Fs.length :=
  DepthThree.sigmaThreeSize_le h

/-- **De Morgan duality.** An AND of DNFs computes `f` exactly when the OR of their negations,
CNFs of the same widths, computes `¬f`. -/
theorem isPiThree_iff_isSigmaThree_map_neg {k : ℕ} {f : BitString N → Bool}
    (Gs : List (DNF N)) :
    IsPiThree k f Gs ↔ IsSigmaThree k (fun x => !f x) (Gs.map DNF.neg) :=
  DepthThree.isPiThree_iff Gs

/-- `Π₃^k(f) = Σ₃^k(¬f)`. -/
theorem piThreeSize_eq_sigmaThreeSize_not (k : ℕ) (f : BitString N → Bool) :
    piThreeSize k f = sigmaThreeSize k (fun x => !f x) :=
  DepthThree.piThreeSize_eq_sigmaThreeSize_not k f

/-- **The finite bound.** For every `k ≥ 1` and `ε > 0` there is `C ≥ 0` such that, if the
accepted inputs of `f` contain no subcube of dimension `D`, then every OR of `t` CNFs of width at
most `k` computing `f` has `|f⁻¹(1)| ≤ t · 2 ^ ((1 - 1/k + ε) N + C D)`. -/
theorem IsSigmaThree.card_accepting_le (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (f : BitString N → Bool) (D : ℕ) (Fs : List (CNF N)),
      IsSigmaThree k f Fs → ¬ ContainsSubcube {x | f x = true} D →
      ((Finset.univ.filter fun x => f x = true).card : ℝ) ≤
        Fs.length * 2 ^ ((1 - 1 / (k : ℝ) + ε) * N + C * D) :=
  DepthThree.card_accepting_le k hk hε

/-- **The finite bound for `Σ₃^k`.** For every `k ≥ 1` and `ε > 0` there is `C ≥ 0` such that
every `f` whose accepted inputs contain no subcube of dimension `D` has
`|f⁻¹(1)| ≤ Σ₃^k(f) · 2 ^ ((1 - 1/k + ε) N + C D)`. -/
theorem card_accepting_le_sigmaThreeSize (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (f : BitString N → Bool) (D : ℕ),
      ¬ ContainsSubcube {x | f x = true} D →
      ((Finset.univ.filter fun x => f x = true).card : ℝ) ≤
        sigmaThreeSize k f * 2 ^ ((1 - 1 / (k : ℝ) + ε) * N + C * D) := by
  obtain ⟨C, hC, hbound⟩ := DepthThree.card_accepting_le k hk hε
  refine ⟨C, hC, fun N f D hfree => ?_⟩
  obtain ⟨Fs, hFs, hlen⟩ := DepthThree.sigmaThreeSize_spec hk f
  rw [← hlen]
  exact hbound N f D Fs hFs hfree

/-- **`Σ₃^k` lower bound for subcube dispersers.** Let `f` be a family of Boolean functions whose
accepted sets eventually contain no subcube of dimension `D n = o(n)` and have logarithmic
density deficit `n log 2 - log |f⁻¹(1)| = o(n)`. Then for every `k ≥ 1` and `ε > 0`, for all
large `n`, `Σ₃^k(f n) ≥ 2 ^ ((1/k - ε) n)`. -/
theorem eventually_two_rpow_le_sigmaThreeSize {f : (n : ℕ) → BitString n → Bool} {D : ℕ → ℕ}
    (hD : (fun n => (D n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (hfree : ∀ᶠ n in atTop, ¬ ContainsSubcube {x | f n x = true} (D n))
    (hdense : (fun n : ℕ => (n : ℝ) * Real.log 2 - Real.log {x | f n x = true}.ncard)
      =o[atTop] (fun n => (n : ℝ)))
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((1 / (k : ℝ) - ε) * n) ≤ sigmaThreeSize k (f n) :=
  DepthThree.eventually_le_sigmaThreeSize hD hfree hdense hk hε

/-- **`Π₃^k` lower bound.** If the rejected sets of `f` eventually contain no subcube of
dimension `D n = o(n)` and have logarithmic density deficit `o(n)`, then for every `k ≥ 1` and
`ε > 0`, for all large `n`, `Π₃^k(f n) ≥ 2 ^ ((1/k - ε) n)`. -/
theorem eventually_two_rpow_le_piThreeSize {f : (n : ℕ) → BitString n → Bool} {D : ℕ → ℕ}
    (hD : (fun n => (D n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (hfree : ∀ᶠ n in atTop, ¬ ContainsSubcube {x | f n x = false} (D n))
    (hdense : (fun n : ℕ => (n : ℝ) * Real.log 2 - Real.log {x | f n x = false}.ncard)
      =o[atTop] (fun n => (n : ℝ)))
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((1 / (k : ℝ) - ε) * n) ≤ piThreeSize k (f n) := by
  have hset : ∀ n, {x : BitString n | (!f n x) = true} = {x | f n x = false} := fun n => by
    ext x
    simp
  have h := DepthThree.eventually_le_sigmaThreeSize (f := fun n x => !f n x) hD
    (by simpa only [hset] using hfree) (by simpa only [hset] using hdense) hk hε
  filter_upwards [h] with n hn
  rw [piThreeSize_eq_sigmaThreeSize_not]
  exact hn

/-- **Rectangle-free sets contain no large subcubes.** If `K ≤ 2 ^ m`, a `K`-rectangle-free set
of inputs contains no subcube of dimension `2 m`: such a subcube splits into a rectangle whose
two sides have `2 ^ m` elements each. -/
theorem not_containsSubcube_of_rectangleFree {S : Set (BitString N)} {K m : ℕ}
    (hS : Frontier.RectangleFree S K) (hK : K ≤ 2 ^ m) : ¬ ContainsSubcube S (2 * m) :=
  DepthThree.not_containsSubcube_of_rectangleFree hS hK

/-- **`Σ₃^k` lower bound for rectangle-free families.** Under the hypotheses of the frontier
method (accepted sets eventually `K n`-rectangle-free with `log K = o(n)`, and logarithmic density
deficit `o(n)`), for every `k ≥ 1` and `ε > 0`, for all large `n`,
`Σ₃^k(f n) ≥ 2 ^ ((1/k - ε) n)`. -/
theorem eventually_two_rpow_le_sigmaThreeSize_of_rectangleFree
    {f : (n : ℕ) → BitString n → Bool} {K : ℕ → ℕ}
    (hrect : ∀ᶠ n in atTop, Frontier.RectangleFree {x | f n x = true} (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hdense : (fun n : ℕ => (n : ℝ) * Real.log 2 - Real.log {x | f n x = true}.ncard)
      =o[atTop] (fun n => (n : ℝ)))
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((1 / (k : ℝ) - ε) * n) ≤ sigmaThreeSize k (f n) := by
  refine DepthThree.eventually_le_sigmaThreeSize (D := fun n => 2 * Nat.clog 2 (K n))
    (DepthThree.isLittleO_two_mul_clog hK) ?_ hdense hk hε
  filter_upwards [hrect] with n hn
  exact DepthThree.not_containsSubcube_of_rectangleFree hn (Nat.le_pow_clog one_lt_two _)

end Complexity
