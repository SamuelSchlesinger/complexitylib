/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.DFT.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Linear.Rank
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Rank
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.ZMod.Torsion
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.DFT.Internal

/-!
# The discrete Fourier transform needs `(2.78 - o(1)) N` gates

Let `ω` be a primitive `N`-th root of unity in a field `F` and `dft ω N = (ω ^ (r c))` the
`N`-point Fourier matrix, for any `N` (in particular `N = 2^k`, the map computed by the fast
Fourier transform). For every `ε > 0` and all large `N`, uniformly in the field:

* every fan-in-two **linear** circuit over `F` computing `x ↦ dft ω N x`, that is, every circuit
  with a local linear realization (`Linear.Realization`) in which each gate computes a linear
  combination of its arguments with arbitrary coefficients, has more than
  `(1 + κ/2 - ε) N ≈ (2.78 - ε) N` gates (`Linear.eventually_lt_size_dft`), where
  `κ = π/(3 arccos((1 + 2√2)/4)) ≈ 3.5625` is `1/(2p)` for the Gaussian edge-score pathwidth
  coefficient `p`; at least `(25/9 - ε) N`. This covers the complex DFT with `ω = e^{2πi/N}`
  (`Linear.eventually_lt_size_complexDFT`, `Linear.eventually_lt_size_fft`);
* over a **finite** field, the same holds for every fan-in-two circuit with **arbitrary** gates
  `F × F → F` computing `x ↦ dft ω N x` (`eventually_lt_size_dft`), such as the
  number-theoretic transforms over `ZMod q` with `N ∣ q - 1` (`eventually_lt_size_ntt`).

The Fourier matrix is not totally regular (for `N = 4` it has singular `2 × 2` blocks), so the
bound for totally regular maps does not apply. Instead, the proof uses half cuts. The Fourier
matrix is the transposed Vandermonde matrix of the distinct nodes `ω ^ c`, and on any set `C` of
columns its first `|C|` rows are linearly independent. Hence for a set `X` of `h = ⌊N/2⌋`
inputs and any set `Y` of outputs, `rank F[Yᶜ, X] + rank F[Y, Xᶜ] ≥ h`
(`le_blockRank_add_blockRank_dft`, and `le_blockRank_add_blockRank_vandermonde` for any
distinct nodes): the first block has rank at least the number of the first `h` rows outside
`Y`, and the second, with `N - h ≥ h` columns, at least the number of the first `h` rows in `Y`.
Along the ordering of `MultiOutput.exists_rank`, the prefix holding exactly `h` inputs is
crossed by at least `h` signals by the rank-cut bound, and by at most
`(A + η) (s - N)⁺ + O(log (N + s))` by the ordering bound (`half_le_of_dft`), so a circuit of
size `s` has `s ≥ (1 + 1/(2A) - ε) N`.

*Prior art.* Valiant (1975) observed that a linear circuit computing the Fourier transform is a
hyperconcentrator (`Multigraph.Hyperconcentrator`). For prime `N` all minors of the complex
Fourier matrix are nonsingular (Chebotarëv), so such circuits are superconcentrators, and Lev and
Valiant (*Size bounds for superconcentrators*, Theoretical Computer Science, 1983) derived
`4 N - o(N)` additions. For general `N`, including `N = 2^k`, Lokam (*Complexity lower bounds
using linear algebra*, 2009) and Ailon (arXiv:1403.1307) record no superlinear lower bound for
unrestricted linear circuits; the bound here is linear, with the constant `1 + κ/2 ≈ 2.78`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open Matrix Filter

variable {σ : Signature} {F : Type*} [Field F]

/-! ## Half cuts -/

/-- **Half cuts of Vandermonde matrices.** For distinct nodes `x c`, every set `X` of `h`
columns with `2 h ≤ N`, and every set `Y` of rows, the matrix `(x c ^ r)` satisfies
`h ≤ rank M[Yᶜ, X] + rank M[Y, Xᶜ]`. -/
theorem le_blockRank_add_blockRank_vandermonde {N : ℕ} {x : Fin N → F}
    (hx : Function.Injective x) {h : ℕ} (hh : 2 * h ≤ N) (Y X : Finset (Fin N))
    (hX : X.card = h) :
    h ≤ blockRank (vandermonde x)ᵀ Yᶜ X + blockRank (vandermonde x)ᵀ Y Xᶜ :=
  Internal.le_blockRank_add_blockRank hx hh Y X hX

/-- **Half cuts of the Fourier matrix.** For a primitive `N`-th root of unity `ω`, every set `X`
of `⌊N/2⌋` inputs and every set `Y` of outputs, `⌊N/2⌋ ≤ rank F[Yᶜ, X] + rank F[Y, Xᶜ]`. -/
theorem le_blockRank_add_blockRank_dft {N : ℕ} {ω : F} (hω : IsPrimitiveRoot ω N)
    (Y X : Finset (Fin N)) (hX : X.card = N / 2) :
    N / 2 ≤ blockRank (dft ω N) Yᶜ X + blockRank (dft ω N) Y Xᶜ :=
  Internal.le_blockRank_add_blockRank_dft hω Y X hX

/-! ## Finite bounds -/

/-- **The finite bound for the Fourier transform over a finite field.** If a circuit over a
finite field, over any signature with fan-in at most two, computes `x ↦ dft ω N x` for a
primitive `N`-th root of unity `ω`, then under the graph-ordering hypothesis
`⌊N/2⌋ ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C` for its size `s`. -/
theorem half_le_of_dft [Fintype F] [DecidableEq F] {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) {N : ℕ} {ω : F} (hω : IsPrimitiveRoot ω N)
    {I : Interpretation σ F} {c : Circuit σ N N} (hfan : c.FanInAtMost 2)
    (hc : c.Computes I fun x => dft ω N *ᵥ x) :
    ((N / 2 : ℕ) : ℝ) ≤ (A + η) * max ((c.size : ℝ) - N) 0 +
      3 * Real.logb 2 (N + 3 * c.size) + C :=
  Internal.half_le_of_dft hAη order c.program hfan c.outputs hω
    (blockRank_add_blockRank_le hc)

/-- **The finite bound for linear circuits computing the Fourier transform**, over any field. -/
theorem Linear.Realization.half_le_of_dft {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) {N s : ℕ} {p : Program σ N s}
    (r : Linear.Realization p F) (fan : p.FanInAtMost 2) (out : Fin N → Wire N s) {ω : F}
    (hω : IsPrimitiveRoot ω N) (rows : ∀ i, r.value (out i) = dft ω N i) :
    ((N / 2 : ℕ) : ℝ) ≤ (A + η) * max ((s : ℝ) - N) 0 + 3 * Real.logb 2 (N + 3 * s) + C :=
  Internal.half_le_of_dft hAη order p fan out hω (r.blockRank_add_blockRank_le out _ rows)

/-! ## Asymptotic bounds -/

universe u v

/-- The edge-score coefficient: `1/(2 · 2p) = κ/2` for `κ = π/(3 arccos((1 + 2√2)/4))`. -/
private theorem one_div_two_mul_frontier :
    1 / (2 * (2 * Gaussian.frontierCoefficient)) =
      Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) / 2 := by
  have := Gaussian.one_add_inv_two_mul_frontierCoefficient
  have hp := Gaussian.frontierCoefficient_pos
  rw [show 1 / (2 * (2 * Gaussian.frontierCoefficient)) =
    1 / (2 * Gaussian.frontierCoefficient) / 2 by field_simp]
  linarith

/-- The edge-score coefficient is at least `16/9`. -/
private theorem sixteen_div_nine_le_frontier :
    16 / 9 ≤ Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) / 2 := by
  have hp := mul_pos two_pos Gaussian.frontierCoefficient_pos
  have := one_div_le_one_div_of_le hp Gaussian.two_mul_frontierCoefficient_le
  rw [← one_div_two_mul_frontier, show 1 / (2 * (2 * Gaussian.frontierCoefficient)) =
    1 / (2 * Gaussian.frontierCoefficient) / 2 by field_simp]
  norm_num at this ⊢
  linarith

/-- **Linear circuits for the Fourier transform, general ordering coefficient.** If the
graph-ordering hypothesis holds with coefficient `A > 0` for every positive slack, then for every
`ε > 0` and all large `N`, every fan-in-two circuit over any field with a local linear
realization computing `x ↦ dft ω N x`, for a primitive `N`-th root of unity `ω`, has more than
`(1 + 1/(2A) - ε) N` gates. -/
theorem Linear.eventually_lt_size_dft_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Type u) [Field F] (ω : F), IsPrimitiveRoot ω N →
      ∀ (σ : Signature.{v}) (c : Circuit σ N N), c.FanInAtMost 2 →
        ∀ r : Linear.Realization c.program F, (∀ i, r.value (c.outputs i) = dft ω N i) →
          (1 + 1 / (2 * A) - ε) * N < c.size := by
  filter_upwards [Internal.eventually_lt_size_of_dft_rank_cuts.{u, v} hA order hε] with N hN
  intro F _ ω hω σ c hfan r rows
  exact hN F ω hω σ c hfan (r.blockRank_add_blockRank_le c.outputs _ rows)

/-- **Linear circuits for the Fourier transform need `(2.78 - ε) N` gates.** For every `ε > 0`
and all large `N`, every fan-in-two linear circuit over any field computing `x ↦ dft ω N x`, for
a primitive `N`-th root of unity `ω`, has more than `(1 + κ/2 - ε) N` gates, where
`κ = π/(3 arccos((1 + 2√2)/4)) ≈ 3.5625`. -/
theorem Linear.eventually_lt_size_dft {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Type u) [Field F] (ω : F), IsPrimitiveRoot ω N →
      ∀ (σ : Signature.{v}) (c : Circuit σ N N), c.FanInAtMost 2 →
        ∀ r : Linear.Realization c.program F, (∀ i, r.value (c.outputs i) = dft ω N i) →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) / 2 - ε) * N <
            c.size := by
  have key := Linear.eventually_lt_size_dft_of_orderingBound.{u, v}
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) Multigraph.exists_orderingBound_frontier hε
  rwa [one_div_two_mul_frontier] at key

/-- **Linear circuits for the Fourier transform need `(25/9 - ε) N` gates.** -/
theorem Linear.eventually_lt_size_dft_twentyFive_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Type u) [Field F] (ω : F), IsPrimitiveRoot ω N →
      ∀ (σ : Signature.{v}) (c : Circuit σ N N), c.FanInAtMost 2 →
        ∀ r : Linear.Realization c.program F, (∀ i, r.value (c.outputs i) = dft ω N i) →
          (25 / 9 - ε) * N < c.size := by
  filter_upwards [Linear.eventually_lt_size_dft.{u, v} hε] with N hN
  intro F _ ω hω σ c hfan r rows
  refine lt_of_le_of_lt ?_ (hN F ω hω σ c hfan r rows)
  exact mul_le_mul_of_nonneg_right (by linarith [sixteen_div_nine_le_frontier])
    (Nat.cast_nonneg N)

/-- **The complex DFT.** For every `ε > 0` and all large `N`, every fan-in-two linear circuit over
`ℂ` computing the `N`-point discrete Fourier transform `x ↦ (e^{2πi r c/N}) x` has more than
`(1 + κ/2 - ε) N` gates. -/
theorem Linear.eventually_lt_size_complexDFT {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (σ : Signature.{v}) (c : Circuit σ N N), c.FanInAtMost 2 →
      ∀ r : Linear.Realization c.program ℂ,
        (∀ i, r.value (c.outputs i) = dft (Complex.exp (2 * Real.pi * Complex.I / N)) N i) →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) / 2 - ε) * N <
            c.size := by
  filter_upwards [Linear.eventually_lt_size_dft.{0, v} hε, eventually_ge_atTop 1] with N hN hN1
  exact hN ℂ _ (Complex.isPrimitiveRoot_exp N (by omega))

/-- **The fast Fourier transform is near optimal up to its constant.** For every `ε > 0` and all
large `k`, every fan-in-two linear circuit over `ℂ` computing the `2^k`-point discrete Fourier
transform has more than `(1 + κ/2 - ε) 2^k` gates. -/
theorem Linear.eventually_lt_size_fft {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ (σ : Signature.{v}) (c : Circuit σ (2 ^ k) (2 ^ k)),
      c.FanInAtMost 2 → ∀ r : Linear.Realization c.program ℂ,
        (∀ i, r.value (c.outputs i) =
          dft (Complex.exp (2 * Real.pi * Complex.I / (2 ^ k : ℕ))) (2 ^ k) i) →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) / 2 - ε) *
            (2 ^ k : ℕ) < c.size :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)).eventually
    (Linear.eventually_lt_size_complexDFT.{v} hε)

/-- **Arbitrary gates over a finite field, general ordering coefficient.** If the graph-ordering
hypothesis holds with coefficient `A > 0` for every positive slack, then for every `ε > 0` and all
large `N`, every circuit over a finite field, over any signature with fan-in at most two, computing
`x ↦ dft ω N x` for a primitive `N`-th root of unity `ω`, has more than `(1 + 1/(2A) - ε) N`
gates. -/
theorem eventually_lt_size_dft_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F] (ω : F),
      IsPrimitiveRoot ω N → ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N N),
        c.FanInAtMost 2 → c.Computes I (fun x => dft ω N *ᵥ x) →
          (1 + 1 / (2 * A) - ε) * N < c.size := by
  filter_upwards [Internal.eventually_lt_size_of_dft_rank_cuts.{u, v} hA order hε] with N hN
  intro F _ _ _ ω hω σ I c hfan hc
  exact hN F ω hω σ c hfan (blockRank_add_blockRank_le hc)

/-- **The Fourier transform over a finite field needs `(2.78 - ε) N` gates.** For every `ε > 0`
and all large `N`, every circuit over a finite field, over any signature with fan-in at most two,
computing `x ↦ dft ω N x` for a primitive `N`-th root of unity `ω`, has more than
`(1 + κ/2 - ε) N` gates, where `κ = π/(3 arccos((1 + 2√2)/4)) ≈ 3.5625`. -/
theorem eventually_lt_size_dft {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F] (ω : F),
      IsPrimitiveRoot ω N → ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N N),
        c.FanInAtMost 2 → c.Computes I (fun x => dft ω N *ᵥ x) →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) / 2 - ε) * N <
            c.size := by
  have key := eventually_lt_size_dft_of_orderingBound.{u, v}
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) Multigraph.exists_orderingBound_frontier hε
  rwa [one_div_two_mul_frontier] at key

/-- **The Fourier transform over a finite field needs `(25/9 - ε) N` gates.** -/
theorem eventually_lt_size_dft_twentyFive_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F] (ω : F),
      IsPrimitiveRoot ω N → ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N N),
        c.FanInAtMost 2 → c.Computes I (fun x => dft ω N *ᵥ x) →
          (25 / 9 - ε) * N < c.size := by
  filter_upwards [eventually_lt_size_dft.{u, v} hε] with N hN
  intro F _ _ _ ω hω σ I c hfan hc
  refine lt_of_le_of_lt ?_ (hN F ω hω σ I c hfan hc)
  exact mul_le_mul_of_nonneg_right (by linarith [sixteen_div_nine_le_frontier])
    (Nat.cast_nonneg N)

/-- **Primitive roots for number-theoretic transforms.** For a prime `q` and `N ∣ q - 1`, `ZMod q`
contains a primitive `N`-th root of unity. -/
theorem exists_isPrimitiveRoot_zmod (q N : ℕ) [Fact q.Prime] (hN : N ∣ q - 1) :
    ∃ ω : ZMod q, IsPrimitiveRoot ω N := by
  have : NeZero (q - 1) := ⟨by have := (Fact.out : q.Prime).two_le; omega⟩
  have := HasEnoughRootsOfUnity.of_dvd (ZMod q) hN
  exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot (ZMod q) N

/-- **Number-theoretic transforms need `(2.78 - ε) N` gates.** For every `ε > 0` and all large
`N`, for every prime `q` and every primitive `N`-th root of unity `ω` in `ZMod q` (one exists
when `N ∣ q - 1`), every circuit over `ZMod q`, over any signature with fan-in at most two,
computing `x ↦ dft ω N x` has more than `(1 + κ/2 - ε) N` gates. -/
theorem eventually_lt_size_ntt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (q : ℕ) [Fact q.Prime] (ω : ZMod q), IsPrimitiveRoot ω N →
      ∀ (σ : Signature.{v}) (I : Interpretation σ (ZMod q)) (c : Circuit σ N N),
        c.FanInAtMost 2 → c.Computes I (fun x => dft ω N *ᵥ x) →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) / 2 - ε) * N <
            c.size := by
  filter_upwards [eventually_lt_size_dft.{0, v} hε] with N hN
  intro q _ ω hω σ I c hfan hc
  exact hN (ZMod q) ω hω σ I c hfan hc

end Algebraic.Cutwidth.MultiOutput
