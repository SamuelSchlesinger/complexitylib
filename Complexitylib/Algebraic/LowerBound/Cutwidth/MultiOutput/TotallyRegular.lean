/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
public import Mathlib.Algebra.Field.ZMod
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.TotallyRegular.Internal

/-!
# Lower bounds for totally regular linear maps

A matrix is *totally regular* when every square submatrix is nonsingular (`TotallyRegular`).
Let a circuit over a finite field `F`, over any signature whose gates have at most two arguments
(so any functions `F × F → F`, unary functions and constants are allowed), compute the linear
map `x ↦ M x` for a totally regular `N × N` matrix `M`.

**The finite bound** (`sub_one_le_of_totallyRegular`). With the graph-ordering hypothesis for
coefficient `A`, slack `η` and constant `C`, a circuit of size `s` has
`N - 1 ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C`.

The proof combines the two halves of the cut method. The ordering transfer
(`MultiOutput.exists_rank`) ranks the wires so that every prefix is crossed by few signals, and
the rank-cut bound (`MultiOutput.blockRank_add_blockRank_le`) shows that a prefix holding `N`
of the `2 N` inputs and outputs is crossed by at least
`rank M[Y_T, X_S] + rank M[Y_S, X_T] = |X_S| + |Y_S| = N` signals, since every block of a totally
regular matrix has full rank (`TotallyRegular.min_card_le_blockRank`). Inputs and outputs are
counted separately: an output carried by an input wire counts twice, and as distinct outputs
of a totally regular map lie on distinct wires the count grows by at most two per wire, so a
prefix with `N` or `N + 1` of them exists, which costs the `- 1`. All inputs and outputs lie in
one component of the wire graph (its component is closed, hence uncrossed, so the rank-cut bound
forces every input and output into it), and the prefix is charged to that component.

**The asymptotic bound** (`eventually_lt_size_of_totallyRegular`). With the edge-score ordering
coefficient `A = 2 κ_E`, where `κ_E = Gaussian.frontierCoefficient ≈ 0.14035`, for every
`ε > 0` and all large `N`, every such circuit has more than `(1 + 1/(2 κ_E) - ε) N` gates, the
coefficient being `1 + π/(3 arccos((1 + 2√2)/4)) ≈ 4.5625`; as `2 κ_E ≤ 9/32`, also more than
`(41/9 - ε) N` gates (`eventually_lt_size_of_totallyRegular_fortyOne_div_nine`). The threshold
depends only on `ε`, not on the field or the signature.

**Rectangular totally regular maps** (`sub_one_le_of_totallyRegular_rect`,
`eventually_lt_size_of_totallyRegular_rect`). When `M` is an `m × N` totally regular matrix with
`N ≤ m` (such as a systematic Reed–Solomon encoding matrix), distinct outputs still lie on
distinct wires for `N ≥ 2`. Peeling the last gate of the program and at most one output wire
seated on it `m - N` times reduces the circuit to one of size `s - (m - N)` computing an `N × N`
totally regular row-submatrix of `M`, yielding the finite bound
`N - 1 ≤ (A + η) (s - m)⁺ + 3 log₂ (N + 3 s) + C` and the asymptotic lower bound
`m + (1/(2 κ_E) - ε) N < s` (hence `m + (32/9 - ε) N < s`,
`eventually_lt_size_of_totallyRegular_rect_thirtyTwo_div_nine`).

**An explicit family** (`totallyRegular_cauchy`, `eventually_lt_size_cauchyZMod`). Cauchy
matrices `(1 / (x i - y j))` with distinct nodes are totally regular, as every square submatrix
is again a nonsingular Cauchy matrix. Over `ZMod q` for a prime `q ≥ 2 N`, the nodes `x i = i`
and `y j = N + j` give the explicit family `cauchyZMod q N`, and every fan-in-two circuit over
`ZMod q` computing it has more than `(41/9 - ε) N` gates for large `N` (by Bertrand's postulate
such a prime exists for every `N ≥ 1`).

*Prior art.* By a counting argument, the graph of a circuit computing a totally regular map is
a superconcentrator, whatever its gate functions (Valiant), and size lower bounds for
superconcentrators bound such circuits. The `5 N`-edge lower bound of Lev and Valiant for
superconcentrators is the edge-counting analogue of the cutwidth coefficient `κ = 1/6`, that
is, of the ordering coefficient `A = 1/3` (`Multigraph.exists_orderingBound_one_third`). Here
gates are counted, and the ordering coefficient is `2 κ_E ≈ 0.2807`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open Matrix Filter

variable {σ : Signature} {F : Type*} [Field F]

/-! ## Totally regular matrices -/

/-- **Blocks of a totally regular matrix have full rank**: every block has rank at least the
smaller of its dimensions. -/
theorem TotallyRegular.min_card_le_blockRank {m n : Nat} {M : Matrix (Fin m) (Fin n) F}
    (hM : TotallyRegular M) (Y : Finset (Fin m)) (X : Finset (Fin n)) :
    min Y.card X.card ≤ blockRank M Y X :=
  Internal.min_card_le_blockRank hM Y X

/-- **Row submatrices of a totally regular matrix are totally regular**: any injective selection
of rows of a totally regular matrix is totally regular. -/
theorem TotallyRegular.submatrix_rows {m m' n : Nat} {M : Matrix (Fin m) (Fin n) F}
    (hM : TotallyRegular M) {r : Fin m' → Fin m} (hr : Function.Injective r) :
    TotallyRegular (M.submatrix r id) :=
  Internal.TotallyRegular.submatrix_rows hM hr

/-- **Square Cauchy matrices are nonsingular.** -/
theorem det_cauchy_ne_zero {k : Nat} (x y : Fin k → F) (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) : (cauchy x y).det ≠ 0 :=
  Internal.det_cauchy_ne_zero x y hx hy hxy

/-- **Cauchy matrices are totally regular.** With distinct nodes `x i`, distinct nodes `y j`,
and `x i ≠ y j` for all `i` and `j`, every square submatrix of `(1 / (x i - y j))` is
nonsingular. -/
theorem totallyRegular_cauchy {m n : Nat} (x : Fin m → F) (y : Fin n → F)
    (hx : Function.Injective x) (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) :
    TotallyRegular (cauchy x y) :=
  Internal.totallyRegular_cauchy x y hx hy hxy

/-- **The explicit Cauchy family is totally regular** over `ZMod q` for a prime `q ≥ 2 N`. -/
theorem totallyRegular_cauchyZMod (q N : Nat) [Fact q.Prime] (hq : 2 * N ≤ q) :
    TotallyRegular (cauchyZMod q N) :=
  Internal.totallyRegular_cauchyZMod q N hq

/-! ## The finite bound -/

/-- **The finite bound for totally regular maps.** If a circuit over a finite field, over any
signature with fan-in at most two, computes a totally regular linear map on `N` inputs, then
under the graph-ordering hypothesis `N - 1 ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C` for its
size `s`. -/
theorem sub_one_le_of_totallyRegular [Fintype F] [DecidableEq F] {A η C : ℝ}
    (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C) {N : Nat}
    {M : Matrix (Fin N) (Fin N) F} (hM : TotallyRegular M) {I : Interpretation σ F}
    {c : Circuit σ N N} (hfan : c.FanInAtMost 2) (hc : c.Computes I fun x => M *ᵥ x) :
    (N : ℝ) - 1 ≤ (A + η) * max ((c.size : ℝ) - N) 0 + 3 * Real.logb 2 (N + 3 * c.size) + C :=
  Internal.sub_one_le_of_totallyRegular hAη order c.program hfan I c.outputs hM
    fun x i => congrFun (hc x) i

/-- **The finite bound for rectangular totally regular maps.** If a circuit over a finite field,
over any signature with fan-in at most two, computes an `m × N` totally regular linear map with
`N ≤ m`, then under the graph-ordering hypothesis
`N - 1 ≤ (A + η) (s - m)⁺ + 3 log₂ (N + 3 s) + C` for its size `s`. -/
theorem sub_one_le_of_totallyRegular_rect [Fintype F] [DecidableEq F] {A η C : ℝ}
    (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C) {N m : Nat} (hNm : N ≤ m)
    {M : Matrix (Fin m) (Fin N) F} (hM : TotallyRegular M) {I : Interpretation σ F}
    {c : Circuit σ N m} (hfan : c.FanInAtMost 2) (hc : c.Computes I fun x => M *ᵥ x) :
    (N : ℝ) - 1 ≤ (A + η) * max ((c.size : ℝ) - m) 0 + 3 * Real.logb 2 (N + 3 * c.size) + C :=
  Internal.sub_one_le_of_totallyRegular_rect hAη order hNm c.program hfan I c.outputs hM
    fun x i => congrFun (hc x) i

/-! ## Asymptotic bounds -/

universe u v

/-- **The asymptotic bound with a general ordering coefficient.** If the graph-ordering
hypothesis holds with coefficient `A > 0` for every positive slack, then for every `ε > 0` and
all large `N`, every fan-in-two circuit over a finite field computing a totally regular map on
`N` inputs has more than `(1 + 1/A - ε) N` gates. -/
theorem eventually_lt_size_of_totallyRegular_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (M : Matrix (Fin N) (Fin N) F), TotallyRegular M →
      ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N N),
        c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) →
          (1 + 1 / A - ε) * N < c.size :=
  Internal.eventually_lt_size_of_orderingBound hA order hε

/-- **Totally regular maps need `(1 + 1/(2 κ_E) - ε) N` gates.** For every `ε > 0` and all large
`N`, every circuit over a finite field, over any signature with fan-in at most two, computing a
totally regular linear map on `N` inputs has more than `(1 + 1/(2 κ_E) - ε) N` gates, where
`κ_E = Gaussian.frontierCoefficient`; the coefficient is
`1 + π/(3 arccos((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem eventually_lt_size_of_totallyRegular {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (M : Matrix (Fin N) (Fin N) F), TotallyRegular M →
      ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N N),
        c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) →
          (1 + 1 / (2 * Gaussian.frontierCoefficient) - ε) * N < c.size :=
  eventually_lt_size_of_totallyRegular_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) Multigraph.exists_orderingBound_frontier hε

/-- **Totally regular maps need `(41/9 - ε) N` gates.** -/
theorem eventually_lt_size_of_totallyRegular_fortyOne_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (M : Matrix (Fin N) (Fin N) F), TotallyRegular M →
      ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N N),
        c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) →
          (41 / 9 - ε) * N < c.size := by
  have hcoef : (41 / 9 : ℝ) ≤ 1 + 1 / (2 * Gaussian.frontierCoefficient) := by
    have hpos : 0 < 2 * Gaussian.frontierCoefficient :=
      mul_pos two_pos Gaussian.frontierCoefficient_pos
    have := one_div_le_one_div_of_le hpos Gaussian.two_mul_frontierCoefficient_le
    norm_num at this ⊢
    linarith
  filter_upwards [eventually_lt_size_of_totallyRegular.{u, v} hε] with N hN
  intro F _ _ _ M hM σ I c hfan hc
  refine lt_of_le_of_lt ?_ (hN F M hM σ I c hfan hc)
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg N)

/-- **The asymptotic bound for rectangular totally regular maps with a general ordering
coefficient.** If the graph-ordering hypothesis holds with coefficient `A > 0` for every
positive slack, then for every `ε > 0` and all large `N`, for every `m ≥ N`, every fan-in-two
circuit over a finite field computing an `m × N` totally regular map has more than
`m + (1/A - ε) N` gates. -/
theorem eventually_lt_size_of_totallyRegular_rect_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ {m : Nat}, N ≤ m →
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (M : Matrix (Fin m) (Fin N) F), TotallyRegular M →
        ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N m),
          c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) →
            (m : ℝ) + (1 / A - ε) * N < c.size :=
  Internal.eventually_lt_size_of_orderingBound_rect hA order hε

/-- **Rectangular totally regular maps need `m + (1/(2 κ_E) - ε) N` gates.** For every `ε > 0`
and all large `N`, for every `m ≥ N`, every circuit over a finite field, over any signature with
fan-in at most two, computing an `m × N` totally regular linear map has more than
`m + (1/(2 κ_E) - ε) N` gates, where `κ_E = Gaussian.frontierCoefficient`. -/
theorem eventually_lt_size_of_totallyRegular_rect {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ {m : Nat}, N ≤ m →
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (M : Matrix (Fin m) (Fin N) F), TotallyRegular M →
        ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N m),
          c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) →
            (m : ℝ) + (1 / (2 * Gaussian.frontierCoefficient) - ε) * N < c.size :=
  eventually_lt_size_of_totallyRegular_rect_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) Multigraph.exists_orderingBound_frontier hε

/-- **Rectangular totally regular maps need `m + (32/9 - ε) N` gates.** -/
theorem eventually_lt_size_of_totallyRegular_rect_thirtyTwo_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ {m : Nat}, N ≤ m →
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (M : Matrix (Fin m) (Fin N) F), TotallyRegular M →
        ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N m),
          c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) →
            (m : ℝ) + (32 / 9 - ε) * N < c.size := by
  have hcoef : (32 / 9 : ℝ) ≤ 1 / (2 * Gaussian.frontierCoefficient) := by
    have hpos : 0 < 2 * Gaussian.frontierCoefficient :=
      mul_pos two_pos Gaussian.frontierCoefficient_pos
    have := one_div_le_one_div_of_le hpos Gaussian.two_mul_frontierCoefficient_le
    norm_num at this ⊢
    linarith
  filter_upwards [eventually_lt_size_of_totallyRegular_rect.{u, v} hε] with N hN
  intro m hNm F _ _ _ M hM σ I c hfan hc
  refine lt_of_le_of_lt ?_ (hN hNm F M hM σ I c hfan hc)
  have : (32 / 9 - ε) * (N : ℝ) ≤ (1 / (2 * Gaussian.frontierCoefficient) - ε) * N :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg N)
  linarith

/-- **The explicit family needs `(41/9 - ε) N` gates.** For every `ε > 0` and all large `N`,
for every prime `q ≥ 2 N`, every circuit over `ZMod q`, over any signature with fan-in at most
two, computing `x ↦ cauchyZMod q N x` has more than `(41/9 - ε) N` gates. -/
theorem eventually_lt_size_cauchyZMod {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ (q : Nat) [Fact q.Prime], 2 * N ≤ q →
      ∀ (σ : Signature.{v}) (I : Interpretation σ (ZMod q)) (c : Circuit σ N N),
        c.FanInAtMost 2 → c.Computes I (fun x => cauchyZMod q N *ᵥ x) →
          (41 / 9 - ε) * N < c.size := by
  filter_upwards [eventually_lt_size_of_totallyRegular_fortyOne_div_nine.{0, v} hε] with N hN
  intro q _ hq σ I c hfan hc
  exact hN (ZMod q) (cauchyZMod q N) (totallyRegular_cauchyZMod q N hq) σ I c hfan hc

end Algebraic.Cutwidth.MultiOutput
