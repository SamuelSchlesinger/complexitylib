/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Quadratic.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.TotallyRegular
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Ordering
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
public import Mathlib.Algebra.Field.ZMod
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Quadratic.Internal

/-!
# Lower bounds for quadratic forms

Let a circuit over a finite field `F`, over any signature whose gates have at most two arguments
(so any functions `F × F → F`, unary functions and constants are allowed, which covers arithmetic
circuits over `F`), compute the quadratic form `x ↦ xᵀ M x` (`quadForm`) of an `N × N` matrix
`M`, with one output. Write `H = M + Mᵀ`.

**The rank-cut bound** (`blockRank_add_transpose_le`). Split the wires into `S` and its
complement `T`, with forward signals `A`, backward signals `B`, and inputs `X_S` and `X_T` on
the two sides. Then `rank H[X_S, X_T] ≤ |A| + |B|`, wherever the output lies. The inputs with a
fixed boundary key form a product `P_S × P_T` of left and right parts (`SingleCut`). On such a
class the output depends on one side only (`SingleCut.trace_mix`), so the mixed second
difference `f(x_S, x_T) - f(x'_S, x_T) - f(x_S, x'_T) + f(x'_S, x'_T)` vanishes
(`trace_add_trace_eq_trace_mix_add_trace_mix`); for a quadratic form it is the cross term
`(x_S - x'_S)ᵀ H[X_S, X_T] (x_T - x'_T)` (`quadForm_add_quadForm_eq`). So the difference spaces
`D_S` and `D_T` of the two parts are orthogonal through `H[X_S, X_T]`, which forces
`dim D_S + dim D_T ≤ N - rank H[X_S, X_T]` (`card_mul_card_le_of_dotProduct_mulVec_eq_zero`,
via Sylvester's rank inequality). Every class thus has at most `|F| ^ (N - r)` inputs, and there
are at most `|F| ^ (|A| + |B|)` classes.

**The finite bound** (`half_le_of_quadForm`). If `H` is totally regular, then with the
graph-ordering hypothesis for coefficient `A`, slack `η` and constant `C`, a circuit of size `s`
has `⌊N/2⌋ ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C`. The component of an input wire is closed,
hence crossed by no signal, so the rank-cut bound and total regularity put every input into it
(`input_mem_component_of_quadForm`). Along the ranking of `MultiOutput.exists_rank`, the prefix
ending at a suitable input holds exactly `⌊N/2⌋` inputs, so it is crossed by at least
`rank H[X_S, X_T] ≥ min (⌊N/2⌋, ⌈N/2⌉) = ⌊N/2⌋` signals, and it is charged to the component
holding all `N` inputs.

**The asymptotic bound** (`eventually_lt_size_of_quadForm`). With the edge-score ordering
coefficient `A = 2 κ_E`, where `κ_E = Gaussian.frontierCoefficient ≈ 0.14035`, for every `ε > 0`
and all large `N`, every such circuit has more than `(1 + 1/(4 κ_E) - ε) N` gates, the
coefficient being `1 + π/(6 arccos((1 + 2√2)/4)) ≈ 2.7813`; as `2 κ_E ≤ 9/32`, also more than
`(25/9 - ε) N` gates (`eventually_lt_size_of_quadForm_twentyFive_div_nine`). The threshold
depends only on `ε`, not on the field, the matrix or the signature.

**An explicit family** (`eventually_lt_size_hankelCauchyZMod`). Over `ZMod q` for a prime
`q > 2 N`, the Hankel Cauchy matrix `hankelCauchyZMod q N` with entries `1 / (i + j + 2)` is the
Cauchy matrix with nodes `x i = i + 1` and `y j = -(j + 1)`, hence totally regular, and it is
symmetric; as `q` is odd, `H = 2 M` is totally regular too
(`totallyRegular_hankelCauchyZMod_add_transpose`). Every fan-in-two circuit over `ZMod q`
computing its quadratic form has more than `(25/9 - ε) N` gates for large `N`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open SingleCut Matrix Filter

variable {σ : Signature} {n s : Nat}

/-! ## The mixed second difference -/

/-- **The mixed second difference vanishes on a class.** If two inputs have the same boundary
key for a split `S`, the values of any wire at the two inputs sum to its values at the two
mixed inputs. -/
theorem trace_add_trace_eq_trace_mix_add_trace_mix {U : Type*} [AddCommMonoid U]
    (p : Program σ n s) (I : Interpretation σ U) {S : Finset (Wire n s)} {x x' : Fin n → U}
    (h : boundaryKey p I S x = boundaryKey p I S x') (w : Wire n s) :
    p.trace I x w + p.trace I x' w = p.trace I (mix S x x') w + p.trace I (mix S x' x) w :=
  Internal.trace_add_trace_eq_trace_mix_add_trace_mix p I h w

/-- **The mixed second difference of a quadratic form** is the cross term
`(x_S - x'_S)ᵀ (M + Mᵀ)[X_S, X_T] (x_T - x'_T)`. -/
theorem quadForm_add_quadForm_eq {F : Type*} [CommRing F] (M : Matrix (Fin n) (Fin n) F)
    (S : Finset (Wire n s)) (x x' : Fin n → F) :
    quadForm M x + quadForm M x' = quadForm M (mix S x x') + quadForm M (mix S x' x) +
      (leftPart S x - leftPart S x') ⬝ᵥ
        ((M + Mᵀ).submatrix (fun i : ↥(inputsIn S) => (i : Fin n))
          (fun j : ↥(inputsIn S)ᶜ => (j : Fin n)) *ᵥ (rightPart S x - rightPart S x')) :=
  Internal.quadForm_add_quadForm_eq M S x x'

/-! ## The rank-cut bound -/

section RankCut

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The product-class bound.** If `(l - l')ᵀ B (r - r') = 0` for all `l, l' ∈ L` and
`r, r' ∈ R`, then `|L| |R| ≤ |F| ^ (|ι| + |κ| - rank B)`. -/
theorem card_mul_card_le_of_dotProduct_mulVec_eq_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (B : Matrix ι κ F) (L : Finset (ι → F)) (R : Finset (κ → F))
    (h : ∀ l ∈ L, ∀ l' ∈ L, ∀ r ∈ R, ∀ r' ∈ R, (l - l') ⬝ᵥ (B *ᵥ (r - r')) = 0) :
    L.card * R.card ≤ Fintype.card F ^ (Fintype.card ι + Fintype.card κ - B.rank) :=
  Internal.card_mul_card_le_of_dotProduct_mulVec_eq_zero B L R h

/-- **The rank-cut bound for quadratic forms, for a program.** If the wire `out` of a program
carries the quadratic form of `M`, every split `S` has `rank (M + Mᵀ)[X_S, X_T] ≤ |A| + |B|`. -/
theorem blockRank_add_transpose_le_of_trace (p : Program σ n s) (I : Interpretation σ F)
    (out : Wire n s) (M : Matrix (Fin n) (Fin n) F) (hf : ∀ x, p.trace I x out = quadForm M x)
    (S : Finset (Wire n s)) :
    blockRank (M + Mᵀ) (inputsIn S) (inputsIn S)ᶜ ≤ (forward p S).card + (backward p S).card :=
  Internal.blockRank_add_transpose_le p I out M hf S

/-- **The rank-cut bound for quadratic forms.** If a circuit with values in a finite field, over
any signature, computes the quadratic form `x ↦ xᵀ M x`, then every set `S` of its wires has
`rank (M + Mᵀ)[X_S, X_T] ≤ |A| + |B|`, where `X_S` and `X_T` are the inputs in `S` and outside
`S`, and `A` and `B` the forward and backward signals of `S`. -/
theorem blockRank_add_transpose_le {c : Circuit σ n 1} {I : Interpretation σ F}
    {M : Matrix (Fin n) (Fin n) F} (hc : c.Computes I fun x _ => quadForm M x)
    (S : Finset (Wire n c.size)) :
    blockRank (M + Mᵀ) (inputsIn S) (inputsIn S)ᶜ ≤
      (forward c.program S).card + (backward c.program S).card :=
  Internal.blockRank_add_transpose_le c.program I (c.outputs 0) M (fun x => congrFun (hc x) 0) S

/-- **All inputs lie in one component.** If a circuit computes the quadratic form of `M` and
`M + Mᵀ` is totally regular, the component of any input wire contains every input. -/
theorem input_mem_component_of_quadForm {c : Circuit σ n 1} {I : Interpretation σ F}
    {M : Matrix (Fin n) (Fin n) F} (hM : TotallyRegular (M + Mᵀ))
    (hc : c.Computes I fun x _ => quadForm M x) (j j' : Fin n) :
    Wire.input j' ∈ component c.program (Wire.input j) :=
  Internal.input_mem_component_of_quadForm c.program I (c.outputs 0) hM
    (fun x => congrFun (hc x) 0) j j'

end RankCut

/-! ## Symmetric totally regular matrices -/

section Symmetric

variable {F : Type*} [Field F]

/-- **Doubling a symmetric totally regular matrix.** If `M` is symmetric and totally regular and
`2 ≠ 0` in `F`, then `M + Mᵀ = 2 M` is totally regular. -/
theorem totallyRegular_add_transpose {N : Nat} {M : Matrix (Fin N) (Fin N) F}
    (hM : TotallyRegular M) (hsymm : Mᵀ = M) (h2 : (2 : F) ≠ 0) : TotallyRegular (M + Mᵀ) :=
  Internal.totallyRegular_add_transpose hM hsymm h2

/-- The Hankel Cauchy matrix is the Cauchy matrix with nodes `x i = i + 1` and
`y j = -(j + 1)`. -/
theorem hankelCauchyZMod_eq_cauchy (q N : Nat) [Fact q.Prime] :
    hankelCauchyZMod q N =
      cauchy (fun i : Fin N => ((i : Nat) + 1 : ZMod q)) fun j => -((j : Nat) + 1 : ZMod q) :=
  Internal.hankelCauchyZMod_eq_cauchy q N

/-- **The Hankel Cauchy matrix is totally regular** over `ZMod q` for a prime `q > 2 N`. -/
theorem totallyRegular_hankelCauchyZMod (q N : Nat) [Fact q.Prime] (hq : 2 * N < q) :
    TotallyRegular (hankelCauchyZMod q N) :=
  Internal.totallyRegular_hankelCauchyZMod q N hq

/-- **The symmetrized Hankel Cauchy matrix is totally regular** over `ZMod q` for a prime
`q > 2 N`. -/
theorem totallyRegular_hankelCauchyZMod_add_transpose (q N : Nat) [Fact q.Prime]
    (hq : 2 * N < q) : TotallyRegular (hankelCauchyZMod q N + (hankelCauchyZMod q N)ᵀ) :=
  Internal.totallyRegular_hankelCauchyZMod_add_transpose q N hq

end Symmetric

/-! ## The finite bound -/

/-- **The finite bound for quadratic forms.** If a circuit over a finite field, over any
signature with fan-in at most two, computes the quadratic form of an `N × N` matrix `M` with
`M + Mᵀ` totally regular, then under the graph-ordering hypothesis
`⌊N/2⌋ ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C` for its size `s`. -/
theorem half_le_of_quadForm {F : Type*} [Field F] [Fintype F] [DecidableEq F] {A η C : ℝ}
    (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C) {N : Nat}
    {M : Matrix (Fin N) (Fin N) F} (hM : TotallyRegular (M + Mᵀ)) {I : Interpretation σ F}
    {c : Circuit σ N 1} (hfan : c.FanInAtMost 2) (hc : c.Computes I fun x _ => quadForm M x) :
    ((N / 2 : Nat) : ℝ) ≤
      (A + η) * max ((c.size : ℝ) - N) 0 + 3 * Real.logb 2 (N + 3 * c.size) + C :=
  Internal.half_le_of_quadForm hAη order c.program hfan I (c.outputs 0) hM
    fun x => congrFun (hc x) 0

/-! ## Asymptotic bounds -/

universe u v

/-- **The asymptotic bound with a general ordering coefficient.** If the graph-ordering
hypothesis holds with coefficient `A > 0` for every positive slack, then for every `ε > 0` and
all large `N`, every fan-in-two circuit over a finite field computing the quadratic form of an
`N × N` matrix `M` with `M + Mᵀ` totally regular has more than `(1 + 1/(2A) - ε) N` gates. -/
theorem eventually_lt_size_of_quadForm_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (M : Matrix (Fin N) (Fin N) F), TotallyRegular (M + Mᵀ) →
      ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N 1),
        c.FanInAtMost 2 → c.Computes I (fun x _ => quadForm M x) →
          (1 + 1 / (2 * A) - ε) * N < c.size :=
  Internal.eventually_lt_size_of_quadForm_of_orderingBound hA order hε

/-- **Quadratic forms need `(1 + 1/(4 κ_E) - ε) N` gates.** For every `ε > 0` and all large `N`,
every circuit over a finite field, over any signature with fan-in at most two, computing the
quadratic form of an `N × N` matrix `M` with `M + Mᵀ` totally regular has more than
`(1 + 1/(4 κ_E) - ε) N` gates, where `κ_E = Gaussian.frontierCoefficient`; the coefficient is
`1 + π/(6 arccos((1 + 2√2)/4)) ≈ 2.7813`. -/
theorem eventually_lt_size_of_quadForm {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (M : Matrix (Fin N) (Fin N) F), TotallyRegular (M + Mᵀ) →
      ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N 1),
        c.FanInAtMost 2 → c.Computes I (fun x _ => quadForm M x) →
          (1 + 1 / (4 * Gaussian.frontierCoefficient) - ε) * N < c.size := by
  have h := eventually_lt_size_of_quadForm_of_orderingBound.{u, v}
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) Multigraph.exists_orderingBound_frontier hε
  have h4 : 2 * (2 * Gaussian.frontierCoefficient) = 4 * Gaussian.frontierCoefficient := by ring
  rwa [h4] at h

/-- **Quadratic forms need `(25/9 - ε) N` gates.** -/
theorem eventually_lt_size_of_quadForm_twentyFive_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (M : Matrix (Fin N) (Fin N) F), TotallyRegular (M + Mᵀ) →
      ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N 1),
        c.FanInAtMost 2 → c.Computes I (fun x _ => quadForm M x) →
          (25 / 9 - ε) * N < c.size := by
  have hcoef : (25 / 9 : ℝ) ≤ 1 + 1 / (4 * Gaussian.frontierCoefficient) := by
    have hpos : 0 < 4 * Gaussian.frontierCoefficient :=
      mul_pos (by norm_num) Gaussian.frontierCoefficient_pos
    have h4 : 4 * Gaussian.frontierCoefficient ≤ 9 / 16 := by
      linarith [Gaussian.two_mul_frontierCoefficient_le]
    have := one_div_le_one_div_of_le hpos h4
    norm_num at this ⊢
    linarith
  filter_upwards [eventually_lt_size_of_quadForm.{u, v} hε] with N hN
  intro F _ _ _ M hM σ I c hfan hc
  refine lt_of_le_of_lt ?_ (hN F M hM σ I c hfan hc)
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg N)

/-- **The explicit family needs `(25/9 - ε) N` gates.** For every `ε > 0` and all large `N`,
for every prime `q > 2 N`, every circuit over `ZMod q`, over any signature with fan-in at most
two, computing the quadratic form `x ↦ xᵀ (1 / (i + j + 2)) x` of `hankelCauchyZMod q N` has
more than `(25/9 - ε) N` gates. -/
theorem eventually_lt_size_hankelCauchyZMod {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ (q : Nat) [Fact q.Prime], 2 * N < q →
      ∀ (σ : Signature.{v}) (I : Interpretation σ (ZMod q)) (c : Circuit σ N 1),
        c.FanInAtMost 2 → c.Computes I (fun x _ => quadForm (hankelCauchyZMod q N) x) →
          (25 / 9 - ε) * N < c.size := by
  filter_upwards [eventually_lt_size_of_quadForm_twentyFive_div_nine.{0, v} hε] with N hN
  intro q _ hq σ I c hfan hc
  exact hN (ZMod q) (hankelCauchyZMod q N) (totallyRegular_hankelCauchyZMod_add_transpose q N hq)
    σ I c hfan hc

end Algebraic.Cutwidth.MultiOutput
