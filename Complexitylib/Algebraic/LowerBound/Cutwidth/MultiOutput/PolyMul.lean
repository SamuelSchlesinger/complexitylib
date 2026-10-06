/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.PolyMul.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Taylor
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Quadratic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Arithmetic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.PolyMul.Internal

/-!
# Lower bounds for polynomial multiplication

Polynomial multiplication `polyMul n` maps the coefficients `x₀, …, x_{n-1}` and
`y₀, …, y_{n-1}` of two polynomials of degree below `n` (the first and the last `n` inputs) to
the `2n - 1` coefficients `z_m = ∑_{i + j = m} xᵢ yⱼ` of their product.

**The cut bound** (`min_add_min_le_of_polyMul`). Let a circuit with polynomial gates over any
field `K`, of any degree and arity, formally compute polynomial multiplication. Every split `S`
of its wires, holding the inputs `X_S` and leaving `X_T`, is crossed by at least
`min(|X_S ∩ x|, |X_T ∩ y|) + min(|X_S ∩ y|, |X_T ∩ x|)` signals. By the Hessian consequence of
the Taylor cut lemma (`Taylor.blockRank_hessian_le`), for all weights `μ` the block
`H[X_S, X_T]` of the Hessian of `∑ₘ μ m z_m` has rank at most the number of crossing signals;
this Hessian is `[[0, Λ], [Λᵀ, 0]]` for the Hankel matrix `Λ = (μ (i + j))`
(`sum_smul_hessian_polyMulPolynomial`). For the weights `μ m = t ^ (m²)` in the rational
functions `K(t)`, `Λ` is totally regular in every characteristic (`totallyRegular_genericHankel`):
in the expansion of a square minor with increasing rows and columns, the identity permutation
alone attains the largest degree, by the rearrangement inequality. So the two blocks of
`H[X_S, X_T]` have the full ranks `min(|X_S ∩ x|, |X_T ∩ y|)` and `min(|X_S ∩ y|, |X_T ∩ x|)`
(`min_add_min_le_blockRank_crossMatrix`). Over `ZMod q` for a prime `q > 2n`, the same bound holds
for **arbitrary** gate functions (`min_add_min_le_of_polyMul_zmod`): the weights
`μ m = 1 / (m + 2)` make `Λ` the Hankel Cauchy matrix, and the counting rank-cut bound
(`blockRank_add_transpose_le_of_sum`) applies to the quadratic form `∑ₘ μ m z_m = xᵀ Λ y`.

**The finite bound** (`le_of_polyMul`, `le_of_polyMul_zmod`). The component of the first input
is crossed by no signal, so the cut bound puts every input into it. Along the ranking of
`MultiOutput.exists_rank`, the prefix ending at a suitable input holds exactly `n` of the `2n`
inputs, `a` of the first factor and `n - a` of the second, so it is crossed by at least
`min(a, a) + min(n - a, n - a) = n` signals. With a graph-ordering hypothesis for coefficient
`A`, slack `η` and constant `C`, a fan-in-two circuit with `s` gates therefore has
`n ≤ (A + η) (s - 2n)⁺ + 3 log₂ (2n + 3 s) + C`.

**The asymptotic bound** (`eventually_lt_size_of_polyMul`). With the edge-score ordering
coefficient `A = 2 κ_E`, where `κ_E = Gaussian.frontierCoefficient ≈ 0.14035`, for every
`ε > 0` and all large `n`, every such circuit has more than `(2 + 1/(2 κ_E) - ε) n` gates, the
coefficient being `2 + π/(3 arccos((1 + 2√2)/4)) ≈ 5.5625`; as `2 κ_E ≤ 9/32`, also more than
`(50/9 - ε) n` gates. The threshold depends only on `ε`, not on the field, the signature or the
gate polynomials. The bound holds

* for formal computation with polynomial gates over every field (`eventually_lt_size_of_polyMul`),
* for computation of the polynomial function with polynomial gates over every infinite field
  (`eventually_lt_size_of_polyMul_of_infinite`),
* for the number of additions and multiplications of arithmetic circuits over every infinite
  field, with arbitrary constants free (`eventually_lt_arithmeticCost_of_polyMul`), and
* for circuits with arbitrary gates of fan-in at most two over `ZMod q` for every prime
  `q > 2n` (`eventually_lt_size_of_polyMul_zmod`).

Gate polynomials carry their coefficients, so in the first two statements only explicit nullary
gate occurrences are counted beyond the operations.

*Prior art.* Lower bounds for polynomial multiplication have counted multiplications:
Kaminski and Bshouty (*Multiplicative complexity of polynomial multiplication over finite
fields*, J. ACM 36, 1989) prove that bilinear algorithms over a fixed finite field need
`3n - o(n)` multiplications, while over fields with at least `2n - 2` elements `2n - 1`
multiplications suffice. Read as bounds on the total number of operations they give about
`4n`. The coefficient here is not claimed to be a record beyond this comparison.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open SingleCut Matrix Filter

variable {σ : Signature} {n : ℕ}

/-! ## Polynomial multiplication -/

/-- **Polynomial multiplication multiplies polynomials.** On the coefficients `x` and `y` of
`∑ᵢ xᵢ Xⁱ` and `∑ⱼ yⱼ Xʲ`, output `m` is the coefficient of `X ^ m` in their product. -/
theorem polyMul_append_eq_coeff {R : Type*} [CommSemiring R] (x y : Fin n → R)
    (m : Fin (2 * n - 1)) :
    polyMul n (Fin.append x y) m =
      ((∑ i : Fin n, Polynomial.C (x i) * Polynomial.X ^ (i : ℕ)) *
        ∑ j : Fin n, Polynomial.C (y j) * Polynomial.X ^ (j : ℕ)).coeff m :=
  PolyMul.Internal.polyMul_append_eq_coeff x y m

/-- Polynomial multiplication evaluates its polynomials. -/
theorem polyMul_eq_eval {K : Type*} [CommSemiring K] (z : Fin (n + n) → K)
    (m : Fin (2 * n - 1)) : polyMul n z m = MvPolynomial.eval z (polyMulPolynomial K n m) :=
  PolyMul.Internal.polyMul_eq_eval z m

/-- **The Hessian of a weighted sum of the outputs.** At every point, the Hessian of
`∑ₘ μ m z_m` is `[[0, Λ], [Λᵀ, 0]]` for the Hankel matrix `Λ = (μ (i + j))`. -/
theorem sum_smul_hessian_polyMulPolynomial {K L : Type*} [CommRing K] [Field L] [Algebra K L]
    (μ : ℕ → L) (a : Fin (n + n) → L) :
    ∑ m : Fin (2 * n - 1), μ m • Taylor.hessian (polyMulPolynomial K n m) a =
      crossMatrix (hankel n μ) :=
  PolyMul.Internal.sum_smul_hessian_polyMulPolynomial μ a

/-- **A generic totally regular Hankel matrix.** Over the rational functions `K(t)`, in every
characteristic, every square submatrix of the Hankel matrix `(t ^ ((i + j)²))` is
nonsingular. -/
theorem totallyRegular_genericHankel {K : Type*} [Field K] :
    TotallyRegular (hankel n fun m => (RatFunc.X : RatFunc K) ^ (m ^ 2)) :=
  PolyMul.Internal.totallyRegular_genericHankel

/-- **The blocks of `[[0, Λ], [Λᵀ, 0]]`.** If `Λ` is totally regular, the block with rows `X` and
columns `Xᶜ` has rank at least `min(|X ∩ x|, |Xᶜ ∩ y|) + min(|X ∩ y|, |Xᶜ ∩ x|)`. -/
theorem min_add_min_le_blockRank_crossMatrix {F : Type*} [Field F]
    {Λ : Matrix (Fin n) (Fin n) F} (hΛ : TotallyRegular Λ) (X : Finset (Fin (n + n))) :
    min (firstIn X).card (secondIn Xᶜ).card + min (secondIn X).card (firstIn Xᶜ).card ≤
      blockRank (crossMatrix Λ) X Xᶜ :=
  PolyMul.Internal.min_add_min_le_blockRank_crossMatrix hΛ X

/-! ## The cut bound -/

/-- **The cut bound for polynomial gates over any field.** If a circuit with polynomial gates
over a field `K` formally computes polynomial multiplication, every set `S` of its wires is
crossed by at least `min(|X_S ∩ x|, |X_T ∩ y|) + min(|X_S ∩ y|, |X_T ∩ x|)` forward and
backward signals, where `X_S` and `X_T` are the inputs in and outside `S`. -/
theorem min_add_min_le_of_polyMul {K : Type*} [Field K]
    (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K) {c : Circuit σ (n + n) (2 * n - 1)}
    (hc : Taylor.FormallyComputes P c (polyMulPolynomial K n)) (S : Finset (Wire (n + n) c.size)) :
    min (firstIn (inputsIn S)).card (secondIn (inputsIn S)ᶜ).card +
        min (secondIn (inputsIn S)).card (firstIn (inputsIn S)ᶜ).card ≤
      (forward c.program S).card + (backward c.program S).card :=
  PolyMul.Internal.min_add_min_le_of_formallyComputes P c.program c.outputs hc S

/-- **The cut bound over `ZMod q` for arbitrary gates.** If a circuit over `ZMod q`, for a prime
`q > 2n`, over any signature, computes polynomial multiplication, every set `S` of its wires is
crossed by at least `min(|X_S ∩ x|, |X_T ∩ y|) + min(|X_S ∩ y|, |X_T ∩ x|)` signals. -/
theorem min_add_min_le_of_polyMul_zmod (q : ℕ) [Fact q.Prime] (hq : 2 * n < q)
    {I : Interpretation σ (ZMod q)} {c : Circuit σ (n + n) (2 * n - 1)}
    (hc : c.Computes I (polyMul n)) (S : Finset (Wire (n + n) c.size)) :
    min (firstIn (inputsIn S)).card (secondIn (inputsIn S)ᶜ).card +
        min (secondIn (inputsIn S)).card (firstIn (inputsIn S)ᶜ).card ≤
      (forward c.program S).card + (backward c.program S).card :=
  PolyMul.Internal.min_add_min_le_of_computes_zmod q hq I c.program c.outputs
    (fun x m => congrFun (hc x) m) S

/-! ## The finite bound -/

/-- **The finite bound for polynomial gates over any field.** If a fan-in-two circuit with
polynomial gates over a field formally computes polynomial multiplication, then under the
graph-ordering hypothesis `n ≤ (A + η) (s - 2n)⁺ + 3 log₂ (2n + 3 s) + C` for its size `s`. -/
theorem le_of_polyMul {A η C : ℝ} (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C)
    {K : Type*} [Field K] (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
    {c : Circuit σ (n + n) (2 * n - 1)} (hfan : c.FanInAtMost 2)
    (hc : Taylor.FormallyComputes P c (polyMulPolynomial K n)) :
    (n : ℝ) ≤
      (A + η) * max ((c.size : ℝ) - 2 * n) 0 + 3 * Real.logb 2 (2 * n + 3 * c.size) + C :=
  PolyMul.Internal.le_of_cut hAη order c.program hfan (min_add_min_le_of_polyMul P hc)

/-- **The finite bound over `ZMod q` for arbitrary gates.** -/
theorem le_of_polyMul_zmod {A η C : ℝ} (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C)
    (q : ℕ) [Fact q.Prime] (hq : 2 * n < q) {I : Interpretation σ (ZMod q)}
    {c : Circuit σ (n + n) (2 * n - 1)} (hfan : c.FanInAtMost 2) (hc : c.Computes I (polyMul n)) :
    (n : ℝ) ≤
      (A + η) * max ((c.size : ℝ) - 2 * n) 0 + 3 * Real.logb 2 (2 * n + 3 * c.size) + C :=
  PolyMul.Internal.le_of_cut hAη order c.program hfan (min_add_min_le_of_polyMul_zmod q hq hc)

/-! ## Asymptotic bounds -/

universe u v

/-- **The asymptotic bound with a general ordering coefficient.** If the graph-ordering
hypothesis holds with coefficient `A > 0` for every positive slack, then for every `ε > 0` and
all large `n`, every fan-in-two circuit with polynomial gates over any field formally computing
polynomial multiplication of two polynomials with `n` coefficients has more than
`(2 + 1/A - ε) n` gates. -/
theorem eventually_lt_size_of_polyMul_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type u) [Field K] (σ : Signature.{v})
      (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K) (c : Circuit σ (n + n) (2 * n - 1)),
        c.FanInAtMost 2 → Taylor.FormallyComputes P c (polyMulPolynomial K n) →
          (2 + 1 / A - ε) * n < c.size := by
  filter_upwards [PolyMul.Internal.eventually_lt_of_le hA order hε] with n hn
  intro K _ σ P c hfan hc
  exact hn c.size fun η C hAη hC => le_of_polyMul hAη hC P hfan hc

/-- **Polynomial multiplication needs `(2 + 1/(2 κ_E) - ε) n` polynomial gates over every
field.** For every `ε > 0` and all large `n`, every circuit with polynomial gates of fan-in at
most two over any field, of any degree and with any coefficients, formally computing the
product of two polynomials with `n` coefficients has more than `(2 + 1/(2 κ_E) - ε) n` gates,
where `κ_E = Gaussian.frontierCoefficient`; the coefficient is
`2 + π/(3 arccos((1 + 2√2)/4)) ≈ 5.5625`. -/
theorem eventually_lt_size_of_polyMul {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type u) [Field K] (σ : Signature.{v})
      (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K) (c : Circuit σ (n + n) (2 * n - 1)),
        c.FanInAtMost 2 → Taylor.FormallyComputes P c (polyMulPolynomial K n) →
          (2 + 1 / (2 * Gaussian.frontierCoefficient) - ε) * n < c.size :=
  eventually_lt_size_of_polyMul_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) Multigraph.exists_orderingBound_frontier hε

/-- **Polynomial multiplication needs `(50/9 - ε) n` polynomial gates over every field.** -/
theorem eventually_lt_size_of_polyMul_fifty_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type u) [Field K] (σ : Signature.{v})
      (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K) (c : Circuit σ (n + n) (2 * n - 1)),
        c.FanInAtMost 2 → Taylor.FormallyComputes P c (polyMulPolynomial K n) →
          (50 / 9 - ε) * n < c.size := by
  have hcoef : (50 / 9 : ℝ) ≤ 2 + 1 / (2 * Gaussian.frontierCoefficient) := by
    have hpos : 0 < 2 * Gaussian.frontierCoefficient :=
      mul_pos two_pos Gaussian.frontierCoefficient_pos
    have := one_div_le_one_div_of_le hpos Gaussian.two_mul_frontierCoefficient_le
    norm_num at this ⊢
    linarith
  filter_upwards [eventually_lt_size_of_polyMul.{u, v} hε] with n hn
  intro K _ σ P c hfan hc
  refine lt_of_le_of_lt ?_ (hn K σ P c hfan hc)
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)

/-- **Polynomial multiplication over an infinite field.** For every `ε > 0` and all large `n`,
over every infinite field, every circuit whose operations are polynomial functions of at most
two arguments and which computes polynomial multiplication as a function has more than
`(2 + 1/(2 κ_E) - ε) n` gates. -/
theorem eventually_lt_size_of_polyMul_of_infinite {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type u) [Field K] [Infinite K] (σ : Signature.{v})
      (I : Interpretation σ K), Polynomial.IsPolynomial I →
      ∀ c : Circuit σ (n + n) (2 * n - 1), c.FanInAtMost 2 → c.Computes I (polyMul n) →
          (2 + 1 / (2 * Gaussian.frontierCoefficient) - ε) * n < c.size := by
  filter_upwards [eventually_lt_size_of_polyMul.{u, v} hε] with n hn
  intro K _ _ σ I hI c hfan hc
  refine hn K σ hI.gatePolynomial c hfan (Taylor.formallyComputes_of_computes hI fun x => ?_)
  funext m
  rw [hc x, polyMul_eq_eval]

/-- Every output of polynomial multiplication is a nonconstant function. -/
theorem polyMul_nonconstant {K : Type*} [Field K] (m : Fin (2 * n - 1)) :
    ∃ x y : Fin (n + n) → K, polyMul n x m ≠ polyMul n y m :=
  PolyMul.Internal.polyMul_nonconstant m

/-- **Arithmetic circuits with free constants.** For every `ε > 0` and all large `n`, over every
infinite field, every circuit of additions, multiplications and constants computing polynomial
multiplication performs more than `(2 + 1/(2 κ_E) - ε) n` additions and multiplications;
constants are free. -/
theorem eventually_lt_arithmeticCost_of_polyMul {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type u) [Field K] [Infinite K] (Kc : Type v) (constant : Kc → K)
      (c : Circuit (Arithmetic.signature Kc) (n + n) (2 * n - 1)),
        c.Computes (Arithmetic.interpretation constant) (polyMul n) →
          (2 + 1 / (2 * Gaussian.frontierCoefficient) - ε) * n <
            c.cost Arithmetic.gateCost := by
  filter_upwards [eventually_lt_size_of_polyMul_of_infinite.{u, u} hε, eventually_gt_atTop 0]
    with n bound hn
  intro K _ _ Kc constant c hc
  obtain ⟨d, size, fan, agrees⟩ := Polynomial.exists_polynomial_circuit_of_nonconstant
    (by omega : 0 < n + n) constant c fun m => by
      obtain ⟨x, y, hxy⟩ := polyMul_nonconstant (K := K) m
      exact ⟨x, y, by rwa [hc x, hc y]⟩
  have result := bound K (Polynomial.signature K) (Polynomial.interpretation K)
    Polynomial.isPolynomial_interpretation d fan fun x => (agrees x).trans (hc x)
  rwa [size] at result

/-- **Arbitrary gates over `ZMod q`.** For every `ε > 0` and all large `n`, for every prime
`q > 2n`, every circuit over `ZMod q`, over any signature with fan-in at most two (so with
arbitrary functions `ZMod q × ZMod q → ZMod q` as gates), computing polynomial multiplication
has more than `(2 + 1/(2 κ_E) - ε) n` gates. -/
theorem eventually_lt_size_of_polyMul_zmod {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : ℕ) [Fact q.Prime], 2 * n < q →
      ∀ (σ : Signature.{v}) (I : Interpretation σ (ZMod q)) (c : Circuit σ (n + n) (2 * n - 1)),
        c.FanInAtMost 2 → c.Computes I (polyMul n) →
          (2 + 1 / (2 * Gaussian.frontierCoefficient) - ε) * n < c.size := by
  filter_upwards [PolyMul.Internal.eventually_lt_of_le
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) Multigraph.exists_orderingBound_frontier hε]
    with n hn
  intro q _ hq σ I c hfan hc
  exact hn c.size fun η C hAη hC => le_of_polyMul_zmod hAη hC q hq hfan hc

end Algebraic.Cutwidth.MultiOutput
