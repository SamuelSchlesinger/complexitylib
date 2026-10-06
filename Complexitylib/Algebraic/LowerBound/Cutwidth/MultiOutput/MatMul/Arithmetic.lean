/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Arithmetic.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Taylor
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Arithmetic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Arithmetic.Internal

/-!
# Arithmetic circuits for matrix multiplication

Let `matMulPolynomial K n` be the `n²` outputs `C i k = ∑ j, A i j B j k` of the product of two
`n × n` matrices, as polynomials in the `2 n²` inputs with coefficients in a field `K`
(`MatMul.Arithmetic.Defs`). Consider circuits whose gates are polynomials with coefficients in
`K`, of any degree and arity, that formally compute matrix multiplication
(`Taylor.FormallyComputes`): every output wire carries the polynomial `C i k`. The size bounds
are for circuits of fan-in at most two. The size counts gates; inputs and output designations
are free, and gate polynomials carry their coefficients, so only explicit nullary gate
occurrences are counted beyond the operations. For circuits of additions, multiplications and
constants (`Arithmetic.signature`) the cost counts the additions and multiplications, and
constants are free.

**The cut bounds** (`charges_le_of_matMul_formal`). Let a split `S` of the wires be crossed by
`w` forward and backward signals, and place the terminals as in `MatMul.Tripartite`, with
heavy vertices `H_I`, `H_J`, `H_K`. By the Taylor cut lemma (`MultiOutput.Taylor`):
* the Hessian of `∑ Λ i k C i k` is block diagonal over the inner index `j`; for a totally
  regular `Λ` its cross block has rank at least `R_J = ∑ j, min (d j, 2 n - d j)`, so
  `R_J ≤ w`;
* the Jacobian of the product at `(A₀, B₀)` sends `(δA, δB)` to `δA B₀ + A₀ δB`. Its forward
  block (outputs outside `S`, inputs in `S`) and backward block (outputs in `S`, inputs outside
  `S`) have ranks summing to at most `w`. With totally regular `A₀ = B₀`, group the forward block
  by the heavy rows `i` (against the inputs `A i j`) and then by the columns `k` (against the
  inputs `B j k`, with the light rows); the outputs of a light row do not depend on the `A`
  entries of another row, so the groups are triangular and the rank is at least
  `∑_{i ∈ H_I} min (#{k : C i k ∉ S}, #{j : A i j ∈ S}) +
    ∑_k min (#{i ∉ H_I : C i k ∉ S}, #{j : B j k ∈ S})`. The backward block, grouped by the light
  rows, gives the complementary sum; together they form the row Jacobian charge
  `L_I = jacobianChargeI`, and `L_I ≤ w`. Grouping by columns gives `L_K ≤ w`.

Over every field `K`, the Hankel matrix `(t ^ ((i + j)²))` over `K(t)` is totally regular
(`totallyRegular_genericHankel`), and the Taylor cut lemma holds over `K(t)`.

**The charging inequality** (`Tripartite.fifteen_mul_sq_le_eight_mul_charge`). Charge every
terminal with one heavy and one light endpoint as in `MatMul.Tripartite`. Then `R_J` pays for the
`A` and `B` terminals charged to `J`; `L_I` pays for every light–heavy `C` terminal and for the
`B` terminals charged to `K`, up to the overshoot `h_K (n - h_I - h_J)⁺ + (n - h_K) (h_I + h_J -
n)⁺`; `L_K` symmetrically. With `h_p = n/2 + U_p` and `δ = ∑ U_p`, the total is at least
`(15/8) n² - n δ/2 - δ²/2`, so at the threshold prefix, where `0 ≤ 2 δ ≤ 3`,
`15 n² ≤ 8 (R_J + L_I + L_K) + 6 n + 9`.

**The finite bound** (`fifteen_mul_sq_sub_le_of_matMul_formal`). All terminals lie in one
component, so under the graph-ordering hypothesis a fan-in-two circuit of size `s` has
`(15 n² - 6 n - 9)/24 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C`.

**The asymptotic bounds** (`eventually_lt_size_of_matMul_formal`). With the edge-score ordering
coefficient `A = 2 κ_E`, where `κ_E = Gaussian.frontierCoefficient ≈ 0.14035`, for every
`ε > 0` and all large `n`, every such circuit over every field has more than
`(2 + 5/(16 κ_E) - ε) n² ≈ (4.2266 - ε) n²` gates; as `2 κ_E ≤ 9/32`, also more than
`(38/9 - ε) n²` gates (`eventually_lt_size_of_matMul_formal_thirtyEight_div_nine`). The
threshold depends only on `ε`. The bound holds

* for formal computation with polynomial gates over every field
  (`eventually_lt_size_of_matMul_formal`),
* for computation of the product as a function with polynomial gates over every infinite field
  (`eventually_lt_size_of_matMul_of_infinite_jacobian`), and
* for the number of additions and multiplications of arithmetic circuits, with arbitrary
  constants free, computing the product over every infinite field
  (`eventually_lt_arithmeticCost_of_matMul_jacobian`) or formally computing the polynomials over every
  field (`eventually_lt_arithmeticCost_of_matMul_formal_jacobian`,
  `eventually_lt_arithmeticCost_of_matMul_formal_thirtyEight_div_nine`).

*Prior art.* Bläser (*A 5/2 n²-lower bound for the multiplicative complexity of
n × n-matrix multiplication*, STACS 2001) proves that `5/2 n² - 3 n` multiplications are needed
over every field; counting about `n²` further gates for the outputs, this is about `3.5 n²`
operations in total. Shpilka (*Lower bounds for matrix product*, SICOMP 2003) proves
`3 n² - o(n²)` product gates over `GF(2)` for quadratic circuits, about `4 n²` operations with
the outputs. The bound here counts all gates of circuits with arbitrary fan-in-two polynomial
gates, and the additions and multiplications of arithmetic circuits.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open SingleCut Tripartite Filter

variable {σ : Signature} {n : Nat}

/-! ## The polynomials -/

/-- **The polynomials of matrix multiplication evaluate to the product**, over every
commutative algebra. -/
theorem aeval_matMulPolynomial {K A : Type*} [CommSemiring K] [CommSemiring A] [Algebra K A]
    (z : Fin (n * n + n * n) → A) (o : Fin (n * n)) :
    MvPolynomial.aeval z (matMulPolynomial K n o) = matMul n z o :=
  MatMul.ArithmeticInternal.aeval_matMulPolynomial z o

/-- The polynomials of matrix multiplication evaluate to the product. -/
theorem eval_matMulPolynomial {K : Type*} [CommSemiring K] (z : Fin (n * n + n * n) → K)
    (o : Fin (n * n)) : MvPolynomial.eval z (matMulPolynomial K n o) = matMul n z o :=
  MatMul.ArithmeticInternal.eval_matMulPolynomial z o

/-! ## The charging inequality -/

/-- **The charging inequality with the Jacobian charges.** If the heavy vertices number `h` with
`3 n ≤ 2 h ≤ 3 n + 3`, then `15 n² ≤ 8 (R_J + L_I + L_K) + 6 n + 9`. -/
theorem Tripartite.fifteen_mul_sq_le_eight_mul_charge (a b c : Finset (Fin n × Fin n))
    (hlo : 3 * n ≤ 2 * heavyCount a b c) (hhi : 2 * heavyCount a b c ≤ 3 * n + 3) :
    15 * n ^ 2 ≤
      8 * (chargeJ a b + jacobianChargeI a b c + jacobianChargeK a b c) + 6 * n + 9 :=
  MatMul.ArithmeticInternal.fifteen_mul_sq_le a b c hlo hhi

/-! ## The cut bounds -/

section Formal

variable {K : Type*} [Field K] (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
  {c : Circuit σ (n * n + n * n) (n * n)}

/-- **The cut bounds.** If a circuit with polynomial gates over a field `K` formally computes
matrix multiplication, then for every set `S` of its wires each of the Hessian charge `R_J` and
the Jacobian charges `L_I` and `L_K` of the placed terminals is at most the number of forward
and backward signals of `S`. -/
theorem charges_le_of_matMul_formal (hc : Taylor.FormallyComputes P c (matMulPolynomial K n))
    (S : Finset (Wire (n * n + n * n) c.size)) :
    chargeJ (place (matMulTermA n c.size) S) (place (matMulTermB n c.size) S) ≤
        (forward c.program S).card + (backward c.program S).card ∧
      jacobianChargeI (place (matMulTermA n c.size) S) (place (matMulTermB n c.size) S)
          (place (matMulTermC c.outputs) S) ≤
        (forward c.program S).card + (backward c.program S).card ∧
      jacobianChargeK (place (matMulTermA n c.size) S) (place (matMulTermB n c.size) S)
          (place (matMulTermC c.outputs) S) ≤
        (forward c.program S).card + (backward c.program S).card :=
  ⟨MatMul.ArithmeticInternal.chargeJ_le_of_formal P hc S,
    MatMul.ArithmeticInternal.jacobianChargeI_le_of_formal P hc S,
    MatMul.ArithmeticInternal.jacobianChargeK_le_of_formal P hc S⟩

/-- **All terminals lie in one component.** If a circuit with polynomial gates formally computes
matrix multiplication and `n ≥ 1`, the component of its output `C 0 0` contains every input and
every output. -/
theorem mem_component_of_matMul_formal (hc : Taylor.FormallyComputes P c (matMulPolynomial K n))
    (hn : 0 < n) :
    (∀ x, Wire.input x ∈ component c.program (c.outputs (matMulOutput n ⟨0, hn⟩ ⟨0, hn⟩))) ∧
      ∀ o, c.outputs o ∈ component c.program (c.outputs (matMulOutput n ⟨0, hn⟩ ⟨0, hn⟩)) :=
  MatMul.ArithmeticInternal.mem_component_of_formal P hn hc

/-- **The finite bound.** If a fan-in-two circuit with polynomial gates over a field formally
computes matrix multiplication, then under the graph-ordering hypothesis
`(15 n² - 6 n - 9)/24 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C` for its size `s`. -/
theorem fifteen_mul_sq_sub_le_of_matMul_formal {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) (hfan : c.FanInAtMost 2)
    (hc : Taylor.FormallyComputes P c (matMulPolynomial K n)) :
    (15 * (n : ℝ) ^ 2 - 6 * n - 9) / 24 ≤ (A + η) * max ((c.size : ℝ) - 2 * n ^ 2) 0 +
      3 * Real.logb 2 (2 * n ^ 2 + 3 * c.size) + C :=
  MatMul.ArithmeticInternal.fifteen_mul_sq_sub_le hAη order P c.program hfan c.outputs hc

end Formal

/-! ## Asymptotic bounds -/

universe u v

/-- **The asymptotic bound with a general ordering coefficient.** If the graph-ordering
hypothesis holds with coefficient `A > 0` for every positive slack, then for every `ε > 0` and
all large `n`, every fan-in-two circuit with polynomial gates over any field formally computing
the product of two `n × n` matrices has more than `(2 + 5/(8 A) - ε) n²` gates. -/
theorem eventually_lt_size_of_matMul_formal_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] (σ : Signature.{v})
      (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
      (c : Circuit σ (n * n + n * n) (n * n)),
        c.FanInAtMost 2 → Taylor.FormallyComputes P c (matMulPolynomial K n) →
          (2 + 5 / (8 * A) - ε) * n ^ 2 < c.size := by
  filter_upwards [MatMul.ArithmeticInternal.eventually_lt_of_le hA order hε] with n hn
  intro K _ σ P c hfan hc
  exact hn c.size fun η C hAη hC => fifteen_mul_sq_sub_le_of_matMul_formal P hAη hC hfan hc

/-- **Matrix multiplication needs `(2 + 5/(16 κ_E) - ε) n²` polynomial gates over every field.**
For every `ε > 0` and all large `n`, every circuit with polynomial gates of fan-in at most two
over any field, of any degree and with any coefficients, formally computing the product of two
`n × n` matrices has more than `(2 + 5/(16 κ_E) - ε) n²` gates, where
`κ_E = Gaussian.frontierCoefficient`; the coefficient is
`2 + 5 π/(24 arccos((1 + 2√2)/4)) ≈ 4.2266`. -/
theorem eventually_lt_size_of_matMul_formal {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] (σ : Signature.{v})
      (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
      (c : Circuit σ (n * n + n * n) (n * n)),
        c.FanInAtMost 2 → Taylor.FormallyComputes P c (matMulPolynomial K n) →
          (2 + 5 / (16 * Gaussian.frontierCoefficient) - ε) * n ^ 2 < c.size := by
  have h := eventually_lt_size_of_matMul_formal_of_orderingBound.{u, v}
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) Multigraph.exists_orderingBound_frontier hε
  have h8 : 8 * (2 * Gaussian.frontierCoefficient) = 16 * Gaussian.frontierCoefficient := by ring
  rwa [h8] at h

/-- `38/9 ≤ 2 + 5/(16 κ_E)`, since `2 κ_E ≤ 9/32`. -/
theorem thirtyEight_div_nine_le_two_add_five_div :
    (38 / 9 : ℝ) ≤ 2 + 5 / (16 * Gaussian.frontierCoefficient) := by
  have hpos : 0 < 16 * Gaussian.frontierCoefficient :=
    mul_pos (by norm_num) Gaussian.frontierCoefficient_pos
  have h16 : 16 * Gaussian.frontierCoefficient ≤ 9 / 4 := by
    linarith [Gaussian.two_mul_frontierCoefficient_le]
  have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 5) hpos h16
  norm_num at this ⊢
  linarith

/-- **Matrix multiplication needs `(38/9 - ε) n²` polynomial gates over every field.** -/
theorem eventually_lt_size_of_matMul_formal_thirtyEight_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] (σ : Signature.{v})
      (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
      (c : Circuit σ (n * n + n * n) (n * n)),
        c.FanInAtMost 2 → Taylor.FormallyComputes P c (matMulPolynomial K n) →
          (38 / 9 - ε) * n ^ 2 < c.size := by
  filter_upwards [eventually_lt_size_of_matMul_formal.{u, v} hε] with n hn
  intro K _ σ P c hfan hc
  refine lt_of_le_of_lt ?_ (hn K σ P c hfan hc)
  exact mul_le_mul_of_nonneg_right (by linarith [thirtyEight_div_nine_le_two_add_five_div])
    (by positivity)

/-- **Matrix multiplication over an infinite field.** For every `ε > 0` and all large `n`, over
every infinite field, every circuit whose operations are polynomial functions of at most two
arguments and which computes the product of two `n × n` matrices as a function has more than
`(2 + 5/(16 κ_E) - ε) n²` gates. -/
theorem eventually_lt_size_of_matMul_of_infinite_jacobian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] [Infinite K] (σ : Signature.{v})
      (I : Interpretation σ K), Polynomial.IsPolynomial I →
      ∀ c : Circuit σ (n * n + n * n) (n * n), c.FanInAtMost 2 → c.Computes I (matMul n) →
        (2 + 5 / (16 * Gaussian.frontierCoefficient) - ε) * n ^ 2 < c.size := by
  filter_upwards [eventually_lt_size_of_matMul_formal.{u, v} hε] with n hn
  intro K _ _ σ I hI c hfan hc
  refine hn K σ hI.gatePolynomial c hfan (Taylor.formallyComputes_of_computes hI fun x => ?_)
  funext o
  rw [hc x]
  exact (eval_matMulPolynomial x o).symm

/-- **Arithmetic circuits with free constants.** For every `ε > 0` and all large `n`, over every
infinite field, every circuit of additions, multiplications and constants computing the product
of two `n × n` matrices performs more than `(2 + 5/(16 κ_E) - ε) n²` additions and
multiplications; constants are free. -/
theorem eventually_lt_arithmeticCost_of_matMul_jacobian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] [Infinite K] (Kc : Type v) (constant : Kc → K)
      (c : Circuit (Arithmetic.signature Kc) (n * n + n * n) (n * n)),
        c.Computes (Arithmetic.interpretation constant) (matMul n) →
          (2 + 5 / (16 * Gaussian.frontierCoefficient) - ε) * n ^ 2 <
            c.cost Arithmetic.gateCost := by
  filter_upwards [eventually_lt_size_of_matMul_of_infinite_jacobian.{u, u} hε, eventually_gt_atTop 0]
    with n bound hn
  intro K _ _ Kc constant c hc
  obtain ⟨d, size, fan, agrees⟩ := Polynomial.exists_polynomial_circuit_of_nonconstant
    (by positivity : 0 < n * n + n * n) constant c fun o => by
      obtain ⟨x, y, hxy⟩ := matMul_nonconstant (K := K) o
      exact ⟨x, y, by rwa [hc x, hc y]⟩
  have result := bound K (Polynomial.signature K) (Polynomial.interpretation K)
    Polynomial.isPolynomial_interpretation d fan fun x => (agrees x).trans (hc x)
  rwa [size] at result

/-- **Arithmetic circuits with free constants over every field.** For every `ε > 0` and all
large `n`, over every field `K`, every circuit of additions, multiplications and constants of
`K` formally computing the product of two `n × n` matrices performs more than
`(2 + 5/(16 κ_E) - ε) n²` additions and multiplications; constants are free. The circuit run
over the infinite field `K(t)` computes the product there. -/
theorem eventually_lt_arithmeticCost_of_matMul_formal_jacobian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] (Kc : Type v) (constant : Kc → K)
      (c : Circuit (Arithmetic.signature Kc) (n * n + n * n) (n * n)),
        Taylor.FormallyComputes (Taylor.arithmeticPolynomial constant) c
            (matMulPolynomial K n) →
          (2 + 5 / (16 * Gaussian.frontierCoefficient) - ε) * n ^ 2 <
            c.cost Arithmetic.gateCost := by
  filter_upwards [eventually_lt_arithmeticCost_of_matMul_jacobian.{u, v} hε] with n bound
  intro K _ Kc constant c hc
  have : Infinite (RatFunc K) :=
    Infinite.of_injective _ (RatFunc.algebraMap_injective K)
  refine bound (RatFunc K) Kc (fun k => algebraMap K (RatFunc K) (constant k)) c fun x => ?_
  have h := hc.computes (RatFunc K)
  rw [Taylor.algebraInterpretation_arithmeticPolynomial] at h
  rw [h x]
  funext o
  exact aeval_matMulPolynomial x o

/-- **Arithmetic circuits for matrix multiplication need `(38/9 - ε) n²` operations over every
field**, constants free. -/
theorem eventually_lt_arithmeticCost_of_matMul_formal_thirtyEight_div_nine {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] (Kc : Type v) (constant : Kc → K)
      (c : Circuit (Arithmetic.signature Kc) (n * n + n * n) (n * n)),
        Taylor.FormallyComputes (Taylor.arithmeticPolynomial constant) c
            (matMulPolynomial K n) →
          (38 / 9 - ε) * n ^ 2 < c.cost Arithmetic.gateCost := by
  filter_upwards [eventually_lt_arithmeticCost_of_matMul_formal_jacobian.{u, v} hε] with n hn
  intro K _ Kc constant c hc
  refine lt_of_le_of_lt ?_ (hn K Kc constant c hc)
  exact mul_le_mul_of_nonneg_right (by linarith [thirtyEight_div_nine_le_two_add_five_div])
    (by positivity)

end Algebraic.Cutwidth.MultiOutput
