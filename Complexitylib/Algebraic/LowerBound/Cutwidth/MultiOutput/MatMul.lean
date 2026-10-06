/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Tripartite
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.TotallyRegular
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Taylor
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Arithmetic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
public import Complexitylib.Algebraic.Circuit
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Internal.Bound

/-!
# Lower bounds for matrix multiplication

Let `matMul n : F ^ (n² + n²) → F ^ (n²)` be the product `C = A B` of two `n × n` matrices over a
field `F`, written in coordinates (`MatMul.Defs`; `matMul_matMulInput`). Consider
circuits over `F`, over any signature whose gates have at most two arguments, so with arbitrary
functions `F × F → F`, unary functions and constants as gates; over `F = GF(2)` these are the
circuits over the full binary basis `B₂` computing the Boolean matrix product modulo two. Over
arbitrary fields `K`, also consider circuits with polynomial gates of fan-in at most two, and
arithmetic circuits of additions, multiplications and free constants (`Arithmetic.gateCost`). The
model is that of `MultiOutput.FieldMul` and `MultiOutput.TotallyRegular`: the size counts gates,
inputs and output designations are free.

**The terminal graph** (`MatMul.Tripartite`). The inputs `A i j`, `B j k` and the outputs
`C i k` are the edges of the complete tripartite graph on three copies `I`, `J`, `K` of
`Fin n`. A split `S` of the wires places `d v` of the `2 n` terminals at each vertex `v`; the
*charges* `R_I`, `R_J`, `R_K` sum `min (d, 2 n - d)` over the vertices of each part.

**The charge bounds** (`charges_le_of_matMul_of_totallyRegular`, `charges_le_add_of_matMul`,
`charges_le_of_matMul_polynomial`). Let `S` be crossed by `w` forward and backward signals.
* Fixing `B = B₀` makes the product linear in `A`, with change `δA ↦ δA B₀`, block diagonal
  over the rows `i`; by the restricted rank-cut bound (`card_pow_le_supportedKernel`), `w` is at
  least the rank of the blocks `B₀[A_S(i), C_T(i)]` and `B₀[A_T(i), C_S(i)]`, summed over `i`.
* Fixing `A = A₀` gives the same over the columns `k`.
* For any `Λ`, the combination `∑ i k, Λ i k C i k` of the outputs is a quadratic form whose
  Hessian pairs `A i j` with `B j k` through `Λ i k`; by the rank-cut bound for a combination of
  outputs (`blockRank_add_transpose_le_of_sum`), `w` is at least the rank of its cross block,
  which is block diagonal over the inner index `j`.

If `F` has a totally regular `n × n` matrix (every square submatrix nonsingular), used for
`B₀`, `A₀` and `Λ`, every block has full rank and `R_I, R_J, R_K ≤ w`; this holds over `ZMod q`
for a prime `q ≥ 2 n` with the Cauchy matrix `cauchyZMod q n`, and for polynomial gates over any
field `K` by evaluating over `K(t)` with the generic Hankel matrix (`totallyRegular_genericHankel`).
Over every finite field, in particular `GF(2)`, a uniformly random `n × n` matrix has kernel
blocks of average size at most twice the ideal size, so a matrix chosen after the split loses at
most `4 n`: `R_I, R_J, R_K ≤ w + 4 n`.

**One component** (`mem_component_of_matMul`). The component of the output `C 0 0` is crossed by
no signal, so with `B₀` or `A₀` a matrix unit, the slices separate; the unit vector at `A i j`
moves `C i k` when `B₀ = E j k`, and the unit vector at `B j k` moves `C i k` when `A₀ = E i j`.
So the component holds every input and output.

**The finite bounds** (`half_sq_le_of_matMul_of_totallyRegular`, `sq_sub_le_of_matMul`,
`half_sq_le_of_matMul_polynomial`). The terminals lie on distinct wires
(`terminal_injective_of_matMul`). Along the ranking of `MultiOutput.exists_rank`, the *threshold
prefix* (`Tripartite.exists_threshold`), the first prefix with at least `⌈3 n/2⌉` heavy vertices
(with at least `n` placed terminals), ends at a terminal and has at most `⌈3 n/2⌉ + 1` of them.
Charging each terminal with one heavy and one light endpoint to its light endpoint if placed and
to its heavy endpoint otherwise gives `3 n² ≤ 2 (R_I + R_J + R_K) + 3`
(`Tripartite.three_mul_sq_le_two_mul_charge`). Charged to the component holding all `2 n²`
inputs, a circuit of size `s` therefore has
`(n² - 1)/2 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C` with a totally regular matrix or for
polynomial gates over any field, and
`(n² - 8 n - 1)/2 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C` over every finite field.

**The asymptotic bounds** (`eventually_lt_size_of_matMul`,
`eventually_lt_size_of_matMul_polynomial`, `eventually_lt_arithmeticCost_of_matMul`). With the
edge-score ordering coefficient `A = 2 κ_E`, where `κ_E = Gaussian.frontierCoefficient ≈ 0.14035`,
for every `ε > 0` and all large `n`, every such circuit has more than `(2 + 1/(4 κ_E) - ε) n²`
gates, the coefficient being `2 + π/(6 arccos((1 + 2√2)/4)) ≈ 3.7812`; as `2 κ_E ≤ 9/32`, also
more than `(34/9 - ε) n²` gates. The threshold depends only on `ε`, not on the field or the
signature. The bound holds

* for circuits with arbitrary fan-in-two gates over every finite field (`eventually_lt_size_of_matMul`),
  in particular over `GF(2) = ZMod 2` (`eventually_lt_size_matMul_zmod_two`),
* for formal computation with polynomial gates of fan-in at most two over every field
  (`eventually_lt_size_of_matMul_polynomial`),
* for computation of the matrix product function with polynomial gates of fan-in at most two over
  every infinite field (`eventually_lt_size_of_matMul_of_infinite`), and
* for the number of additions and multiplications of arithmetic circuits, with arbitrary
  constants free, computing the matrix product over every infinite field
  (`eventually_lt_arithmeticCost_of_matMul`) or formally over every field
  (`eventually_lt_arithmeticCost_of_matMul_formal`).

*Prior art.* Lower bounds for matrix multiplication usually count the multiplications of
bilinear or quadratic algorithms in arithmetic models: Bläser (STACS 2001) proves
`5/2 n² - 3 n` multiplications, and Shpilka (SICOMP 2003) `3 n² - o(n²)` product gates over
`GF(2)` for bilinear and quadratic circuits. We know of no earlier bound beyond the trivial
`≈ 2 n²` on the number of gates of circuits with arbitrary fan-in-two gates, or over `B₂`,
computing the matrix product.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open SingleCut Tripartite Filter

variable {σ : Signature} {n : Nat}

/-! ## Matrix multiplication in coordinates -/

/-- **`matMul` multiplies.** On the input holding `A` and `B`, the output `C i k` is the entry
`(A * B) i k` of the product. -/
theorem matMul_matMulInput {R : Type*} [Semiring R] (A B : Matrix (Fin n) (Fin n) R)
    (i k : Fin n) : matMul n (matMulInput A B) (matMulOutput n i k) = (A * B) i k :=
  MatMul.Internal.matMul_matMulInput A B i k

/-! ## Circuits for matrix multiplication -/

section Circuit

variable {F : Type*} [Field F] [Fintype F] {I : Interpretation σ F}
  {c : Circuit σ (n * n + n * n) (n * n)}

omit [Fintype F] in
/-- **The terminals lie on distinct wires.** In a circuit over a field computing `matMul n`, the
inputs `A i j`, `B j k` and the outputs `C i k` lie on `3 n²` distinct wires. -/
theorem terminal_injective_of_matMul (hc : c.Computes I (matMul n)) :
    Function.Injective (Sum.elim (matMulTermA n c.size)
      (Sum.elim (matMulTermB n c.size) (matMulTermC c.outputs))) :=
  MatMul.Internal.terminal_injective fun z o => congrFun (hc z) o

omit [Fintype F] in
/-- **All inputs and outputs lie in one component.** If a circuit over a field, over any
signature, computes `matMul n` and `n ≥ 1`, the component of its output `C 0 0` in the wire
graph contains every input and every output. -/
theorem mem_component_of_matMul (hc : c.Computes I (matMul n)) (hn : 0 < n) :
    (∀ x, Wire.input x ∈ component c.program (c.outputs (matMulOutput n ⟨0, hn⟩ ⟨0, hn⟩))) ∧
      ∀ o, c.outputs o ∈ component c.program (c.outputs (matMulOutput n ⟨0, hn⟩ ⟨0, hn⟩)) :=
  MatMul.Internal.mem_component_of_trace hn fun z o => congrFun (hc z) o

/-- **The charge bounds with a totally regular matrix.** If a circuit over a finite field with a
totally regular `n × n` matrix computes `matMul n`, then for every set `S` of its wires each of
the charges `R_I`, `R_J`, `R_K` of the placed terminals is at most the number of forward and
backward signals of `S`. -/
theorem charges_le_of_matMul_of_totallyRegular (hc : c.Computes I (matMul n))
    {M : Matrix (Fin n) (Fin n) F} (hM : TotallyRegular M)
    (S : Finset (Wire (n * n + n * n) c.size)) :
    chargeI (place (matMulTermA n c.size) S) (place (matMulTermC c.outputs) S) ≤
        (forward c.program S).card + (backward c.program S).card ∧
      chargeJ (place (matMulTermA n c.size) S) (place (matMulTermB n c.size) S) ≤
        (forward c.program S).card + (backward c.program S).card ∧
      chargeK (place (matMulTermB n c.size) S) (place (matMulTermC c.outputs) S) ≤
        (forward c.program S).card + (backward c.program S).card := by
  classical
  exact MatMul.Internal.charges_le_of_totallyRegular (fun z o => congrFun (hc z) o) hM S

/-- **The charge bounds over every finite field.** If a circuit over a finite field computes
`matMul n`, then for every set `S` of its wires each of the charges `R_I`, `R_J`, `R_K` of the
placed terminals is at most the number of forward and backward signals of `S` plus `4 n`. -/
theorem charges_le_add_of_matMul (hc : c.Computes I (matMul n))
    (S : Finset (Wire (n * n + n * n) c.size)) :
    chargeI (place (matMulTermA n c.size) S) (place (matMulTermC c.outputs) S) ≤
        (forward c.program S).card + (backward c.program S).card + 4 * n ∧
      chargeJ (place (matMulTermA n c.size) S) (place (matMulTermB n c.size) S) ≤
        (forward c.program S).card + (backward c.program S).card + 4 * n ∧
      chargeK (place (matMulTermB n c.size) S) (place (matMulTermC c.outputs) S) ≤
        (forward c.program S).card + (backward c.program S).card + 4 * n := by
  classical
  exact MatMul.Internal.charges_le_add (fun z o => congrFun (hc z) o) S

/-- **The finite bound with a totally regular matrix.** If a circuit over a finite field with a
totally regular `n × n` matrix, over any signature with fan-in at most two, computes `matMul n`,
then under the graph-ordering hypothesis
`(n² - 1)/2 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C` for its size `s`. -/
theorem half_sq_le_of_matMul_of_totallyRegular {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) {M : Matrix (Fin n) (Fin n) F}
    (hM : TotallyRegular M) (hfan : c.FanInAtMost 2) (hc : c.Computes I (matMul n)) :
    ((n : ℝ) ^ 2 - 1) / 2 ≤ (A + η) * max ((c.size : ℝ) - 2 * n ^ 2) 0 +
      3 * Real.logb 2 (2 * n ^ 2 + 3 * c.size) + C := by
  classical
  exact MatMul.Internal.half_sq_le_of_totallyRegular hAη order hM c.program hfan I c.outputs
    fun z o => congrFun (hc z) o

/-- **The finite bound over every finite field.** If a circuit over a finite field, over any
signature with fan-in at most two, computes `matMul n`, then under the graph-ordering hypothesis
`(n² - 8 n - 1)/2 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C` for its size `s`. -/
theorem sq_sub_le_of_matMul {A η C : ℝ} (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C)
    (hfan : c.FanInAtMost 2) (hc : c.Computes I (matMul n)) :
    ((n : ℝ) ^ 2 - 8 * n - 1) / 2 ≤ (A + η) * max ((c.size : ℝ) - 2 * n ^ 2) 0 +
      3 * Real.logb 2 (2 * n ^ 2 + 3 * c.size) + C := by
  classical
  exact MatMul.Internal.sq_sub_le hAη order c.program hfan I c.outputs
    fun z o => congrFun (hc z) o

end Circuit

/-- **The charge bounds for polynomial gates over any field.** If a circuit with polynomial gates
over any field `K` formally computes `matMul n`, then for every set `S` of its wires each of the
charges `R_I`, `R_J`, `R_K` of the placed terminals is at most the number of forward and backward
signals of `S`. -/
theorem charges_le_of_matMul_polynomial {K : Type*} [Field K]
    (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
    {c : Circuit σ (n * n + n * n) (n * n)}
    (hc : Taylor.FormallyComputes P c (matMul n MvPolynomial.X))
    (S : Finset (Wire (n * n + n * n) c.size)) :
    chargeI (place (matMulTermA n c.size) S) (place (matMulTermC c.outputs) S) ≤
        (forward c.program S).card + (backward c.program S).card ∧
      chargeJ (place (matMulTermA n c.size) S) (place (matMulTermB n c.size) S) ≤
        (forward c.program S).card + (backward c.program S).card ∧
      chargeK (place (matMulTermB n c.size) S) (place (matMulTermC c.outputs) S) ≤
        (forward c.program S).card + (backward c.program S).card :=
  MatMul.Internal.charges_le_of_formallyComputes P c.program c.outputs hc S

/-- **The finite bound for polynomial gates over any field.** If a fan-in-two circuit with
polynomial gates over any field formally computes `matMul n`, then under the graph-ordering
hypothesis `(n² - 1)/2 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C` for its size `s`. -/
theorem half_sq_le_of_matMul_polynomial {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) {K : Type*} [Field K]
    (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
    {c : Circuit σ (n * n + n * n) (n * n)} (hfan : c.FanInAtMost 2)
    (hc : Taylor.FormallyComputes P c (matMul n MvPolynomial.X)) :
    ((n : ℝ) ^ 2 - 1) / 2 ≤ (A + η) * max ((c.size : ℝ) - 2 * n ^ 2) 0 +
      3 * Real.logb 2 (2 * n ^ 2 + 3 * c.size) + C :=
  MatMul.Internal.half_sq_le_of_formallyComputes P c.program c.outputs hAη order hfan hc

/-- **The finite bound over `ZMod q`.** For a prime `q ≥ 2 n`, the Cauchy matrix
`cauchyZMod q n` is totally regular, so every circuit over `ZMod q` with fan-in at most two
computing `matMul n` has `(n² - 1)/2 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C`. -/
theorem half_sq_le_of_matMul_zmod {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) {q : Nat} [Fact q.Prime] (hq : 2 * n ≤ q)
    {I : Interpretation σ (ZMod q)} {c : Circuit σ (n * n + n * n) (n * n)}
    (hfan : c.FanInAtMost 2) (hc : c.Computes I (matMul n)) :
    ((n : ℝ) ^ 2 - 1) / 2 ≤ (A + η) * max ((c.size : ℝ) - 2 * n ^ 2) 0 +
      3 * Real.logb 2 (2 * n ^ 2 + 3 * c.size) + C :=
  half_sq_le_of_matMul_of_totallyRegular hAη order (totallyRegular_cauchyZMod q n hq)
    hfan hc

/-! ## Asymptotic bounds -/

universe u v

private theorem thirtyFour_div_nine_le :
    (34 / 9 : ℝ) ≤ 2 + 1 / (4 * Gaussian.frontierCoefficient) := by
  have hpos : 0 < 4 * Gaussian.frontierCoefficient :=
    mul_pos (by norm_num) Gaussian.frontierCoefficient_pos
  have h4 : 4 * Gaussian.frontierCoefficient ≤ 9 / 16 := by
    linarith [Gaussian.two_mul_frontierCoefficient_le]
  have := one_div_le_one_div_of_le hpos h4
  norm_num at this ⊢
  linarith

/-- **The asymptotic bound with a general ordering coefficient.** If the graph-ordering
hypothesis holds with coefficient `A > 0` for every positive slack, then for every `ε > 0` and
all large `n`, every fan-in-two circuit over a finite field computing `matMul n` has more than
`(2 + 1/(2 A) - ε) n²` gates. -/
theorem eventually_lt_size_of_matMul_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] (σ : Signature.{v})
      (I : Interpretation σ F) (c : Circuit σ (n * n + n * n) (n * n)),
        c.FanInAtMost 2 → c.Computes I (matMul n) → (2 + 1 / (2 * A) - ε) * n ^ 2 < c.size :=
  MatMul.Internal.eventually_lt_size_of_orderingBound_matMul hA order hε

/-- **Matrix multiplication needs `(2 + 1/(4 κ_E) - ε) n²` gates.** For every `ε > 0` and all
large `n`, every circuit over a finite field, over any signature with fan-in at most two,
computing the product of two `n × n` matrices has more than `(2 + 1/(4 κ_E) - ε) n²` gates,
where `κ_E = Gaussian.frontierCoefficient`; the coefficient is
`2 + π/(6 arccos((1 + 2√2)/4)) ≈ 3.7812`. -/
theorem eventually_lt_size_of_matMul {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] (σ : Signature.{v})
      (I : Interpretation σ F) (c : Circuit σ (n * n + n * n) (n * n)),
        c.FanInAtMost 2 → c.Computes I (matMul n) →
          (2 + 1 / (4 * Gaussian.frontierCoefficient) - ε) * n ^ 2 < c.size := by
  have h := eventually_lt_size_of_matMul_of_orderingBound.{u, v}
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) Multigraph.exists_orderingBound_frontier hε
  have h4 : 2 * (2 * Gaussian.frontierCoefficient) = 4 * Gaussian.frontierCoefficient := by ring
  rwa [h4] at h

/-- **Matrix multiplication needs `(34/9 - ε) n²` gates.** -/
theorem eventually_lt_size_of_matMul_thirtyFour_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] (σ : Signature.{v})
      (I : Interpretation σ F) (c : Circuit σ (n * n + n * n) (n * n)),
        c.FanInAtMost 2 → c.Computes I (matMul n) → (34 / 9 - ε) * n ^ 2 < c.size := by
  have hcoef := thirtyFour_div_nine_le
  filter_upwards [eventually_lt_size_of_matMul.{u, v} hε] with n hn
  intro F _ _ σ I c hfan hc
  refine lt_of_le_of_lt ?_ (hn F σ I c hfan hc)
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **Boolean matrix multiplication modulo two needs `(2 + 1/(4 κ_E) - ε) n²` binary gates.**
For every `ε > 0` and all large `n`, every circuit over `GF(2) = ZMod 2` with fan-in at most
two, so in particular every circuit over the full binary basis `B₂`, computing the product of
two `n × n` matrices over `GF(2)` has more than `(2 + 1/(4 κ_E) - ε) n² ≈ (3.7812 - ε) n²`
gates. -/
theorem eventually_lt_size_matMul_zmod_two {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ (ZMod 2))
      (c : Circuit σ (n * n + n * n) (n * n)), c.FanInAtMost 2 → c.Computes I (matMul n) →
        (2 + 1 / (4 * Gaussian.frontierCoefficient) - ε) * n ^ 2 < c.size := by
  filter_upwards [eventually_lt_size_of_matMul.{0, v} hε] with n hn
  intro σ I c hfan hc
  exact hn (ZMod 2) σ I c hfan hc

/-- **Boolean matrix multiplication modulo two needs `(34/9 - ε) n²` binary gates.** -/
theorem eventually_lt_size_matMul_zmod_two_thirtyFour_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ (ZMod 2))
      (c : Circuit σ (n * n + n * n) (n * n)), c.FanInAtMost 2 → c.Computes I (matMul n) →
        (34 / 9 - ε) * n ^ 2 < c.size := by
  filter_upwards [eventually_lt_size_of_matMul_thirtyFour_div_nine.{0, v} hε] with n hn
  intro σ I c hfan hc
  exact hn (ZMod 2) σ I c hfan hc

/-- **The asymptotic bound for polynomial gates with a general ordering coefficient.** -/
theorem eventually_lt_size_of_matMul_polynomial_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] (σ : Signature.{v})
      (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
      (c : Circuit σ (n * n + n * n) (n * n)),
        c.FanInAtMost 2 → Taylor.FormallyComputes P c (matMul n MvPolynomial.X) →
          (2 + 1 / (2 * A) - ε) * n ^ 2 < c.size :=
  MatMul.Internal.eventually_lt_size_of_orderingBound_matMul_polynomial hA order hε

/-- **Matrix multiplication needs `(2 + 1/(4 κ_E) - ε) n²` polynomial gates over every field.**
For every `ε > 0` and all large `n`, every circuit with polynomial gates of fan-in at most two
over any field, of any degree and with any coefficients, formally computing the product of two
`n × n` matrices has more than `(2 + 1/(4 κ_E) - ε) n²` gates. -/
theorem eventually_lt_size_of_matMul_polynomial {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] (σ : Signature.{v})
      (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
      (c : Circuit σ (n * n + n * n) (n * n)),
        c.FanInAtMost 2 → Taylor.FormallyComputes P c (matMul n MvPolynomial.X) →
          (2 + 1 / (4 * Gaussian.frontierCoefficient) - ε) * n ^ 2 < c.size := by
  have h := eventually_lt_size_of_matMul_polynomial_of_orderingBound.{u, v}
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) Multigraph.exists_orderingBound_frontier hε
  have h4 : 2 * (2 * Gaussian.frontierCoefficient) = 4 * Gaussian.frontierCoefficient := by ring
  rwa [h4] at h

/-- **Matrix multiplication needs `(34/9 - ε) n²` polynomial gates over every field.** -/
theorem eventually_lt_size_of_matMul_polynomial_thirtyFour_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] (σ : Signature.{v})
      (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
      (c : Circuit σ (n * n + n * n) (n * n)),
        c.FanInAtMost 2 → Taylor.FormallyComputes P c (matMul n MvPolynomial.X) →
          (34 / 9 - ε) * n ^ 2 < c.size := by
  have hcoef := thirtyFour_div_nine_le
  filter_upwards [eventually_lt_size_of_matMul_polynomial.{u, v} hε] with n hn
  intro K _ σ P c hfan hc
  refine lt_of_le_of_lt ?_ (hn K σ P c hfan hc)
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **Matrix multiplication with polynomial gates over an infinite field.** For every `ε > 0`
and all large `n`, over every infinite field, every circuit whose operations are polynomial
functions of at most two arguments and which computes matrix multiplication as a function has
more than `(2 + 1/(4 κ_E) - ε) n²` gates. -/
theorem eventually_lt_size_of_matMul_of_infinite {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] [Infinite K] (σ : Signature.{v})
      (I : Interpretation σ K), Polynomial.IsPolynomial I →
      ∀ c : Circuit σ (n * n + n * n) (n * n), c.FanInAtMost 2 → c.Computes I (matMul n) →
        (2 + 1 / (4 * Gaussian.frontierCoefficient) - ε) * n ^ 2 < c.size := by
  filter_upwards [eventually_lt_size_of_matMul_polynomial.{u, v} hε] with n hn
  intro K _ _ σ I hI c hfan hc
  refine hn K σ hI.gatePolynomial c hfan (Taylor.formallyComputes_of_computes hI fun x => ?_)
  rw [hc x]
  exact funext fun o => (MatMul.Internal.eval_matMul_X x o).symm

/-- **Matrix multiplication with polynomial gates over an infinite field needs
`(34/9 - ε) n²` gates.** -/
theorem eventually_lt_size_of_matMul_of_infinite_thirtyFour_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] [Infinite K] (σ : Signature.{v})
      (I : Interpretation σ K), Polynomial.IsPolynomial I →
      ∀ c : Circuit σ (n * n + n * n) (n * n), c.FanInAtMost 2 → c.Computes I (matMul n) →
        (34 / 9 - ε) * n ^ 2 < c.size := by
  have hcoef := thirtyFour_div_nine_le
  filter_upwards [eventually_lt_size_of_matMul_of_infinite.{u, v} hε] with n hn
  intro K _ _ σ I hI c hfan hc
  refine lt_of_le_of_lt ?_ (hn K σ I hI c hfan hc)
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- Every output entry of matrix multiplication is a nonconstant function. -/
theorem matMul_nonconstant {K : Type*} [Field K] (o : Fin (n * n)) :
    ∃ x y : Fin (n * n + n * n) → K, matMul n x o ≠ matMul n y o :=
  MatMul.Internal.matMul_nonconstant o

/-- **Arithmetic circuits with free constants.** For every `ε > 0` and all large `n`, over every
infinite field, every circuit of additions, multiplications and constants computing the product
of two `n × n` matrices performs more than `(2 + 1/(4 κ_E) - ε) n²` additions and
multiplications; constants are free. -/
theorem eventually_lt_arithmeticCost_of_matMul {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] [Infinite K] (Kc : Type v) (constant : Kc → K)
      (c : Circuit (Arithmetic.signature Kc) (n * n + n * n) (n * n)),
        c.Computes (Arithmetic.interpretation constant) (matMul n) →
          (2 + 1 / (4 * Gaussian.frontierCoefficient) - ε) * n ^ 2 <
            c.cost Arithmetic.gateCost := by
  filter_upwards [eventually_lt_size_of_matMul_of_infinite.{u, u} hε, eventually_gt_atTop 0]
    with n bound hn
  intro K _ _ Kc constant c hc
  obtain ⟨d, size, fan, agrees⟩ := Polynomial.exists_polynomial_circuit_of_nonconstant
    (by positivity : 0 < n * n + n * n) constant c fun o => by
      obtain ⟨x, y, hxy⟩ := matMul_nonconstant (K := K) o
      exact ⟨x, y, by rwa [hc x, hc y]⟩
  have result := bound K (Polynomial.signature K) (Polynomial.interpretation K)
    Polynomial.isPolynomial_interpretation d fan fun x => (agrees x).trans (hc x)
  rwa [size] at result

/-- **Arithmetic circuits with free constants need `(34/9 - ε) n²` operations.** -/
theorem eventually_lt_arithmeticCost_of_matMul_thirtyFour_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] [Infinite K] (Kc : Type v) (constant : Kc → K)
      (c : Circuit (Arithmetic.signature Kc) (n * n + n * n) (n * n)),
        c.Computes (Arithmetic.interpretation constant) (matMul n) →
          (34 / 9 - ε) * n ^ 2 < c.cost Arithmetic.gateCost := by
  have hcoef := thirtyFour_div_nine_le
  filter_upwards [eventually_lt_arithmeticCost_of_matMul.{u, v} hε] with n hn
  intro K _ _ Kc constant c hc
  refine lt_of_le_of_lt ?_ (hn K Kc constant c hc)
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **Arithmetic circuits with free constants over every field.** For every `ε > 0` and all
large `n`, over every field `K`, every circuit of additions, multiplications and constants of
`K` formally computing the product of two `n × n` matrices performs more than
`(2 + 1/(4 κ_E) - ε) n²` additions and multiplications; constants are free. -/
theorem eventually_lt_arithmeticCost_of_matMul_formal {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] (Kc : Type v) (constant : Kc → K)
      (c : Circuit (Arithmetic.signature Kc) (n * n + n * n) (n * n)),
        Taylor.FormallyComputes (Taylor.arithmeticPolynomial constant) c
          (matMul n MvPolynomial.X) →
          (2 + 1 / (4 * Gaussian.frontierCoefficient) - ε) * n ^ 2 <
            c.cost Arithmetic.gateCost := by
  filter_upwards [eventually_lt_arithmeticCost_of_matMul.{u, v} hε] with n bound
  intro K _ Kc constant c hc
  have : Infinite (RatFunc K) :=
    Infinite.of_injective _ (RatFunc.algebraMap_injective K)
  refine bound (RatFunc K) Kc (fun k => algebraMap K (RatFunc K) (constant k)) c fun x => ?_
  have h := hc.computes (RatFunc K)
  rw [Taylor.algebraInterpretation_arithmeticPolynomial] at h
  rw [h x]
  funext o
  exact MatMul.Internal.aeval_matMul_X x o

/-- **Arithmetic circuits with free constants over every field need `(34/9 - ε) n²`
operations.** -/
theorem eventually_lt_arithmeticCost_of_matMul_formal_thirtyFour_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] (Kc : Type v) (constant : Kc → K)
      (c : Circuit (Arithmetic.signature Kc) (n * n + n * n) (n * n)),
        Taylor.FormallyComputes (Taylor.arithmeticPolynomial constant) c
          (matMul n MvPolynomial.X) →
          (34 / 9 - ε) * n ^ 2 < c.cost Arithmetic.gateCost := by
  have hcoef := thirtyFour_div_nine_le
  filter_upwards [eventually_lt_arithmeticCost_of_matMul_formal.{u, v} hε] with n hn
  intro K _ Kc constant c hc
  refine lt_of_le_of_lt ?_ (hn K Kc constant c hc)
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Algebraic.Cutwidth.MultiOutput
