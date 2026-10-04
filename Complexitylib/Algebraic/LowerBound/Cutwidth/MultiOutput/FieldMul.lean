/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.FieldMul.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
public import Complexitylib.Algebraic.Circuit
public import Mathlib.FieldTheory.Finite.GaloisField
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.FieldMul.Internal

/-!
# Lower bounds for multiplication in a finite field

Let `K` be a finite field of degree `n` over a finite field `F`, with a basis `b`, and let
`fieldMul b : F ^ (n + n) → F ^ n` be multiplication in `K` written in coordinates: the first
`n` inputs are the coordinates of `x`, the last `n` those of `y`, and the outputs are the
coordinates of `x * y` (`fieldMul_append_equivFun`). Consider circuits over `F`, over any
signature whose gates have at most two arguments, so with arbitrary functions `F × F → F`,
unary functions and constants as gates. Over `F = GF(2)` these are the circuits over the full
binary basis `B₂`.

**The cut bound** (`le_add_two_of_fieldMul`). Every split of the wires holding `a` inputs of
the first factor and `n - a` outputs is crossed by at least `n - 2` signals. Fixing the second
factor `y` makes the map linear in `x`, so the restricted rank-cut bound
(`MultiOutput.card_pow_le_supportedKernel`) applies to the blocks
`M_y[Y_T, X_S]` and `M_y[Y_S, X_T]` of multiplication by `y`. Averaged over `y`, a block with
`|X| ≤ |Y|` has a kernel of average size below `2`: a nonzero vector `u` lies in the kernel for
a `|F| ^ -|Y|` fraction of the `y`, since `y ↦ y · u` is a bijection of `K`. So some `y` makes
both blocks nearly of full rank.

**One component** (`mem_component_of_fieldMul`). The component of an output is crossed by no
signal, so the same blocks vanish on it for every fixed factor; as `y = (b j)⁻¹ b i` makes the
entry `(i, j)` nonzero, the component holds every input of the first factor and every output,
and by fixing `x` instead, every input of the second factor.

**The finite bound** (`sub_two_le_of_fieldMul`). Under the graph-ordering hypothesis for
coefficient `A`, slack `η` and constant `C`, a circuit of size `s` has
`n - 2 ≤ (A + η) (s - 2 n)⁺ + 3 log₂ (2 n + 3 s) + C`. The outputs are distinct wires and none
is an input of the first factor, so along the ranking of `MultiOutput.exists_rank` some prefix
ending at one of these `2 n` terminals holds exactly `n` of them; it is charged to the
component holding all `2 n` inputs.

**The asymptotic bound** (`eventually_lt_size_of_fieldMul`). With the edge-score ordering
coefficient `A = 2 κ_E`, where `κ_E = Gaussian.frontierCoefficient ≈ 0.14035`, for every
`ε > 0` and all large `n`, every such circuit has more than `(2 + 1/(2 κ_E) - ε) n` gates, the
coefficient being `2 + π/(3 arccos((1 + 2√2)/4)) ≈ 5.5625`; as `2 κ_E ≤ 9/32`, also more than
`(50/9 - ε) n` gates (`eventually_lt_size_of_fieldMul_fifty_div_nine`). The threshold depends
only on `ε`, not on the fields, the basis or the signature. In particular
(`eventually_lt_size_galoisField`), multiplication in `GF(2 ^ n) = GaloisField 2 n` over
`GF(2) = ZMod 2`, in any basis, needs more than `(2 + 1/(2 κ_E) - ε) n` binary gates; such
bases exist (`nonempty_basis_galoisField`).

*Prior art.* An earlier linear lower bound for this kind of multiplication is due to Lamagna and
Savage; whether the coefficient here is new is under literature check.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open SingleCut Filter

variable {σ : Signature} {n : Nat}

/-! ## Multiplication in coordinates -/

/-- **`fieldMul` multiplies.** On the coordinates of `u` and of `v` it returns the coordinates
of `u * v`. -/
theorem fieldMul_append_equivFun {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Module.Basis (Fin n) F K) (u v : K) :
    fieldMul b (Fin.append (b.equivFun u) (b.equivFun v)) = b.equivFun (u * v) :=
  Internal.fieldMul_append_equivFun b u v

/-! ## Circuits for multiplication -/

section Circuit

variable {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
  {b : Module.Basis (Fin n) F K} {I : Interpretation σ F} {c : Circuit σ (n + n) n}

/-- **All inputs and outputs lie in one component.** If a circuit over a finite field, over any
signature, computes multiplication in coordinates and `n ≥ 1`, the component of its first
output in the wire graph contains every input and every output. -/
theorem mem_component_of_fieldMul (hc : c.Computes I (fieldMul b)) (hn : 0 < n) :
    (∀ k, Wire.input k ∈ component c.program (c.outputs ⟨0, hn⟩)) ∧
      ∀ i, c.outputs i ∈ component c.program (c.outputs ⟨0, hn⟩) := by
  classical
  exact Internal.mem_component_of_trace b hn c.program I c.outputs
    fun z i => congrFun (hc z) i

/-- **The cut bound for multiplication.** If a circuit over a finite field, over any signature,
computes multiplication in coordinates, then every set `S` of its wires holding `a` inputs of
the first factor and `n - a` outputs is crossed by at least `n - 2` forward and backward
signals. -/
theorem le_add_two_of_fieldMul (hc : c.Computes I (fieldMul b)) (S : Finset (Wire (n + n) c.size))
    (hS : (Finset.univ.filter fun j : Fin n => Wire.input (Fin.castAdd n j) ∈ S).card +
      (outputsIn c.outputs S).card = n) :
    n ≤ (forward c.program S).card + (backward c.program S).card + 2 := by
  classical
  exact Internal.le_add_two_of_trace b c.program I c.outputs (fun z i => congrFun (hc z) i) S hS

/-- **The finite bound for multiplication.** If a circuit over a finite field, over any
signature with fan-in at most two, computes multiplication in a degree-`n` extension in
coordinates, then under the graph-ordering hypothesis
`n - 2 ≤ (A + η) (s - 2 n)⁺ + 3 log₂ (2 n + 3 s) + C` for its size `s`. -/
theorem sub_two_le_of_fieldMul {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) (hfan : c.FanInAtMost 2)
    (hc : c.Computes I (fieldMul b)) :
    (n : ℝ) - 2 ≤
      (A + η) * max ((c.size : ℝ) - 2 * n) 0 + 3 * Real.logb 2 (2 * n + 3 * c.size) + C := by
  classical
  exact Internal.sub_two_le_of_trace b hAη order c.program hfan I c.outputs
    fun z i => congrFun (hc z) i

end Circuit

/-! ## Asymptotic bounds -/

universe u v w

/-- **The asymptotic bound with a general ordering coefficient.** If the graph-ordering
hypothesis holds with coefficient `A > 0` for every positive slack, then for every `ε > 0` and
all large `n`, every fan-in-two circuit over a finite field `F` computing multiplication in a
degree-`n` extension `K` of `F`, in any basis, has more than `(2 + 1/A - ε) n` gates. -/
theorem eventually_lt_size_of_fieldMul_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] (K : Type w) [Field K]
      [Algebra F K] (b : Module.Basis (Fin n) F K) (σ : Signature.{v})
      (I : Interpretation σ F) (c : Circuit σ (n + n) n),
        c.FanInAtMost 2 → c.Computes I (fieldMul b) → (2 + 1 / A - ε) * n < c.size :=
  Internal.eventually_lt_size_of_orderingBound_fieldMul hA order hε

/-- **Multiplication in a degree-`n` extension needs `(2 + 1/(2 κ_E) - ε) n` gates.** For every
`ε > 0` and all large `n`, every circuit over a finite field `F`, over any signature with
fan-in at most two, computing multiplication in a degree-`n` extension of `F` in any basis has
more than `(2 + 1/(2 κ_E) - ε) n` gates, where `κ_E = Gaussian.frontierCoefficient`; the
coefficient is `2 + π/(3 arccos((1 + 2√2)/4)) ≈ 5.5625`. -/
theorem eventually_lt_size_of_fieldMul {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] (K : Type w) [Field K]
      [Algebra F K] (b : Module.Basis (Fin n) F K) (σ : Signature.{v})
      (I : Interpretation σ F) (c : Circuit σ (n + n) n),
        c.FanInAtMost 2 → c.Computes I (fieldMul b) →
          (2 + 1 / (2 * Gaussian.frontierCoefficient) - ε) * n < c.size :=
  eventually_lt_size_of_fieldMul_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) Multigraph.exists_orderingBound_frontier hε

/-- **Multiplication in a degree-`n` extension needs `(50/9 - ε) n` gates.** -/
theorem eventually_lt_size_of_fieldMul_fifty_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] (K : Type w) [Field K]
      [Algebra F K] (b : Module.Basis (Fin n) F K) (σ : Signature.{v})
      (I : Interpretation σ F) (c : Circuit σ (n + n) n),
        c.FanInAtMost 2 → c.Computes I (fieldMul b) → (50 / 9 - ε) * n < c.size := by
  have hcoef : (50 / 9 : ℝ) ≤ 2 + 1 / (2 * Gaussian.frontierCoefficient) := by
    have hpos : 0 < 2 * Gaussian.frontierCoefficient :=
      mul_pos two_pos Gaussian.frontierCoefficient_pos
    have := one_div_le_one_div_of_le hpos Gaussian.two_mul_frontierCoefficient_le
    norm_num at this ⊢
    linarith
  filter_upwards [eventually_lt_size_of_fieldMul.{u, v, w} hε] with n hn
  intro F _ _ K _ _ b σ I c hfan hc
  refine lt_of_le_of_lt ?_ (hn F K b σ I c hfan hc)
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)

/-! ## Multiplication in `GF(2 ^ n)` -/

/-- `GF(2 ^ n)` has a basis over `GF(2)` indexed by `Fin n` for every `n ≥ 1`. -/
theorem nonempty_basis_galoisField (hn : n ≠ 0) :
    Nonempty (Module.Basis (Fin n) (ZMod 2) (GaloisField 2 n)) :=
  ⟨Module.finBasisOfFinrankEq _ _ (GaloisField.finrank 2 hn)⟩

/-- **Multiplication in `GF(2 ^ n)` needs `(2 + 1/(2 κ_E) - ε) n` binary gates.** For every
`ε > 0` and all large `n`, every circuit over `GF(2) = ZMod 2` with fan-in at most two, so in
particular every circuit over the full binary basis `B₂`, computing multiplication in
`GF(2 ^ n) = GaloisField 2 n` in any basis over `GF(2)` has more than
`(2 + 1/(2 κ_E) - ε) n ≈ (5.5625 - ε) n` gates. -/
theorem eventually_lt_size_galoisField {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (b : Module.Basis (Fin n) (ZMod 2) (GaloisField 2 n))
      (σ : Signature.{v}) (I : Interpretation σ (ZMod 2)) (c : Circuit σ (n + n) n),
        c.FanInAtMost 2 → c.Computes I (fieldMul b) →
          (2 + 1 / (2 * Gaussian.frontierCoefficient) - ε) * n < c.size := by
  filter_upwards [eventually_lt_size_of_fieldMul.{0, v, 0} hε] with n hn
  intro b σ I c hfan hc
  exact hn (ZMod 2) (GaloisField 2 n) b σ I c hfan hc

/-- **Multiplication in `GF(2 ^ n)` needs `(50/9 - ε) n` binary gates.** -/
theorem eventually_lt_size_galoisField_fifty_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (b : Module.Basis (Fin n) (ZMod 2) (GaloisField 2 n))
      (σ : Signature.{v}) (I : Interpretation σ (ZMod 2)) (c : Circuit σ (n + n) n),
        c.FanInAtMost 2 → c.Computes I (fieldMul b) → (50 / 9 - ε) * n < c.size := by
  filter_upwards [eventually_lt_size_of_fieldMul_fifty_div_nine.{0, v, 0} hε] with n hn
  intro b σ I c hfan hc
  exact hn (ZMod 2) (GaloisField 2 n) b σ I c hfan hc

end Algebraic.Cutwidth.MultiOutput
