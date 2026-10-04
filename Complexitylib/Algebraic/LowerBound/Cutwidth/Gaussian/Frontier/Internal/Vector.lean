/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Local

/-!
# Normalized edge sums of kernel rows

An edge `uv` carries the unit vector `(x_u + x_v) / ‖x_u + x_v‖`, where `x` are the
normalized kernel rows. It is supported on the two endpoint balls, and its inner product
with either endpoint row is `√((1 + ρ) / 2)`, where `ρ = ⟨x_u, x_v⟩`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

variable {W : Type} [Fintype W] (H : SimpleGraph W)

/-- The squared norm of the sum of two kernel rows. -/
noncomputable def pairNormSq (q : ℝ) (R : ℕ) (u v : W) : ℝ :=
  ∑ z, (unitKernel H q R u z + unitKernel H q R v z) ^ 2

theorem pairNormSq_comm (q : ℝ) (R : ℕ) (u v : W) :
    pairNormSq H q R u v = pairNormSq H q R v u := by
  unfold pairNormSq
  simp only [add_comm]

theorem pairNormSq_eq (q : ℝ) (R : ℕ) (u v : W) :
    pairNormSq H q R u v = 2 + 2 * ∑ z, unitKernel H q R u z * unitKernel H q R v z := by
  unfold pairNormSq
  have hu := sum_unitKernel_sq H q R u
  have hv := sum_unitKernel_sq H q R v
  have : ∀ z, (unitKernel H q R u z + unitKernel H q R v z) ^ 2 =
      unitKernel H q R u z ^ 2 + unitKernel H q R v z ^ 2 +
        2 * (unitKernel H q R u z * unitKernel H q R v z) := fun z => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hu, hv]
  ring

/-- The unit vector of an edge: the normalized sum of its endpoint kernel rows. -/
noncomputable def edgeVector (q : ℝ) (R : ℕ) : Sym2 W → W → ℝ :=
  Sym2.lift ⟨fun u v z => (unitKernel H q R u z + unitKernel H q R v z) /
      Real.sqrt (pairNormSq H q R u v), fun u v => by
    funext z
    dsimp only
    rw [add_comm, pairNormSq_comm]⟩

@[simp] theorem edgeVector_mk (q : ℝ) (R : ℕ) (u v z : W) :
    edgeVector H q R s(u, v) z = (unitKernel H q R u z + unitKernel H q R v z) /
      Real.sqrt (pairNormSq H q R u v) := rfl

/-- The Gaussian score of an edge. -/
noncomputable def edgeScore (q : ℝ) (R : ℕ) (ω : W → ℝ) (e : Sym2 W) : ℝ :=
  form (edgeVector H q R e) ω

theorem sum_edgeVector_sq {q : ℝ} {R : ℕ} {u v : W} (hpos : 0 < pairNormSq H q R u v) :
    ∑ z, edgeVector H q R s(u, v) z ^ 2 = 1 := by
  simp only [edgeVector_mk, div_pow, ← Finset.sum_div]
  rw [Real.sq_sqrt hpos.le]
  exact div_self hpos.ne'

/-- The inner product of an edge vector with the row of an endpoint. -/
theorem sum_edgeVector_mul {q : ℝ} {R : ℕ} {u v : W} (hpos : 0 < pairNormSq H q R u v) :
    ∑ z, edgeVector H q R s(u, v) z * unitKernel H q R v z =
      Real.sqrt ((1 + ∑ z, unitKernel H q R u z * unitKernel H q R v z) / 2) := by
  set ρ := ∑ z, unitKernel H q R u z * unitKernel H q R v z with hρ
  have hsq : pairNormSq H q R u v = 2 * (1 + ρ) := by rw [pairNormSq_eq]; ring
  have hpos' : 0 < 1 + ρ := by linarith
  have hnum : ∑ z, (unitKernel H q R u z + unitKernel H q R v z) * unitKernel H q R v z =
      1 + ρ := by
    have hv := sum_unitKernel_sq H q R v
    simp only [add_mul, Finset.sum_add_distrib, ← pow_two, hv]
    ring
  simp only [edgeVector_mk, div_mul_eq_mul_div, ← Finset.sum_div, hnum, hsq]
  rw [Real.sqrt_mul (by norm_num), show Real.sqrt ((1 + ρ) / 2) =
      Real.sqrt (1 + ρ) / Real.sqrt 2 from Real.sqrt_div' _ (by norm_num)]
  have h1 : 0 < Real.sqrt (1 + ρ) := Real.sqrt_pos.mpr hpos'
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  field_simp
  rw [Real.sq_sqrt hpos'.le]

theorem edgeVector_eq_zero [DecidableEq W] {q : ℝ} {R : ℕ} {e : Sym2 W} {z : W}
    (hz : z ∉ edgeSupport H R e) : edgeVector H q R e z = 0 := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [edgeSupport_mk, Finset.mem_union, not_or] at hz
    rw [edgeVector_mk, unitKernel_eq_zero_of_notMem_ball H hz.1,
      unitKernel_eq_zero_of_notMem_ball H hz.2, add_zero, zero_div]

theorem edgeScore_congr [DecidableEq W] {q : ℝ} {R : ℕ} {e : Sym2 W} {S : Finset W}
    (hS : edgeSupport H R e ⊆ S) {ω ω' : W → ℝ} (h : ∀ i ∈ S, ω i = ω' i) :
    edgeScore H q R ω e = edgeScore H q R ω' e :=
  form_congr (S := S) (fun _ hi => edgeVector_eq_zero H fun hz => hi (hS hz)) h

theorem measurable_edgeScore (q : ℝ) (R : ℕ) (e : Sym2 W) :
    Measurable fun ω => edgeScore H q R ω e :=
  Gaussian.measurable_form _

end Algebraic.Cutwidth.Gaussian.Internal
