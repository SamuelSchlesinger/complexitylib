/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.CauchyCharZero
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial

/-!
# Polynomial-gate lower bounds for the explicit rational Cauchy family

One rational matrix family works over every characteristic-zero field, including
the rationals, reals, and complexes. The coefficient applies to arbitrary binary
polynomial gates, with unrestricted degree, coefficients, depth, and fanout.
Explicit nullary gate occurrences are counted in the circuit size.
-/

public section

namespace Algebraic.Cutwidth.MultiOutput.Polynomial

open Filter Matrix

universe u v

/-- The rational Cauchy map requires the Gaussian linear coefficient over any polynomial basis. -/
theorem eventually_lt_size_cauchyCharZero {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Type u) [Field F] [CharZero F],
      ∀ (σ : Signature.{v}) (I : Interpretation σ F), IsPolynomial I →
      ∀ c : Circuit σ N N, c.FanInAtMost 2 →
      c.Computes I (fun x => cauchyCharZero F N *ᵥ x) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * N <
          c.size := by
  filter_upwards [eventually_lt_size_of_totallyRegular.{u, v} hε] with N bound
  intro F _ _ σ I polynomial c fan computes
  exact bound F (cauchyCharZero F N) (totallyRegular_cauchyCharZero F N)
    σ I polynomial c fan computes

/-- The canonical polynomial signature permits arbitrary coefficients inside each gate. -/
theorem eventually_lt_size_cauchyCharZero_full {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Type u) [Field F] [CharZero F],
      ∀ c : Circuit (signature F) N N, c.FanInAtMost 2 →
      c.Computes (interpretation F) (fun x => cauchyCharZero F N *ᵥ x) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * N <
          c.size := by
  filter_upwards [eventually_lt_size_cauchyCharZero.{u, u} hε] with N bound
  intro F _ _ c fan computes
  exact bound F (signature F) (interpretation F) isPolynomial_interpretation c fan computes

end Algebraic.Cutwidth.MultiOutput.Polynomial
