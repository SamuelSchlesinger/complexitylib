/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform.Defs
public import Complexitylib.Algebraic.Basis.Binary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph
public import Mathlib.Order.Filter.AtTopBot.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding.Asymptotics
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
import Mathlib.Tactic.NormNum

/-!
# The coefficient-four bound for the computed hard family

The actual uniform source-reduction family has fixed extraction error below
one half and sublinear entropy. Its dyadic threshold has binary logarithm
equal to that entropy. Balanced padding therefore gives the circuit bound
`1 + 1/A` for every graph-ordering coefficient `A > 0`, and shifting the
eventual statement measures it at every sufficiently large full input length.
The proved ordering bound with `A = 1/3` gives the coefficient four, and the
Gaussian edge-score bound with `A = 2(3/π)(√2 - 1)/√(5 + 2√2)` gives
`1 + π(√2 + 1)√(5 + 2√2)/6`; its rational weakening `A = 2/7` gives `9/2`.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Filter

theorem sourceReductionHardFamily_eventually_lt_size_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => sourceReductionHardFamily n x) →
        (1 + 1 / A - ε) * n < circuit.size := by
  have logarithm :
      (fun n => Real.logb 2
        ((2 ^ sourceReductionEntropy n (sourceReductionFamilyScale n) : Nat) : ℝ))
        =o[atTop] (fun n => (n : ℝ)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one one_lt_two, mul_one] using sourceReductionFamilyEntropy_isLittleO
  have bound := eventually_lt_size_balancePad_of_flatSumsetExtractor_of_orderingBound hA order
    sourceReductionFamily (fun n => 2 ^ sourceReductionEntropy n (sourceReductionFamilyScale n))
    (by norm_num : (35 / 72 : ℝ) < 1 / 2)
    (Filter.Eventually.of_forall fun n => by positivity) logarithm
    sourceReductionFamily_eventually_flat hε
  filter_upwards [(tendsto_sub_atTop_nat 1).eventually bound, eventually_ge_atTop 1]
    with n previous nonzero
  cases n with
  | zero => lia
  | succ n =>
    intro circuit computes
    have computes' : circuit.Computes Binary.interpretation
        (fun x _ => balancePad (sourceReductionFamily n) x) := by
      simpa only [sourceReductionHardFamily_succ] using computes
    simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      using previous circuit computes'

theorem sourceReductionHardFamily_eventually_lt_size {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => sourceReductionHardFamily n x) →
        (4 - ε) * n < circuit.size := by
  filter_upwards [sourceReductionHardFamily_eventually_lt_size_of_orderingBound
    (by norm_num : (0 : ℝ) < 1 / 3) Multigraph.exists_orderingBound_one_third hε]
    with n hn circuit computes
  have := hn circuit computes
  rwa [show (1 : ℝ) + 1 / (1 / 3) = 4 by norm_num] at this

theorem sourceReductionHardFamily_eventually_lt_size_gaussian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => sourceReductionHardFamily n x) →
        (1 + Real.pi * (Real.sqrt 2 + 1) * Real.sqrt (5 + 2 * Real.sqrt 2) / 6 - ε) * n <
          circuit.size := by
  have bound := sourceReductionHardFamily_eventually_lt_size_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos)
    Multigraph.exists_orderingBound_frontier hε
  rwa [Gaussian.one_add_inv_two_mul_frontierCoefficient] at bound

theorem sourceReductionHardFamily_eventually_lt_size_nine_div_two {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => sourceReductionHardFamily n x) →
        (9 / 2 - ε) * n < circuit.size := by
  filter_upwards [sourceReductionHardFamily_eventually_lt_size_of_orderingBound
    (by norm_num : (0 : ℝ) < 2 / 7) Multigraph.exists_orderingBound_two_div_seven hε]
    with n hn circuit computes
  have := hn circuit computes
  rwa [show (1 : ℝ) + 1 / (2 / 7) = 9 / 2 by norm_num] at this

end Algebraic.Cutwidth.Extractor.Internal
