/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform.Defs
public import Complexitylib.Algebraic.Basis.Binary
public import Mathlib.Order.Filter.AtTopBot.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding.Asymptotics
import Mathlib.Tactic.NormNum

/-!
# The coefficient-four bound for the computed hard family

The actual uniform source-reduction family has fixed extraction error below
one half and sublinear entropy. Its dyadic threshold has binary logarithm
equal to that entropy. Balanced padding therefore gives the circuit bound,
and shifting the eventual statement measures it at every sufficiently large
full input length.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Filter

theorem sourceReductionHardFamily_eventually_lt_size {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => sourceReductionHardFamily n x) →
        (4 - ε) * n < circuit.size := by
  have logarithm :
      (fun n => Real.logb 2
        ((2 ^ sourceReductionEntropy n (sourceReductionFamilyScale n) : Nat) : ℝ))
        =o[atTop] (fun n => (n : ℝ)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one one_lt_two, mul_one] using sourceReductionFamilyEntropy_isLittleO
  have bound := eventually_lt_size_balancePad_of_flatSumsetExtractor sourceReductionFamily
    (fun n => 2 ^ sourceReductionEntropy n (sourceReductionFamilyScale n))
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

end Algebraic.Cutwidth.Extractor.Internal
