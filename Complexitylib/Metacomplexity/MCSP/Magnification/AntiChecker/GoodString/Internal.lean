/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Circuit.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Parameters.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Defs
import Complexitylib.Circuits.Majority
import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString
import Complexitylib.Metacomplexity.ScaledExponent

/-!
# Anti-Checker good-string parameter bridge -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem eventually_survivorTupleMajoritySizeBound_le_hardThreshold_internal
    (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      AntiChecker.survivorTupleMajoritySizeBound arity
          (smallThreshold beta arity) ≤
        hardThreshold beta arity := by
  have hpolynomial :=
    PositiveRationalScale.eventually_coefficient_mul_succ_pow_le_powFloor
      beta 50 2
  filter_upwards [hpolynomial, Filter.eventually_ge_atTop 1]
      with arity hpolynomial harity
  let : NeZero arity := ⟨by omega⟩
  have hsmallScaled :
      fixedConstant * (arity * smallThreshold beta arity) ≤
        hardThreshold beta arity := by
    unfold smallThreshold hardThreshold Parameters.yesThreshold
      Parameters.noThreshold gapParameters
    rw [← Nat.mul_assoc]
    exact Nat.mul_div_le _ _
  have hmajorityThreshold :
      CircuitCode.strictMajorityThreshold arity ≤ arity :=
    CircuitCode.strictMajorityThreshold_le arity
  have hoverheadScaled :
      fixedConstant *
          (3 + 2 * arity * CircuitCode.strictMajorityThreshold arity) ≤
        hardThreshold beta arity := by
    calc
      fixedConstant *
          (3 + 2 * arity * CircuitCode.strictMajorityThreshold arity) ≤
          fixedConstant * (3 + 2 * arity * arity) :=
        Nat.mul_le_mul_left fixedConstant
          (Nat.add_le_add_left
            (Nat.mul_le_mul_left (2 * arity) hmajorityThreshold) 3)
      _ ≤ 50 * (arity + 1) ^ 2 := by
        unfold fixedConstant
        nlinarith
      _ ≤ hardThreshold beta arity := by
        simpa [hardThreshold, gapParameters, Parameters.noThreshold] using
          hpolynomial
  have htotalScaled :
      fixedConstant *
          (arity * smallThreshold beta arity +
            (3 + 2 * arity *
              CircuitCode.strictMajorityThreshold arity)) ≤
        fixedConstant * hardThreshold beta arity := by
    rw [Nat.mul_add]
    calc
      fixedConstant * (arity * smallThreshold beta arity) +
          fixedConstant *
            (3 + 2 * arity *
              CircuitCode.strictMajorityThreshold arity) ≤
          hardThreshold beta arity + hardThreshold beta arity :=
        Nat.add_le_add hsmallScaled hoverheadScaled
      _ ≤ fixedConstant * hardThreshold beta arity := by
        unfold fixedConstant
        omega
  unfold AntiChecker.survivorTupleMajoritySizeBound
  exact Nat.le_of_mul_le_mul_left htotalScaled (by decide)

theorem eventually_hasShrinkExtension_of_isHardAt_internal
    (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ∀ (target : BitString arity → Bool)
          (inputs : List (BitString arity)),
        IsHardAt beta target →
          AntiChecker.HasShrinkExtension (2 * arity) target
            (smallThreshold beta arity) inputs := by
  filter_upwards
      [eventually_survivorTupleMajoritySizeBound_le_hardThreshold_internal
        beta,
      Filter.eventually_ge_atTop 8]
      with arity hfits harity
  intro target inputs hhard
  exact AntiChecker.hasShrinkExtension_two_mul_arity_of_circuitHardness
    harity target inputs hfits hhard

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
