/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Weak.Defs
public import Mathlib.Data.Nat.Log

/-!
# Weak approximate counting -- proof internals
-/


public section

namespace Complexity

namespace ApproximateCounting

namespace Weak

theorem estimate_lt_two_pow_add_four_internal {domainWidth : ℕ}
    (responses : Level domainWidth → Bool) :
    estimate responses < 2 ^ (domainWidth + 4) := by
  unfold estimate
  split
  · apply Nat.pow_lt_pow_right (by omega)
    exact (selectedLevel responses).isLt
  · exact Nat.two_pow_pos _

theorem mem_trueLevels_iff_internal {domainWidth : ℕ}
    {responses : Level domainWidth → Bool} {level : Level domainWidth} :
    level ∈ trueLevels responses ↔ responses level = true := by
  simp [trueLevels]

theorem selectedLevel_mem_trueLevels_internal {domainWidth : ℕ}
    {responses : Level domainWidth → Bool}
    (hnonempty : (trueLevels responses).Nonempty) :
    selectedLevel responses ∈ trueLevels responses := by
  simp only [selectedLevel, dite_eq_left hnonempty]
  exact Finset.max'_mem _ _

theorem le_selectedLevel_of_mem_internal {domainWidth : ℕ}
    {responses : Level domainWidth → Bool} {level : Level domainWidth}
    (hlevel : level ∈ trueLevels responses) :
    level ≤ selectedLevel responses := by
  have hnonempty : (trueLevels responses).Nonempty := ⟨level, hlevel⟩
  simp only [selectedLevel, dite_eq_left hnonempty]
  exact Finset.le_max' _ _ hlevel

theorem response_selectedLevel_eq_true_of_nonempty_internal {domainWidth : ℕ}
    {responses : Level domainWidth → Bool}
    (hnonempty : (trueLevels responses).Nonempty) :
    responses (selectedLevel responses) = true :=
  mem_trueLevels_iff_internal.mp
    (selectedLevel_mem_trueLevels_internal hnonempty)

theorem estimate_eq_zero_of_cardinality_eq_zero_internal
    {domainWidth cardinality : ℕ} {responses : Level domainWidth → Bool}
    (haccurate : ResponsesAccurate (cardinality := cardinality) responses)
    (hzero : cardinality = 0) :
    estimate responses = 0 := by
  subst cardinality
  have hresponse : responses (zeroLevel domainWidth) = false := by
    simpa using haccurate.1
  simp [estimate, hresponse]

theorem estimate_eq_pow_of_cardinality_pos_internal
    {domainWidth cardinality : ℕ} {responses : Level domainWidth → Bool}
    (haccurate : ResponsesAccurate (cardinality := cardinality) responses)
    (hpositive : 0 < cardinality) :
    estimate responses = 2 ^ (selectedLevel responses).val := by
  have hresponse : responses (zeroLevel domainWidth) = true := by
    simpa [hpositive] using haccurate.1
  simp [estimate, hresponse]

theorem selectedLevel_response_eq_true_of_cardinality_pos_internal
    {domainWidth cardinality : ℕ} {responses : Level domainWidth → Bool}
    (haccurate : ResponsesAccurate (cardinality := cardinality) responses)
    (hpositive : 0 < cardinality) :
    responses (selectedLevel responses) = true := by
  have hzeroResponse : responses (zeroLevel domainWidth) = true := by
    simpa [hpositive] using haccurate.1
  have hzeroMem : zeroLevel domainWidth ∈ trueLevels responses :=
    mem_trueLevels_iff_internal.mpr hzeroResponse
  exact response_selectedLevel_eq_true_of_nonempty_internal ⟨_, hzeroMem⟩

theorem estimate_le_sixteen_mul_internal
    {domainWidth cardinality : ℕ} {responses : Level domainWidth → Bool}
    (haccurate : ResponsesAccurate (cardinality := cardinality) responses) :
    estimate responses ≤ 16 * cardinality := by
  by_cases hzero : cardinality = 0
  · simp [estimate_eq_zero_of_cardinality_eq_zero_internal haccurate hzero,
      hzero]
  · have hpositive : 0 < cardinality := Nat.pos_of_ne_zero hzero
    have hselected :=
      selectedLevel_response_eq_true_of_cardinality_pos_internal haccurate
        hpositive
    have hnotLow : ¬ 8 * cardinality ≤ 2 ^ (selectedLevel responses).val := by
      intro hlow
      have hfalse := haccurate.2.2 (selectedLevel responses) hlow
      simp [hselected] at hfalse
    rw [estimate_eq_pow_of_cardinality_pos_internal haccurate hpositive]
    omega

theorem cardinality_le_sixteen_mul_estimate_internal
    {domainWidth cardinality : ℕ} {responses : Level domainWidth → Bool}
    (hcardinality : cardinality ≤ 2 ^ domainWidth)
    (haccurate : ResponsesAccurate (cardinality := cardinality) responses) :
    cardinality ≤ 16 * estimate responses := by
  by_cases hzero : cardinality = 0
  · simp [hzero]
  · have hpositive : 0 < cardinality := Nat.pos_of_ne_zero hzero
    rw [estimate_eq_pow_of_cardinality_pos_internal haccurate hpositive]
    by_cases hsmall : cardinality < 8
    · have hpowPositive : 0 < 2 ^ (selectedLevel responses).val :=
        Nat.pow_pos (by omega)
      omega
    · have hlarge : 8 ≤ cardinality := by omega
      let logarithm := Nat.log 2 (cardinality / 8)
      have hquotientPositive : 0 < cardinality / 8 :=
        Nat.div_pos hlarge (by omega)
      have hlogarithmLe : logarithm ≤ domainWidth := by
        dsimp only [logarithm]
        calc
          Nat.log 2 (cardinality / 8) ≤ Nat.log 2 cardinality :=
            Nat.log_mono_right (Nat.div_le_self cardinality 8)
          _ ≤ Nat.log 2 (2 ^ domainWidth) :=
            Nat.log_mono_right hcardinality
          _ = domainWidth := Nat.log_pow (by omega) domainWidth
      have hlogarithmLt : logarithm < domainWidth + 4 := by omega
      let level : Level domainWidth := ⟨logarithm, hlogarithmLt⟩
      have hlevelHigh : 8 * 2 ^ level.val ≤ cardinality := by
        have hpowDiv : 2 ^ level.val ≤ cardinality / 8 := by
          simpa [level, logarithm] using
            Nat.pow_log_le_self 2 hquotientPositive.ne'
        have := (Nat.le_div_iff_mul_le (by omega : 0 < 8)).mp hpowDiv
        simpa [Nat.mul_comm] using this
      have hlevelResponse : responses level = true :=
        haccurate.2.1 level hlevelHigh
      have hlevelMem : level ∈ trueLevels responses :=
        mem_trueLevels_iff_internal.mpr hlevelResponse
      have hlevelLe : level ≤ selectedLevel responses :=
        le_selectedLevel_of_mem_internal hlevelMem
      have hpowLe : 2 ^ logarithm ≤ 2 ^ (selectedLevel responses).val := by
        apply Nat.pow_le_pow_right (by omega)
        exact Fin.le_def.mp hlevelLe
      have hquotientLt : cardinality / 8 < 2 ^ logarithm.succ := by
        simpa [logarithm] using
          Nat.lt_pow_succ_log_self (by omega) (cardinality / 8)
      have hcardinalityLt : cardinality < 2 ^ logarithm.succ * 8 :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < 8)).mp hquotientLt
      rw [Nat.pow_succ] at hcardinalityLt
      omega

theorem estimate_isFactorApproximation_internal
    {domainWidth cardinality : ℕ} {responses : Level domainWidth → Bool}
    (hcardinality : cardinality ≤ 2 ^ domainWidth)
    (haccurate : ResponsesAccurate (cardinality := cardinality) responses) :
    IsFactorApproximation 16 cardinality (estimate responses) :=
  ⟨estimate_le_sixteen_mul_internal haccurate,
    cardinality_le_sixteen_mul_estimate_internal hcardinality haccurate⟩

end Weak

end ApproximateCounting

end Complexity
