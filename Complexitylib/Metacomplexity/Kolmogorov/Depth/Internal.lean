/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Depth.Defs
import Complexitylib.Metacomplexity.Kolmogorov.Internal

/-!
# Computational depth -- proof internals
-/


public section

namespace Complexity

theorem descriptionDifference_top_left_internal (lower : WithTop ℕ) :
    descriptionDifference ⊤ lower = ⊤ := by
  rfl

theorem descriptionDifference_top_right_internal (upper : WithTop ℕ) :
    descriptionDifference upper ⊤ = ⊤ := by
  induction upper using WithTop.recTopCoe <;> rfl

theorem descriptionDifference_coe_internal (upper lower : ℕ) :
    descriptionDifference (upper : WithTop ℕ) (lower : WithTop ℕ) =
      (upper - lower : ℕ) := by
  rfl

theorem descriptionDifference_add_lower_internal
    {upper lower : WithTop ℕ} (horder : lower ≤ upper) :
    descriptionDifference upper lower + lower = upper := by
  induction upper using WithTop.recTopCoe with
  | top => simp [descriptionDifference]
  | coe upper =>
      induction lower using WithTop.recTopCoe with
      | top => simp at horder
      | coe lower =>
          change ((upper - lower + lower : ℕ) : WithTop ℕ) = upper
          exact WithTop.coe_eq_coe.mpr <|
            Nat.sub_add_cancel (WithTop.coe_le_coe.mp horder)

theorem descriptionDifference_le_upper_internal
    {upper lower : WithTop ℕ} (horder : lower ≤ upper) :
    descriptionDifference upper lower ≤ upper := by
  induction upper using WithTop.recTopCoe with
  | top => exact le_top
  | coe upper =>
      induction lower using WithTop.recTopCoe with
      | top => simp at horder
      | coe lower =>
          exact WithTop.coe_le_coe.mpr (Nat.sub_le upper lower)

theorem descriptionDifference_mono_left_internal
    {lower first second : WithTop ℕ}
    (hlower : lower ≤ first) (hupper : first ≤ second) :
    descriptionDifference first lower ≤
      descriptionDifference second lower := by
  induction second using WithTop.recTopCoe with
  | top => exact le_top
  | coe second =>
      induction first using WithTop.recTopCoe with
      | top => simp at hupper
      | coe first =>
          induction lower using WithTop.recTopCoe with
          | top => simp at hlower
          | coe lower =>
              exact WithTop.coe_le_coe.mpr <|
                Nat.sub_le_sub_right (WithTop.coe_le_coe.mp hupper) lower

theorem descriptionDifference_anti_right_internal
    {upper firstLower secondLower : WithTop ℕ}
    (hlower : secondLower ≤ firstLower) (hupper : firstLower ≤ upper) :
    descriptionDifference upper firstLower ≤
      descriptionDifference upper secondLower := by
  induction upper using WithTop.recTopCoe with
  | top => simp [descriptionDifference]
  | coe upper =>
      induction firstLower using WithTop.recTopCoe with
      | top => simp at hupper
      | coe firstLower =>
          induction secondLower using WithTop.recTopCoe with
          | top => simp at hlower
          | coe secondLower =>
              exact WithTop.coe_le_coe.mpr <|
                Nat.sub_le_sub_left
                  (WithTop.coe_le_coe.mp hlower) upper

theorem descriptionDifference_eq_top_iff_internal
    {upper lower : WithTop ℕ} (horder : lower ≤ upper) :
    descriptionDifference upper lower = ⊤ ↔ upper = ⊤ := by
  induction upper using WithTop.recTopCoe with
  | top => simp [descriptionDifference]
  | coe upper =>
      induction lower using WithTop.recTopCoe with
      | top => simp at horder
      | coe lower =>
          simp only [descriptionDifference, WithTop.recTopCoe_coe]
          exact iff_of_false WithTop.coe_ne_top WithTop.coe_ne_top

theorem descriptionDifference_eq_zero_iff_internal
    {upper lower : WithTop ℕ} (horder : lower ≤ upper)
    (hfinite : upper ≠ ⊤) :
    descriptionDifference upper lower = 0 ↔ upper = lower := by
  have hlowerFinite : lower ≠ ⊤ := by
    intro hlower
    rw [hlower] at horder
    exact hfinite (top_unique horder)
  obtain ⟨upperValue, hupperValue⟩ := WithTop.ne_top_iff_exists.mp hfinite
  obtain ⟨lowerValue, hlowerValue⟩ :=
    WithTop.ne_top_iff_exists.mp hlowerFinite
  have hvalueOrder : lowerValue ≤ upperValue := by
    rw [← hlowerValue, ← hupperValue] at horder
    exact WithTop.coe_le_coe.mp horder
  rw [← hupperValue, ← hlowerValue]
  change ((upperValue - lowerValue : ℕ) : WithTop ℕ) = (0 : ℕ) ↔
    (upperValue : WithTop ℕ) = (lowerValue : ℕ)
  constructor
  · intro hzero
    apply WithTop.coe_eq_coe.mpr
    have hsub := WithTop.coe_eq_coe.mp hzero
    exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hsub) hvalueOrder
  · intro heq
    apply WithTop.coe_eq_coe.mpr
    have hvalues : upperValue = lowerValue := by
      exact WithTop.coe_injective heq
    simp [hvalues]

theorem descriptionDifference_add_internal
    {upper middle lower : WithTop ℕ}
    (hlower : lower ≤ middle) (hupper : middle ≤ upper) :
    descriptionDifference upper middle +
        descriptionDifference middle lower =
      descriptionDifference upper lower := by
  induction upper using WithTop.recTopCoe with
  | top => simp [descriptionDifference, WithTop.top_add]
  | coe upper =>
      induction middle using WithTop.recTopCoe with
      | top => simp at hupper
      | coe middle =>
          induction lower using WithTop.recTopCoe with
          | top => simp at hlower
          | coe lower =>
              change (((upper - middle) + (middle - lower) : ℕ) : WithTop ℕ) =
                ((upper - lower : ℕ) : WithTop ℕ)
              have hlowerValue : lower ≤ middle := by
                exact_mod_cast hlower
              have hupperValue : middle ≤ upper := by
                exact_mod_cast hupper
              have hidentity :
                  (upper - middle) + (middle - lower) = upper - lower := by
                omega
              exact congrArg (Nat.cast (R := WithTop ℕ)) hidentity
namespace TM
variable {n : ℕ}

theorem computationalDepthBetween_add_later_internal
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime laterTime +
        machine.timeBoundedKolmogorovComplexity output laterTime =
      machine.timeBoundedKolmogorovComplexity output firstTime := by
  exact descriptionDifference_add_lower_internal
    (timeBoundedKolmogorovComplexity_mono_internal
      machine output hclock)

theorem computationalDepthBetween_le_first_internal
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime laterTime ≤
      machine.timeBoundedKolmogorovComplexity output firstTime := by
  exact descriptionDifference_le_upper_internal
    (timeBoundedKolmogorovComplexity_mono_internal
      machine output hclock)

theorem computationalDepthBetween_eq_top_iff_internal
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime laterTime = ⊤ ↔
      machine.timeBoundedKolmogorovComplexity output firstTime = ⊤ := by
  exact descriptionDifference_eq_top_iff_internal
    (timeBoundedKolmogorovComplexity_mono_internal
      machine output hclock)

theorem computationalDepthBetween_mono_first_internal
    (machine : TM n) (output : List Bool)
    {firstTime secondTime laterTime : ℕ}
    (hfirst : firstTime ≤ secondTime) (hsecond : secondTime ≤ laterTime) :
    machine.computationalDepthBetween output secondTime laterTime ≤
      machine.computationalDepthBetween output firstTime laterTime := by
  apply descriptionDifference_mono_left_internal
  · exact timeBoundedKolmogorovComplexity_mono_internal
      machine output hsecond
  · exact timeBoundedKolmogorovComplexity_mono_internal
      machine output hfirst

theorem computationalDepthBetween_mono_later_internal
    (machine : TM n) (output : List Bool)
    {firstTime secondTime laterTime : ℕ}
    (hfirst : firstTime ≤ secondTime) (hsecond : secondTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime secondTime ≤
      machine.computationalDepthBetween output firstTime laterTime := by
  apply descriptionDifference_anti_right_internal
  · exact timeBoundedKolmogorovComplexity_mono_internal
      machine output hsecond
  · exact timeBoundedKolmogorovComplexity_mono_internal
      machine output hfirst

theorem computationalDepthBetween_eq_zero_iff_internal
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime)
    (hfinite : machine.timeBoundedKolmogorovComplexity output firstTime ≠ ⊤) :
    machine.computationalDepthBetween output firstTime laterTime = 0 ↔
      machine.timeBoundedKolmogorovComplexity output firstTime =
        machine.timeBoundedKolmogorovComplexity output laterTime := by
  exact descriptionDifference_eq_zero_iff_internal
    (timeBoundedKolmogorovComplexity_mono_internal
      machine output hclock) hfinite

theorem computationalDepthBetween_eq_computationalDepth_internal
    (machine : TM n) (output : List Bool) (firstTime laterTime : ℕ)
    (hlater : machine.timeBoundedKolmogorovComplexity output laterTime =
      machine.plainKolmogorovComplexity output) :
    machine.computationalDepthBetween output firstTime laterTime =
      machine.computationalDepth output firstTime := by
  rw [computationalDepthBetween, computationalDepth, hlater]

theorem computationalDepthBetween_add_internal
    (machine : TM n) (output : List Bool)
    {firstTime secondTime laterTime : ℕ}
    (hfirst : firstTime ≤ secondTime) (hsecond : secondTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime secondTime +
        machine.computationalDepthBetween output secondTime laterTime =
      machine.computationalDepthBetween output firstTime laterTime := by
  exact descriptionDifference_add_internal
    (timeBoundedKolmogorovComplexity_mono_internal
      machine output hsecond)
    (timeBoundedKolmogorovComplexity_mono_internal
      machine output hfirst)

theorem computationalDepth_add_plain_internal
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time +
        machine.plainKolmogorovComplexity output =
      machine.timeBoundedKolmogorovComplexity output time := by
  exact descriptionDifference_add_lower_internal
    (plainKolmogorovComplexity_le_timeBounded_internal machine output time)

theorem computationalDepth_le_timeBoundedKolmogorovComplexity_internal
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time ≤
      machine.timeBoundedKolmogorovComplexity output time := by
  exact descriptionDifference_le_upper_internal
    (plainKolmogorovComplexity_le_timeBounded_internal machine output time)

theorem computationalDepth_eq_top_iff_internal
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time = ⊤ ↔
      machine.timeBoundedKolmogorovComplexity output time = ⊤ := by
  exact descriptionDifference_eq_top_iff_internal
    (plainKolmogorovComplexity_le_timeBounded_internal machine output time)

theorem computationalDepth_mono_internal
    (machine : TM n) (output : List Bool)
    {first second : ℕ} (hclock : first ≤ second) :
    machine.computationalDepth output second ≤
      machine.computationalDepth output first := by
  apply descriptionDifference_mono_left_internal
  · exact plainKolmogorovComplexity_le_timeBounded_internal
      machine output second
  · exact timeBoundedKolmogorovComplexity_mono_internal
      machine output hclock

theorem computationalDepth_eq_zero_iff_internal
    (machine : TM n) (output : List Bool) (time : ℕ)
    (hfinite : machine.timeBoundedKolmogorovComplexity output time ≠ ⊤) :
    machine.computationalDepth output time = 0 ↔
      machine.timeBoundedKolmogorovComplexity output time =
        machine.plainKolmogorovComplexity output := by
  exact descriptionDifference_eq_zero_iff_internal
    (plainKolmogorovComplexity_le_timeBounded_internal machine output time)
    hfinite

end TM

end Complexity
