/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Shannon
public import Complexitylib.Metacomplexity.MCSP

/-!
# Shannon bounds for canonical MCSP -- proof internals

This module transports the library's exact Shannon circuit bounds to the
canonical MCSP truth-table encoding.
-/


public section

namespace Complexity

namespace MCSP

theorem exists_minimumSize_gt_shannonLower_internal
    (arity : ℕ) (harity : 6 ≤ arity) :
    ∃ inst : Instance,
      inst.arity = arity ∧
        inst.threshold = 2 ^ arity / (5 * arity) ∧
          inst.minimumSize > 2 ^ arity / (5 * arity) := by
  let : NeZero arity := ⟨by omega⟩
  obtain ⟨f, hf⟩ := shannon_sizeComplexity arity harity
  let inst := Instance.ofFunction arity (2 ^ arity / (5 * arity)) f
  refine ⟨inst, rfl, rfl, ?_⟩
  let : NeZero inst.arity :=
    ⟨by simpa [inst] using (NeZero.ne arity)⟩
  rw [Instance.minimumSize_eq_sizeComplexity]
  simpa [inst] using hf

theorem exists_not_mem_at_shannonLower_internal
    (arity : ℕ) (harity : 6 ≤ arity) :
    ∃ inst : Instance,
      inst.arity = arity ∧
        inst.threshold = 2 ^ arity / (5 * arity) ∧
          inst.encode ∉ Complexity.MCSP := by
  obtain ⟨inst, hinstArity, hthreshold, hminimum⟩ :=
    exists_minimumSize_gt_shannonLower_internal arity harity
  refine ⟨inst, hinstArity, hthreshold, ?_⟩
  rw [Complexity.MCSP.mem_encode_iff_minimumSize_le]
  omega

theorem exists_ofFunction_not_mem_at_shannonLower_internal
    (arity : ℕ) (harity : 6 ≤ arity) :
    ∃ f : BitString arity → Bool,
      (Instance.ofFunction arity (2 ^ arity / (5 * arity)) f).encode ∉
        Complexity.MCSP := by
  let : NeZero arity := ⟨by omega⟩
  obtain ⟨f, hf⟩ := shannon_sizeComplexity arity harity
  refine ⟨f, ?_⟩
  let : NeZero
      (Instance.ofFunction arity (2 ^ arity / (5 * arity)) f).arity :=
    ⟨by simpa using (NeZero.ne arity)⟩
  rw [Complexity.MCSP.mem_encode_iff_sizeComplexity_le]
  simpa using (not_le_of_gt hf)

theorem mem_encode_of_shannonUpper_le_threshold_internal
    (inst : Instance) (harity : 16 ≤ inst.arity)
    (hthreshold : 18 * 2 ^ inst.arity / inst.arity ≤ inst.threshold) :
    inst.encode ∈ Complexity.MCSP := by
  let : NeZero inst.arity := ⟨by omega⟩
  rw [Complexity.MCSP.mem_encode_iff_sizeComplexity_le]
  exact (shannon_upper_bound inst.arity harity inst.function).trans hthreshold

theorem ofFunction_mem_at_shannonUpper_internal
    (arity : ℕ) (harity : 16 ≤ arity) (f : BitString arity → Bool) :
    (Instance.ofFunction arity (18 * 2 ^ arity / arity) f).encode ∈
      Complexity.MCSP := by
  apply mem_encode_of_shannonUpper_le_threshold_internal
  · simpa
  · simp

end MCSP

end Complexity
