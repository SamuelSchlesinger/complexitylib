/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthClasses.Defs
public import Complexitylib.Circuits.BasisHom
public import Complexitylib.Circuits.Family
public import Complexitylib.Circuits.Threshold

/-!
# Circuit depth classes -- proof internals
-/


public section

namespace Complexity

theorem polylogDepth_zero_internal (c n : ℕ) :
    polylogDepth 0 c n = c := by
  simp [polylogDepth]

theorem polylogDepth_one_internal (c n : ℕ) :
    polylogDepth 1 c n = c * Nat.log 2 n + c := by
  simp [polylogDepth, Nat.mul_add]

theorem polylogDepth_mono_constant_internal {c c' : ℕ} (hcc' : c ≤ c')
    (i n : ℕ) :
    polylogDepth i c n ≤ polylogDepth i c' n := by
  exact Nat.mul_le_mul_right ((Nat.log 2 n + 1) ^ i) hcc'

theorem polylogDepth_mono_exponent_internal {i j : ℕ} (hij : i ≤ j)
    (c n : ℕ) :
    polylogDepth i c n ≤ polylogDepth j c n := by
  apply Nat.mul_le_mul_left c
  exact pow_le_pow_right' (by omega) hij

theorem DEPTHWithBasis_mono_internal (B : Basis) {d e : ℕ → ℕ}
    (hde : ∀ n, d n ≤ e n) :
    DEPTHWithBasis B d ⊆ DEPTHWithBasis B e := by
  rintro f ⟨F, hcomputes, hdepth⟩
  exact ⟨F, hcomputes, F.depthBoundedBy_mono hdepth hde⟩

theorem NC_mono_internal {i j : ℕ} (hij : i ≤ j) :
    NC i ⊆ NC j := by
  rintro f ⟨F, c, hcomputes, hsize, hdepth⟩
  refine ⟨F, c, hcomputes, hsize, F.depthBoundedBy_mono hdepth ?_⟩
  exact fun n => polylogDepth_mono_exponent_internal hij c n

theorem AC_mono_internal {i j : ℕ} (hij : i ≤ j) :
    AC i ⊆ AC j := by
  rintro f ⟨F, c, hcomputes, hsize, hdepth⟩
  refine ⟨F, c, hcomputes, hsize, F.depthBoundedBy_mono hdepth ?_⟩
  exact fun n => polylogDepth_mono_exponent_internal hij c n

theorem TC_mono_internal {i j : ℕ} (hij : i ≤ j) :
    TC i ⊆ TC j := by
  rintro f ⟨F, c, hcomputes, hsize, hdepth⟩
  refine ⟨F, c, hcomputes, hsize,
    F.depthBoundedBy_mono hdepth ?_⟩
  exact fun n =>
    polylogDepth_mono_exponent_internal hij c n

theorem AC_subset_TC_internal (i : ℕ) :
    AC i ⊆ TC i := by
  rintro f ⟨F, c, hcomputes, hsize, hdepth⟩
  let thresholdFamily :=
    F.mapBasis Basis.andOrToThresholdHom
  refine ⟨thresholdFamily, c, ?_, ?_, ?_⟩
  · exact (CircuitFamily.function_mapBasis
      Basis.andOrToThresholdHom F).trans hcomputes
  · obtain ⟨polynomial, hpolynomial⟩ := hsize
    refine ⟨polynomial, fun n => ?_⟩
    rw [show thresholdFamily.size n = F.size n by
      exact congrFun
        (CircuitFamily.size_mapBasis
          Basis.andOrToThresholdHom F) n]
    exact hpolynomial n
  · intro n
    rw [show thresholdFamily.depth n = F.depth n by
      exact congrFun
        (CircuitFamily.depth_mapBasis
          Basis.andOrToThresholdHom F) n]
    exact hdepth n

theorem mem_NC1_iff_internal {f : BoolFunFamily} :
    f ∈ NC1 ↔
      ∃ (F : CircuitFamily Basis.andOr2) (c : ℕ),
        F.Computes f ∧ F.PolynomialSize ∧
          F.DepthBoundedBy (fun n => c * Nat.log 2 n + c) := by
  simp only [NC1, NC, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨F, c, hcomputes, hsize, hdepth⟩
    exact ⟨F, c, hcomputes, hsize, fun n => by
      simpa only [polylogDepth_one_internal] using hdepth n⟩
  · rintro ⟨F, c, hcomputes, hsize, hdepth⟩
    exact ⟨F, c, hcomputes, hsize, fun n => by
      simpa only [polylogDepth_one_internal] using hdepth n⟩

theorem mem_AC0_iff_internal {f : BoolFunFamily} :
    f ∈ AC0 ↔
      ∃ (F : CircuitFamily Basis.unboundedAndOr) (c : ℕ),
        F.Computes f ∧ F.PolynomialSize ∧
          F.DepthBoundedBy (fun _ => c) := by
  simp only [AC0, AC, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨F, c, hcomputes, hsize, hdepth⟩
    exact ⟨F, c, hcomputes, hsize, fun n => by
      simpa only [polylogDepth_zero_internal] using hdepth n⟩
  · rintro ⟨F, c, hcomputes, hsize, hdepth⟩
    exact ⟨F, c, hcomputes, hsize, fun n => by
      simpa only [polylogDepth_zero_internal] using hdepth n⟩

theorem mem_TC0_iff_internal {f : BoolFunFamily} :
    f ∈ TC0 ↔
      ∃ (F : CircuitFamily Basis.threshold) (c : ℕ),
        F.Computes f ∧ F.PolynomialSize ∧
          F.DepthBoundedBy (fun _ => c) := by
  simp only [TC0, TC, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨F, c, hcomputes, hsize, hdepth⟩
    exact ⟨F, c, hcomputes, hsize, fun n => by
      simpa only [polylogDepth_zero_internal] using hdepth n⟩
  · rintro ⟨F, c, hcomputes, hsize, hdepth⟩
    exact ⟨F, c, hcomputes, hsize, fun n => by
      simpa only [polylogDepth_zero_internal] using hdepth n⟩

end Complexity
