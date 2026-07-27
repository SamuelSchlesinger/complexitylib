/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.CircuitFormula
public import Complexitylib.Circuits.CircuitFormula.Family.Defs
public import Complexitylib.Circuits.DepthClasses

/-!
# Circuit-family outputs as formula families -- proof internals
-/

@[expose] public section

namespace Complexity

namespace Circuit

theorem depth_eq_outputDepth_zero_internal {N G : ℕ} [NeZero N]
    (circuit : Circuit Basis.andOr2 N 1 G) :
    circuit.depth = circuit.outputDepth 0 := by
  unfold Circuit.depth
  rw [Fin.foldl_succ_last]
  simp [Fin.foldl_zero]

end Circuit

namespace CircuitFamily

theorem eval_outputFormulaFamily_internal
    (F : CircuitFamily Basis.andOr2) (n : ℕ) (assignment : ℕ → Bool) :
    BoolFormula.eval assignment (F.outputFormulaFamily n) =
      F.function n (fun input => assignment input.val) := by
  cases n with
  | zero =>
      cases houtput : F.emptyOutput <;>
        simp [outputFormulaFamily, CircuitFamily.function, houtput, BoolFormula.eval]
  | succ n =>
      exact Circuit.eval_outputFormula (F.circuit (n + 1)) assignment 0

theorem depth_outputFormulaFamily_le_internal
    (F : CircuitFamily Basis.andOr2) (n : ℕ) :
    (F.outputFormulaFamily n).depth ≤ 2 * F.depth n := by
  cases n with
  | zero =>
      cases houtput : F.emptyOutput <;>
        simp [outputFormulaFamily, CircuitFamily.depth, houtput, BoolFormula.depth]
  | succ n =>
      rw [outputFormulaFamily, CircuitFamily.depth_succ,
        Circuit.depth_eq_outputDepth_zero_internal]
      exact Circuit.depth_outputFormula_le_outputDepth (F.circuit (n + 1)) 0

theorem outputFormulaFamily_variables_lt_internal
    (F : CircuitFamily Basis.andOr2) (n index : ℕ)
    (hindex : index ∈ (F.outputFormulaFamily n).vars) :
    index < n := by
  cases n with
  | zero =>
      cases houtput : F.emptyOutput <;>
        simp [outputFormulaFamily, houtput, BoolFormula.vars] at hindex
  | succ n =>
      exact Circuit.vars_outputFormula_lt
        (F.circuit (n + 1)) 0 index hindex

theorem outputFormulaFamily_computes_internal
    {F : CircuitFamily Basis.andOr2} {f : BoolFunFamily}
    (hcomputes : F.Computes f) :
    F.outputFormulaFamily.ComputesOnTotalAssignments
      f.onTotalAssignments := by
  intro n assignment
  rw [eval_outputFormulaFamily_internal]
  exact CircuitFamily.Computes.apply hcomputes n
    (fun input => assignment input.val)

theorem outputFormulaFamily_logDepth_internal
    {F : CircuitFamily Basis.andOr2} {c : ℕ}
    (hdepth : F.DepthBoundedBy fun n => c * Nat.log 2 n + c) :
    F.outputFormulaFamily.LogDepth := by
  refine ⟨2 * c, fun n => ?_⟩
  calc
    (F.outputFormulaFamily n).depth
        ≤ 2 * F.depth n := depth_outputFormulaFamily_le_internal F n
    _ ≤ 2 * (c * Nat.log 2 n + c) := Nat.mul_le_mul_left 2 (hdepth n)
    _ = (2 * c) * Nat.log 2 n + 2 * c := by ring

end CircuitFamily

theorem NC1_onTotalAssignments_subset_FormulaNC1OnTotalAssignments_internal :
    BoolFunFamily.onTotalAssignments '' NC1 ⊆
      FormulaNC1OnTotalAssignments := by
  rintro _ ⟨f, hf, rfl⟩
  rw [mem_NC1_iff] at hf
  obtain ⟨F, c, hcomputes, -, hdepth⟩ := hf
  exact ⟨F.outputFormulaFamily,
    CircuitFamily.outputFormulaFamily_logDepth_internal hdepth,
    CircuitFamily.outputFormulaFamily_computes_internal hcomputes⟩

end Complexity
