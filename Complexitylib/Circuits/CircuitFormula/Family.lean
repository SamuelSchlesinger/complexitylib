/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BarringtonTyped
public import Complexitylib.Circuits.CircuitFormula.Family.Defs
public import Complexitylib.Circuits.CircuitFormula.Family.Internal

/-!
# Circuit-family outputs as formula families

This module lifts selected-output circuit unfolding to total families. A typed
fan-in-two circuit family yields a formula family with identical semantics and
at most twice its depth. Its formulas also read only their declared inputs.
Consequently every `NC1` Boolean-function family lies in the typed
`FormulaNC1` class and hence in the typed width-`5` class `Width5BP`.

The explicitly named total-assignment bridge remains available for clients
whose functions genuinely have domain `ℕ → Bool`.

No formula-size bound is used: shared circuit DAGs may expand exponentially
when unfolded. Barrington's construction depends on formula depth, which the
translation controls directly.
-/

@[expose] public section

namespace Complexity

namespace Circuit

/-- A single-output circuit's global depth is the depth of its unique output. -/
theorem depth_eq_outputDepth_zero {N G : ℕ} [NeZero N]
    (circuit : Circuit Basis.andOr2 N 1 G) :
    circuit.depth = circuit.outputDepth 0 :=
  depth_eq_outputDepth_zero_internal circuit

end Circuit

namespace CircuitFamily

/-- The unfolded formula at length `n` has exactly the circuit family's
length-`n` semantics on the corresponding total assignment. -/
theorem eval_outputFormulaFamily
    (F : CircuitFamily Basis.andOr2) (n : ℕ) (assignment : ℕ → Bool) :
    BoolFormula.eval assignment (F.outputFormulaFamily n) =
      F.function n (fun input => assignment input.val) :=
  eval_outputFormulaFamily_internal F n assignment

/-- Family-level selected-output unfolding increases depth by at most a factor
of two. -/
theorem depth_outputFormulaFamily_le
    (F : CircuitFamily Basis.andOr2) (n : ℕ) :
    (F.outputFormulaFamily n).depth ≤ 2 * F.depth n :=
  depth_outputFormulaFamily_le_internal F n

/-- Every variable mentioned by the unfolded length-`n` formula lies below
the declared input arity `n`. -/
theorem outputFormulaFamily_variables_lt
    (F : CircuitFamily Basis.andOr2) (n index : ℕ)
    (hindex : index ∈ (F.outputFormulaFamily n).vars) :
    index < n :=
  outputFormulaFamily_variables_lt_internal F n index hindex

/-- Package circuit-output unfolding as a genuinely fixed-arity formula
family. -/
def fixedArityOutputFormulaFamily
    (F : CircuitFamily Basis.andOr2) : FixedArityFormulaFamily where
  formula := F.outputFormulaFamily
  variables_lt := F.outputFormulaFamily_variables_lt

/-- The fixed-arity unfolded formula family has exactly the source circuit
family's typed semantics. -/
theorem function_fixedArityOutputFormulaFamily
    (F : CircuitFamily Basis.andOr2) :
    F.fixedArityOutputFormulaFamily.function = F.function := by
  funext n input
  simpa [fixedArityOutputFormulaFamily,
    FixedArityFormulaFamily.function] using
    F.eval_outputFormulaFamily n input.toTotal

/-- The fixed-arity formula packaging preserves the factor-two depth bound. -/
theorem depth_fixedArityOutputFormulaFamily_le
    (F : CircuitFamily Basis.andOr2) (n : ℕ) :
    F.fixedArityOutputFormulaFamily.depth n ≤ 2 * F.depth n :=
  F.depth_outputFormulaFamily_le n

/-- Unfolding a circuit family computes its total-assignment semantics. -/
theorem outputFormulaFamily_computes
    {F : CircuitFamily Basis.andOr2} {f : BoolFunFamily}
    (hcomputes : F.Computes f) :
    F.outputFormulaFamily.ComputesOnTotalAssignments
      f.onTotalAssignments :=
  outputFormulaFamily_computes_internal hcomputes

/-- A `c * log₂ n + c` circuit-depth bound produces a logarithmic-depth
formula family. -/
theorem outputFormulaFamily_logDepth
    {F : CircuitFamily Basis.andOr2} {c : ℕ}
    (hdepth : F.DepthBoundedBy fun n => c * Nat.log 2 n + c) :
    F.outputFormulaFamily.LogDepth :=
  outputFormulaFamily_logDepth_internal hdepth

/-- A logarithmic circuit-depth bound gives a logarithmic-depth fixed-arity
formula family. -/
theorem fixedArityOutputFormulaFamily_logDepth
    {F : CircuitFamily Basis.andOr2} {c : ℕ}
    (hdepth : F.DepthBoundedBy fun n => c * Nat.log 2 n + c) :
    F.fixedArityOutputFormulaFamily.LogDepth := by
  refine ⟨2 * c, fun n => ?_⟩
  calc
    F.fixedArityOutputFormulaFamily.depth n
        ≤ 2 * F.depth n :=
      F.depth_fixedArityOutputFormulaFamily_le n
    _ ≤ 2 * (c * Nat.log 2 n + c) :=
      Nat.mul_le_mul_left 2 (hdepth n)
    _ = (2 * c) * Nat.log 2 n + 2 * c := by ring

end CircuitFamily

/-- Every typed `NC1` circuit family has a variable-bounded,
logarithmic-depth formula family. -/
theorem NC1_subset_FormulaNC1 : NC1 ⊆ FormulaNC1 := by
  intro f hf
  rw [mem_NC1_iff] at hf
  obtain ⟨F, c, hcomputes, -, hdepth⟩ := hf
  exact ⟨F.fixedArityOutputFormulaFamily,
    F.fixedArityOutputFormulaFamily_logDepth hdepth,
    (F.function_fixedArityOutputFormulaFamily).trans hcomputes⟩

/-- Every typed `NC1` circuit family has a variable-bounded,
polynomial-length width-`5` permutation branching-program family. -/
theorem NC1_subset_Width5BP : NC1 ⊆ Width5BP :=
  NC1_subset_FormulaNC1.trans formulaNC1_subset_width5BP

/-- Pointwise typed Barrington theorem for an `NC1` Boolean-function family. -/
theorem BoolFunFamily.mem_Width5BP
    {f : BoolFunFamily} (hf : f ∈ NC1) :
    f ∈ Width5BP :=
  NC1_subset_Width5BP hf

/-- The total-assignment views of `NC1` Boolean-function families are
logarithmic-depth formula families. -/
theorem NC1_onTotalAssignments_subset_FormulaNC1OnTotalAssignments :
    BoolFunFamily.onTotalAssignments '' NC1 ⊆
      FormulaNC1OnTotalAssignments :=
  NC1_onTotalAssignments_subset_FormulaNC1OnTotalAssignments_internal

/-- Pointwise form of the bridge from typed `NC1` circuit families to
logarithmic-depth formula families. -/
theorem BoolFunFamily.onTotalAssignments_mem_FormulaNC1OnTotalAssignments
    {f : BoolFunFamily} (hf : f ∈ NC1) :
    f.onTotalAssignments ∈ FormulaNC1OnTotalAssignments :=
  NC1_onTotalAssignments_subset_FormulaNC1OnTotalAssignments
    ⟨f, hf, rfl⟩

/-- **Barrington for typed `NC1` circuit families.** Their total-assignment
views have polynomial-length width-`5` permutation branching programs. -/
theorem NC1_onTotalAssignments_subset_Width5BPOnTotalAssignments :
    BoolFunFamily.onTotalAssignments '' NC1 ⊆
      Width5BPOnTotalAssignments :=
  NC1_onTotalAssignments_subset_FormulaNC1OnTotalAssignments.trans
    formulaNC1OnTotalAssignments_subset_width5BPOnTotalAssignments

/-- Pointwise Barrington theorem for a typed `NC1` Boolean-function family. -/
theorem BoolFunFamily.onTotalAssignments_mem_Width5BPOnTotalAssignments
    {f : BoolFunFamily} (hf : f ∈ NC1) :
    f.onTotalAssignments ∈ Width5BPOnTotalAssignments :=
  NC1_onTotalAssignments_subset_Width5BPOnTotalAssignments
    ⟨f, hf, rfl⟩

end Complexity
