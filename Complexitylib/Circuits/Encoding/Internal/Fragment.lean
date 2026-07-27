/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Internal.Codec
public import Complexitylib.Circuits.Encoding.Fragment.Defs
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Internal laws for appendable raw-circuit fragments

This module proves generic composition and prefix-preservation facts for the
iterative raw-circuit evaluator. The statements are exposed by
`Complexitylib.Circuits.Encoding.Fragment`.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace RawGate

/-- Internal semantic equation for duplicated-input copy gates. -/
theorem eval_copy_internal (input : ℕ) (negated value : Bool) :
    (copy input negated).eval value value = negated.xor value := by
  cases negated <;> cases value <;> rfl

/-- Internal semantic equation for dual-input constant gates. -/
theorem eval_constant_internal (input : ℕ) (constantValue wireValue : Bool) :
    (constant input constantValue).eval wireValue wireValue = constantValue := by
  cases constantValue <;> cases wireValue <;> rfl

end RawGate

namespace RawCircuit

/-- Internal append law for iterative raw evaluation. -/
theorem evalAux?_append_internal (first second : RawCircuit) (wires : Array Bool) :
    evalAux? (first ++ second) wires =
      (evalAux? first wires).bind (evalAux? second) := by
  induction first generalizing wires with
  | nil => simp [evalAux?]
  | cons gate gates ih =>
      simp only [List.cons_append, evalAux?]
      cases hvalue₀ : wires[gate.input₀]? with
      | none => simp
      | some value₀ =>
          cases hvalue₁ : wires[gate.input₁]? <;> simp [ih]

/-- Internal topological decomposition for appended raw fragments. -/
theorem topologicallyWellFormed_append_internal (available : ℕ)
    (first second : RawCircuit) :
    TopologicallyWellFormed available (first ++ second) ↔
      TopologicallyWellFormed available first ∧
        TopologicallyWellFormed (available + first.length) second := by
  induction first generalizing available with
  | nil => simp [TopologicallyWellFormed]
  | cons gate gates ih =>
      rw [List.cons_append, topologicallyWellFormed_cons,
        topologicallyWellFormed_cons, ih]
      simp only [List.length_cons]
      constructor
      · rintro ⟨hgate, hgates, hsecond⟩
        exact ⟨⟨hgate, hgates⟩, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsecond⟩
      · rintro ⟨⟨hgate, hgates⟩, hsecond⟩
        exact ⟨hgate, hgates, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsecond⟩

/-- Internal proof that raw evaluation only appends memo entries. -/
theorem evalAux?_preserves_prefix_internal {circuit : RawCircuit}
    {wires result : Array Bool} (heval : evalAux? circuit wires = some result)
    {i : ℕ} (hi : i < wires.size) : result[i]? = wires[i]? := by
  induction circuit generalizing wires result with
  | nil =>
      simp only [evalAux?] at heval
      cases heval
      rfl
  | cons gate gates ih =>
      cases hvalue₀ : wires[gate.input₀]? with
      | none => simp [evalAux?, hvalue₀] at heval
      | some value₀ =>
          cases hvalue₁ : wires[gate.input₁]? with
          | none => simp [evalAux?, hvalue₀, hvalue₁] at heval
          | some value₁ =>
              simp only [evalAux?, hvalue₀, hvalue₁] at heval
              have hpreserved := ih heval (by simp only [Array.size_push]; omega)
              rw [Array.getElem?_push, if_neg (by omega)] at hpreserved
              exact hpreserved

end RawCircuit

end CircuitCode

end Complexity
