/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Internal.Codec
public import Complexitylib.Circuits.Encoding.Fragment.Defs

/-!
# Internal laws for appendable raw-circuit fragments

This module proves generic composition and prefix-preservation facts for the
iterative raw-circuit evaluator. The statements are exposed by
`Complexitylib.Circuits.Encoding.Fragment`.
-/


public section

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

/-- Appending a copy gate to a nonempty circuit maps its original output by
the gate's optional negation. -/
theorem eval?_append_copy_internal (circuit : RawCircuit)
    (input : List Bool) (negated : Bool) (hnonempty : circuit ≠ []) :
    (circuit ++
        [RawGate.copy (input.length + circuit.length - 1) negated]).eval?
          input =
      (circuit.eval? input).map (fun value => negated.xor value) := by
  have hlength : 0 < circuit.length :=
    Nat.pos_of_ne_zero (by
      intro hzero
      apply hnonempty
      exact List.eq_nil_of_length_eq_zero hzero)
  have hcircuitEmpty : circuit.isEmpty = false := by
    simpa using hnonempty
  have happendedNonempty :
      (circuit ++
          [RawGate.copy (input.length + circuit.length - 1) negated]).isEmpty =
        false := by
    simp
  unfold eval?
  rw [hcircuitEmpty, happendedNonempty]
  simp only [Bool.false_eq_true, ↓reduceIte, List.length_append,
    List.length_cons, List.length_nil]
  rw [evalAux?_append_internal]
  cases hresult : evalAux? circuit input.toArray with
  | none => simp
  | some result =>
      have hsize := evalAux?_size hresult
      have hindex : input.length + circuit.length - 1 < result.size := by
        rw [hsize]
        simp
        omega
      simp only [Option.bind_some]
      unfold RawGate.copy
      simp only [evalAux?]
      have hget :
          result[input.length + circuit.length - 1]? =
            some result[input.length + circuit.length - 1] := by
        simp [hindex]
      rw [hget]
      simp
      have houtputIndex : input.length + circuit.length = result.size := by
        rw [hsize]
        simp
      rw [Array.getElem?_push]
      rw [ite_eq_left houtputIndex, hget]
      simp [RawGate.eval]

/-- Exact serialization of an output-match extension. -/
theorem encode_appendOutputMatch_internal (inputWidth : ℕ)
    (circuit : RawCircuit) (expected : Bool) :
    (appendOutputMatch inputWidth circuit expected).encode =
      NatCode.encode (circuit.length + 1) ++
        circuit.flatMap RawGate.encode ++
          (RawGate.copy
            (inputWidth + circuit.length - 1) (!expected)).encode := by
  simp [appendOutputMatch, encode]

/-- An output-match extension returns true exactly when the original
nonempty circuit returns the selected bit. -/
theorem eval?_appendOutputMatch_eq_some_true_iff_internal
    (circuit : RawCircuit) (input : List Bool) (expected : Bool)
    (hnonempty : circuit ≠ []) :
    (appendOutputMatch input.length circuit expected).eval? input = some true ↔
      circuit.eval? input = some expected := by
  rw [appendOutputMatch,
    eval?_append_copy_internal circuit input (!expected) hnonempty]
  cases heval : circuit.eval? input with
  | none => simp
  | some value => cases expected <;> cases value <;> simp

/-- Exact decoding turns an output-match extension into a true-evaluation
test at the declared input width. -/
theorem evalCode_appendOutputMatch_encode_iff_of_length_internal
    (inputWidth : ℕ) (circuit : RawCircuit) (input : List Bool)
    (expected : Bool) (hnonempty : circuit ≠ [])
    (hwidth : input.length = inputWidth) :
    evalCode inputWidth
          (appendOutputMatch inputWidth circuit expected).encode input =
        some true ↔
      circuit.eval? input = some expected := by
  unfold evalCode
  rw [ite_eq_left hwidth, decode?_encode]
  rw [appendOutputMatch]
  have happly := eval?_append_copy_internal circuit input (!expected) hnonempty
  rw [hwidth] at happly
  change
    (circuit ++
        [RawGate.copy (inputWidth + circuit.length - 1) (!expected)]).eval?
          input = some true ↔
      circuit.eval? input = some expected
  rw [happly]
  cases heval : circuit.eval? input with
  | none => simp
  | some value => cases expected <;> cases value <;> simp

/-- Exact serialization of a two-gate live-bit output-match extension. -/
theorem encode_appendOutputMatchBit_internal (inputWidth : ℕ)
    (circuit : RawCircuit) (expected : Bool) :
    (appendOutputMatchBit inputWidth circuit expected).encode =
      NatCode.encode (circuit.length + 2) ++
        circuit.flatMap RawGate.encode ++
          (RawGate.copy
            (inputWidth + circuit.length - 1) expected).encode ++
            (RawGate.copy (inputWidth + circuit.length) true).encode := by
  simp [appendOutputMatchBit, encode, List.append_assoc]

/-- The two-gate live-bit output-match extension returns true exactly when
the original nonempty circuit returns the selected bit. -/
theorem eval?_appendOutputMatchBit_eq_some_true_iff_internal
    (circuit : RawCircuit) (input : List Bool) (expected : Bool)
    (hnonempty : circuit ≠ []) :
    (appendOutputMatchBit input.length circuit expected).eval? input =
        some true ↔
      circuit.eval? input = some expected := by
  let mismatch :=
    RawGate.copy (input.length + circuit.length - 1) expected
  let first := circuit ++ [mismatch]
  have hfirstNonempty : first ≠ [] := by simp [first]
  have hfirst :=
    eval?_append_copy_internal circuit input expected hnonempty
  have hsecond := eval?_append_copy_internal first input true hfirstNonempty
  have hshape :
      appendOutputMatchBit input.length circuit expected =
        first ++ [RawGate.copy (input.length + first.length - 1) true] := by
    simp [appendOutputMatchBit, first, mismatch]
  rw [hshape, hsecond]
  have hfirstShape :
      first = circuit ++
        [RawGate.copy (input.length + circuit.length - 1) expected] := rfl
  rw [hfirstShape, hfirst]
  cases heval : circuit.eval? input with
  | none => simp
  | some value => cases expected <;> cases value <;> simp

/-- Exact decoding turns a two-gate live-bit output-match extension into a
true-evaluation test at the declared input width. -/
theorem evalCode_appendOutputMatchBit_encode_iff_of_length_internal
    (inputWidth : ℕ) (circuit : RawCircuit) (input : List Bool)
    (expected : Bool) (hnonempty : circuit ≠ [])
    (hwidth : input.length = inputWidth) :
    evalCode inputWidth
          (appendOutputMatchBit inputWidth circuit expected).encode input =
        some true ↔
      circuit.eval? input = some expected := by
  unfold evalCode
  rw [ite_eq_left hwidth, decode?_encode]
  change
    (appendOutputMatchBit inputWidth circuit expected).eval? input = some true ↔
      circuit.eval? input = some expected
  rw [← hwidth]
  exact eval?_appendOutputMatchBit_eq_some_true_iff_internal
    circuit input expected hnonempty

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
              rw [Array.getElem?_push, ite_eq_right (by omega)] at hpreserved
              exact hpreserved

end RawCircuit

end CircuitCode

end Complexity
