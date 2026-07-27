/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.Core.Defs

/-!
# Pure semantics for the streaming circuit evaluator

The machine controller parses and evaluates one gate before moving to the next.
The public codec first decodes the complete gate list and then evaluates it.
This file supplies a verdict-level streaming evaluator and proves that the two
orders produce the same result. A controller-ordered one-gate step additionally
exposes the ref0-before-ref1 dependency order needed by execution proofs while
retaining `evalFamilyCode` as their external specification; it is not a
transition-level trace model.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- Parse and evaluate exactly `count` gates. The memo list begins with the
primary inputs and grows by one value per gate; `last` is the most recently
appended gate value. Successful termination also requires exact code
consumption. -/
def gateStream? : ℕ → List Bool → List Bool → Option Bool → Option Bool
  | 0, code, _, last => if code = [] then last else none
  | count + 1, code, wires, _ => do
      let (gate, rest) ← RawGate.decodePrefix? code
      let value₀ ← wires[gate.input₀]?
      let value₁ ← wires[gate.input₁]?
      let value := gate.eval value₀ value₁
      gateStream? count rest (wires ++ [value]) (some value)

/-- The semantic result of one controller-ordered gate evaluation. -/
structure GateStepResult where
  /-- The unconsumed circuit code after both references. -/
  rest : List Bool
  /-- The wire memo after appending the new gate value. -/
  wires : List Bool
  /-- The newly computed gate value. -/
  value : Bool

/-- Parse and evaluate one gate in the controller's reference dependency
order: parse the first reference, read its wire, parse the second reference,
and read its wire. -/
def gateStep? (code wires : List Bool) : Option GateStepResult :=
  match code with
  | op :: negated₀ :: negated₁ :: rest => do
      let (input₀, rest₀) ← NatCode.decodePrefix? rest
      let value₀ ← wires[input₀]?
      let (input₁, rest₁) ← NatCode.decodePrefix? rest₀
      let value₁ ← wires[input₁]?
      let value := evalOpBit op (negated₀.xor value₀) (negated₁.xor value₁)
      some { rest := rest₁, wires := wires ++ [value], value }
  | _ => none

/-- Decoding an operation bit and evaluating the resulting raw gate agrees
with the controller's Boolean operation. -/
theorem rawGate_eval_opOfBit (op negated₀ negated₁ value₀ value₁ : Bool)
    (input₀ input₁ : ℕ) :
    ({ op := RawGate.opOfBit op, input₀, input₁, negated₀, negated₁ } :
        RawGate).eval value₀ value₁ =
      evalOpBit op (negated₀.xor value₀) (negated₁.xor value₁) := by
  cases op <;> rfl

/-- A positive gate-stream step is exactly one controller-ordered gate step
followed by the remaining stream. -/
theorem gateStream?_succ_eq_gateStep? (count : ℕ) (code wires : List Bool)
    (last : Option Bool) :
    gateStream? (count + 1) code wires last =
      (gateStep? code wires).bind fun step =>
        gateStream? count step.rest step.wires (some step.value) := by
  cases code with
  | nil => rfl
  | cons op code =>
      cases code with
      | nil => rfl
      | cons negated₀ code =>
          cases code with
          | nil => rfl
          | cons negated₁ rest =>
              cases h₀ : NatCode.decodePrefix? rest with
              | none =>
                  simp [gateStream?, gateStep?, RawGate.decodePrefix?, h₀]
              | some parsed₀ =>
                  obtain ⟨input₀, rest₀⟩ := parsed₀
                  cases h₁ : NatCode.decodePrefix? rest₀ with
                  | none =>
                      cases hw₀ : wires[input₀]? <;>
                        simp [gateStream?, gateStep?, RawGate.decodePrefix?, h₀, h₁,
                          hw₀]
                  | some parsed₁ =>
                      obtain ⟨input₁, rest₁⟩ := parsed₁
                      cases hw₀ : wires[input₀]? with
                      | none =>
                          simp [gateStream?, gateStep?, RawGate.decodePrefix?, h₀, h₁,
                            hw₀]
                      | some value₀ =>
                          cases hw₁ : wires[input₁]? with
                          | none =>
                              simp [gateStream?, gateStep?, RawGate.decodePrefix?, h₀, h₁,
                                hw₀, hw₁]
                          | some value₁ =>
                              simp [gateStream?, gateStep?, RawGate.decodePrefix?, h₀, h₁,
                                hw₀, hw₁, rawGate_eval_opOfBit]

/-- Parse a circuit's unary gate count and evaluate its gate stream. -/
def positiveStream? (code input : List Bool) : Option Bool := do
  let (count, rest) ← NatCode.decodePrefix? code
  gateStream? count rest input none

/-- Evaluate an already-decoded gate list with the same list-shaped memo and
last-value accumulator used by `gateStream?`. -/
private def evalGateLast? : RawCircuit → List Bool → Option Bool → Option Bool
  | [], _, last => last
  | gate :: gates, wires, _ => do
      let value₀ ← wires[gate.input₀]?
      let value₁ ← wires[gate.input₁]?
      let value := gate.eval value₀ value₁
      evalGateLast? gates (wires ++ [value]) (some value)

private theorem gateStream?_encoded (circuit : RawCircuit) (wires : List Bool)
    (last : Option Bool) :
    gateStream? circuit.length (circuit.flatMap RawGate.encode) wires last =
      evalGateLast? circuit wires last := by
  induction circuit generalizing wires last with
  | nil => simp [gateStream?, evalGateLast?]
  | cons gate gates ih =>
      simp [gateStream?, evalGateLast?, ih]

private theorem evalGateLast?_cons_eq_evalAux? (gate : RawGate)
    (gates : RawCircuit) (wires : List Bool) (last : Option Bool) :
    evalGateLast? (gate :: gates) wires last =
      (RawCircuit.evalAux? (gate :: gates) wires.toArray).bind fun result =>
        result[wires.length + (gate :: gates).length - 1]? := by
  induction gates generalizing gate wires last with
  | nil =>
      rw [evalGateLast?, RawCircuit.evalAux?]
      simp only [List.getElem?_toArray]
      cases h₀ : wires[gate.input₀]? with
      | none => rfl
      | some value₀ =>
          cases h₁ : wires[gate.input₁]? with
          | none => rfl
          | some value₁ => simp [evalGateLast?, RawCircuit.evalAux?]
  | cons next rest ih =>
      rw [evalGateLast?, RawCircuit.evalAux?]
      simp only [List.getElem?_toArray]
      cases h₀ : wires[gate.input₀]? with
      | none => rfl
      | some value₀ =>
          cases h₁ : wires[gate.input₁]? with
          | none => rfl
          | some value₁ =>
              change
                evalGateLast? (next :: rest)
                    (wires ++ [gate.eval value₀ value₁])
                    (some (gate.eval value₀ value₁)) =
                  (RawCircuit.evalAux? (next :: rest)
                    (wires.toArray.push (gate.eval value₀ value₁))).bind
                    fun result =>
                      result[wires.length + (gate :: next :: rest).length - 1]?
              have harray :
                  wires.toArray.push (gate.eval value₀ value₁) =
                    (wires ++ [gate.eval value₀ value₁]).toArray := by
                simp
              rw [harray, ih]
              congr 1
              funext result
              congr 1
              simp only [List.length_append, List.length_cons,
                List.length_nil]
              omega

private theorem evalGateLast?_eq_eval? (circuit : RawCircuit)
    (input : List Bool) :
    evalGateLast? circuit input none = circuit.eval? input := by
  cases circuit with
  | nil => simp [evalGateLast?, RawCircuit.eval?]
  | cons gate gates =>
      rw [evalGateLast?_cons_eq_evalAux?]
      simp [RawCircuit.eval?]

private theorem positiveStream?_encode (circuit : RawCircuit)
    (input : List Bool) :
    positiveStream? circuit.encode input = circuit.eval? input := by
  simp [positiveStream?, RawCircuit.encode, gateStream?_encoded,
    evalGateLast?_eq_eval?]

private theorem gateStream?_isSome_decodeGates?_eq_some (count : ℕ)
    (code wires : List Bool) (last : Option Bool)
    (h : (gateStream? count code wires last).isSome) :
    ∃ circuit, RawCircuit.decodeGates? count code = some (circuit, []) := by
  induction count generalizing code wires last with
  | zero =>
      by_cases hcode : code = []
      · subst code
        exact ⟨[], rfl⟩
      · simp [gateStream?, hcode] at h
  | succ count ih =>
      cases hgate : RawGate.decodePrefix? code with
      | none => simp [gateStream?, hgate] at h
      | some parsed =>
          obtain ⟨gate, rest⟩ := parsed
          cases h₀ : wires[gate.input₀]? with
          | none => simp [gateStream?, hgate, h₀] at h
          | some value₀ =>
              cases h₁ : wires[gate.input₁]? with
              | none => simp [gateStream?, hgate, h₀, h₁] at h
              | some value₁ =>
                  obtain ⟨gates, hgates⟩ := ih rest
                    (wires ++ [gate.eval value₀ value₁])
                    (some (gate.eval value₀ value₁)) (by
                      simpa [gateStream?, hgate, h₀, h₁] using h)
                  exact ⟨gate :: gates, by
                    simp [RawCircuit.decodeGates?, hgate, hgates]⟩

private theorem positiveStream?_isSome_decode?_isSome (code input : List Bool)
    (h : (positiveStream? code input).isSome) :
    (RawCircuit.decode? code).isSome := by
  cases hcount : NatCode.decodePrefix? code with
  | none => simp [positiveStream?, hcount] at h
  | some parsed =>
      obtain ⟨count, rest⟩ := parsed
      have hstream : (gateStream? count rest input none).isSome := by
        simpa [positiveStream?, hcount] using h
      obtain ⟨circuit, hgates⟩ :=
        gateStream?_isSome_decodeGates?_eq_some count rest input none hstream
      have hprefix : RawCircuit.decodePrefix? code = some (circuit, []) := by
        simp [RawCircuit.decodePrefix?, hcount, hgates]
      simp [RawCircuit.decode?, hprefix]

/-- The streaming specification agrees with the library's public exact codec
and memoized evaluator. -/
theorem positiveStream?_eq_evalCode (code input : List Bool) :
    positiveStream? code input = evalCode input.length code input := by
  cases hdecode : RawCircuit.decode? code with
  | none =>
      cases hstream : positiveStream? code input with
      | none => simp [evalCode, hdecode]
      | some answer =>
          have hsome : (positiveStream? code input).isSome := by
            simp [hstream]
          have hdecoded := positiveStream?_isSome_decode?_isSome code input hsome
          simp [hdecode] at hdecoded
  | some circuit =>
      have hcode := (RawCircuit.decode?_eq_some_iff code circuit).mp hdecode
      subst code
      simpa [evalCode] using positiveStream?_encode circuit input

/-- Pure semantics of the complete tagged-family stream consumed by the
machine core. -/
def familyStream? (code input : List Bool) : Option Bool :=
  if input.isEmpty then
    match code with
    | [false, answer] => some answer
    | _ => none
  else
    match code with
    | true :: circuitCode => positiveStream? circuitCode input
    | _ => none

/-- The controller-shaped pure stream retains `evalFamilyCode` as its exact
external specification. -/
theorem familyStream?_eq_evalFamilyCode (code input : List Bool) :
    familyStream? code input = evalFamilyCode code input := by
  unfold familyStream? evalFamilyCode
  split
  · rfl
  · cases code with
    | nil => rfl
    | cons tag circuitCode =>
        cases tag with
        | false => rfl
        | true => exact positiveStream?_eq_evalCode circuitCode input

end Internal

end Machine

end CircuitCode

end Complexity
