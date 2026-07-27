/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BitString
public import Complexitylib.Circuits.Encoding.Internal.Codec
public import Complexitylib.Circuits.Internal.CircuitToDescriptor
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Internal: semantics of encoded fan-in-two circuits

This file proves that the iterative, machine-facing evaluator in
`Circuits.Encoding.Defs` implements the existing mathematical circuit
semantics.  The central argument is a memo invariant: after the first `k`
ordered gates have run, the evaluator's array contains exactly the values of
descriptor wires `0, ..., N + k - 1`.
-/

@[expose] public section

namespace Complexity

open CircDesc

namespace CircuitCode

namespace RawGate

/-- Remove the dependent bounds from a descriptor gate while retaining its
    operation, references, and negation flags. -/
private def ofSlot {W : ℕ} (slot : GateSlot W) : RawGate :=
  { op := if slot.1 then .and else .or
    input₀ := slot.2.1.1.val
    input₁ := slot.2.1.2.val
    negated₀ := slot.2.2.1
    negated₁ := slot.2.2.2 }

private theorem eval_ofSlot {W : ℕ} (slot : GateSlot W) (value₀ value₁ : Bool) :
    (ofSlot slot).eval value₀ value₁ =
      if slot.1 then
        slot.2.2.1.xor value₀ && slot.2.2.2.xor value₁
      else
        slot.2.2.1.xor value₀ || slot.2.2.2.xor value₁ := by
  rcases slot with ⟨isAnd, ⟨input₀, input₁⟩, ⟨negated₀, negated₁⟩⟩
  cases isAnd <;> rfl

end RawGate

namespace RawCircuit

/-- Erase the dependent bounds from every gate of a descriptor, preserving
    its topological order. -/
private def ofDesc {N s : ℕ} (d : CircDesc N s) : RawCircuit :=
  List.ofFn fun i => RawGate.ofSlot (d i)

@[simp] private theorem length_ofDesc {N s : ℕ} (d : CircDesc N s) :
    (ofDesc d).length = s := by
  simp [ofDesc]

end RawCircuit

namespace RawCircuit

private def memoArray {N s : ℕ} (d : CircDesc N s) (input : BitString N)
    (k : ℕ) (hk : k ≤ s) : Array Bool :=
  Array.ofFn fun w : Fin (N + k) =>
    wireVal d input (Fin.castLE (Nat.add_le_add_left hk N) w)

private theorem memoArray_get {N s : ℕ} (d : CircDesc N s) (input : BitString N)
    {k : ℕ} (hk : k ≤ s) (w : Fin (N + s)) (hw : w.val < N + k) :
    (memoArray d input k hk)[w.val]? = some (wireVal d input w) := by
  simp only [memoArray, Array.size_ofFn, hw, getElem?_pos, Array.getElem_ofFn]
  congr 2

private theorem memoArray_zero {N s : ℕ} (d : CircDesc N s) (input : BitString N) :
    memoArray d input 0 (Nat.zero_le s) = (List.ofFn input).toArray := by
  apply Array.ext
  · simp [memoArray]
  · intro i hi₁ hi₂
    have hi : i < N := by simpa [memoArray] using hi₁
    simp only [memoArray, Array.getElem_ofFn, List.getElem_toArray, List.getElem_ofFn]
    rw [wireVal]
    simp [hi]

private theorem memoArray_succ {N s : ℕ} (d : CircDesc N s) (input : BitString N)
    {k : ℕ} (hk : k < s) :
    memoArray d input (k + 1) (by omega) =
      (memoArray d input k (by omega)).push
        (wireVal d input ⟨N + k, by omega⟩) := by
  unfold memoArray
  rw [Array.ofFn_succ]
  congr 1

private theorem eval_ofSlot_eq_wireVal {N s : ℕ} (d : CircDesc N s)
    (input : BitString N) {k : ℕ} (hk : k < s) (hordered : CircDesc.Ordered d) :
    let slot := d ⟨k, hk⟩
    (RawGate.ofSlot slot).eval
        (wireVal d input slot.2.1.1)
        (wireVal d input slot.2.1.2) =
      wireVal d input ⟨N + k, by omega⟩ := by
  dsimp only
  have hrefs := hordered ⟨k, hk⟩
  conv_rhs => rw [wireVal]
  simp only [show ¬(N + k < N) by omega, dite_false, Nat.add_sub_cancel_left]
  simp only [show (⟨k, by omega⟩ : Fin s) = ⟨k, hk⟩ by rfl]
  rw [RawGate.eval_ofSlot]
  simp only [hrefs.1, hrefs.2, ite_true]

private theorem evalAux?_singleton_ofSlot {N s : ℕ} (d : CircDesc N s)
    (input : BitString N) {k : ℕ} (hk : k < s) (hordered : CircDesc.Ordered d) :
    evalAux? [RawGate.ofSlot (d ⟨k, hk⟩)]
        (memoArray d input k (by omega)) =
      some (memoArray d input (k + 1) (by omega)) := by
  have hrefs := hordered ⟨k, hk⟩
  rw [memoArray_succ d input hk]
  simp only [evalAux?]
  change
    (do
      let value₀ ← (memoArray d input k (by omega))[(d ⟨k, hk⟩).2.1.1.val]?
      let value₁ ← (memoArray d input k (by omega))[(d ⟨k, hk⟩).2.1.2.val]?
      some ((memoArray d input k (by omega)).push
        ((RawGate.ofSlot (d ⟨k, hk⟩)).eval value₀ value₁))) = _
  rw [memoArray_get d input (by omega) (d ⟨k, hk⟩).2.1.1 hrefs.1]
  rw [memoArray_get d input (by omega) (d ⟨k, hk⟩).2.1.2 hrefs.2]
  change
    some ((memoArray d input k (by omega)).push
      ((RawGate.ofSlot (d ⟨k, hk⟩)).eval
        (wireVal d input (d ⟨k, hk⟩).2.1.1)
        (wireVal d input (d ⟨k, hk⟩).2.1.2))) = _
  rw [eval_ofSlot_eq_wireVal d input hk hordered]

private theorem evalAux?_append (first second : RawCircuit) (wires : Array Bool) :
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

private theorem evalAux?_ofDesc_prefix {N s : ℕ} (d : CircDesc N s)
    (input : BitString N) (hordered : CircDesc.Ordered d)
    (k : ℕ) (hk : k ≤ s) :
    evalAux?
        (List.ofFn fun i : Fin k => RawGate.ofSlot (d (Fin.castLE hk i)))
        (List.ofFn input).toArray =
      some (memoArray d input k hk) := by
  induction k with
  | zero =>
      simp only [List.ofFn_zero, evalAux?]
      rw [memoArray_zero]
  | succ k ih =>
      have hk' : k ≤ s := by omega
      rw [List.ofFn_succ_last, evalAux?_append]
      have hprefix :
          (List.ofFn fun i : Fin k =>
              RawGate.ofSlot (d (Fin.castLE hk (Fin.castSucc i)))) =
            List.ofFn fun i : Fin k => RawGate.ofSlot (d (Fin.castLE hk' i)) := by
        apply List.ofFn_inj.mpr
        funext i
        congr 2
      rw [hprefix, ih hk']
      simp only [Option.bind_some]
      have hlast :
          RawGate.ofSlot (d (Fin.castLE hk (Fin.last k))) =
            RawGate.ofSlot (d ⟨k, by omega⟩) := by
        congr 2
      rw [hlast]
      exact evalAux?_singleton_ofSlot d input (by omega) hordered

/-- Iterative evaluation of an ordered descriptor agrees with its recursive
    mathematical semantics. -/
private theorem eval?_ofDesc {N s : ℕ} (d : CircDesc N s) (hs : 0 < s)
    (hordered : CircDesc.Ordered d) (input : BitString N) :
    (ofDesc d).eval? (List.ofFn input) = some (eval hs d input) := by
  have heval := evalAux?_ofDesc_prefix d input hordered s (Nat.le_refl s)
  have hdesc :
      (List.ofFn fun i : Fin s => RawGate.ofSlot (d (Fin.castLE (Nat.le_refl s) i))) =
        ofDesc d := by
    apply List.ofFn_inj.mpr
    funext i
    congr 2
  rw [hdesc] at heval
  simp only [eval?, length_ofDesc, List.length_ofFn]
  have hne : ofDesc d ≠ [] := by
    intro h
    have := congrArg List.length h
    simp_all
  rw [show (ofDesc d).isEmpty = false by simpa using hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [heval]
  simp only [eval]
  exact memoArray_get d input (Nat.le_refl s) ⟨N + s - 1, by omega⟩ (by omega)

private theorem ofSlot_encodeGate {W W' : ℕ} (gate : Gate Basis.andOr2 W)
    (hW : W ≤ W') :
    RawGate.ofSlot (encodeGate gate hW) = RawGate.ofGate gate := by
  obtain ⟨op, fanIn, arityOk, inputs, negated⟩ := gate
  change fanIn = 2 at arityOk
  subst fanIn
  cases op <;> rfl

private theorem ofDesc_circuitToDesc {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) :
    ofDesc (circuitToDesc c) = ofCircuit c := by
  unfold ofDesc ofCircuit
  rw [List.ofFn_succ_last]
  congr 1
  · apply List.ofFn_inj.mpr
    funext i
    have hi : (i.castSucc : Fin (G + 1)).val < G := i.isLt
    simpa [circuitToDesc, hi] using
      ofSlot_encodeGate (c.gates i) (by omega : N + G ≤ N + (G + 1))
  · simpa [circuitToDesc] using
      ofSlot_encodeGate (c.outputs 0) (by omega : N + G ≤ N + (G + 1))

/-- Raw evaluation of a serialized typed circuit agrees with the typed
    circuit's Boolean semantics. -/
theorem eval?_ofCircuit {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (input : BitString N) :
    (ofCircuit c).eval? input.toList = some ((c.eval input) 0) := by
  rw [← ofDesc_circuitToDesc c]
  rw [show input.toList = List.ofFn input by rfl]
  rw [eval?_ofDesc (circuitToDesc c) (Nat.succ_pos G) (circuitToDesc_ordered c)]
  have hsemantics := congrFun (circuit_eval_eq_eval c) input
  exact congrArg some hsemantics.symm

end RawCircuit

/-- Decoding and iteratively evaluating the canonical encoding of a typed
    fan-in-two circuit returns its typed output. -/
theorem evalCode_encodeCircuit_internal {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (input : BitString N) :
    evalCode N (encodeCircuit c) input.toList = some ((c.eval input) 0) := by
  simp only [evalCode, BitString.length_toList, ↓reduceIte, encodeCircuit,
    RawCircuit.decode?_encode]
  exact RawCircuit.eval?_ofCircuit c input

/-- List-native form of `evalCode_encodeCircuit` for machine-facing clients. -/
theorem evalCode_encodeCircuit_of_length_internal {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (input : List Bool)
    (hinput : input.length = N) :
    evalCode N (encodeCircuit c) input =
      some ((c.eval (BitString.ofList input hinput)) 0) := by
  simpa using evalCode_encodeCircuit_internal c (BitString.ofList input hinput)

end CircuitCode

end Complexity
