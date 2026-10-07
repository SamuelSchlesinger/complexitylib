/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.RationalHitting.PolynomialTime.Defs
public import Complexitylib.Interop.Mathlib.TM0.Guard

/-!
# Canonical polynomial time for the rational hitting-list generator

The source machine is bundled with its binary alphabet codec, guarded by the
five-state unary validator, and translated through the reusable TM0 bridge.
-/

public section

namespace Complexity.RationalHitting.Internal

/-- The shape of every prefix that has not reached the dead state. -/
def InputShape : InputState → List Bool → Prop
  | .start, w => w = []
  | .left, w => ∃ n, w = List.replicate (n + 1) true
  | .separator, w => ∃ n, w = List.replicate (n + 1) true ++ [false]
  | .right, w => ∃ n s, w = binaryInput (n + 1) (s + 1)
  | .dead, _ => True

/-- Each validator step preserves its prefix interpretation. -/
theorem inputShape_step (q : InputState) (b : Bool) (w : List Bool)
    (h : InputShape q w) : InputShape (inputDFA.step q b) (w ++ [b]) := by
  cases q <;> cases b <;> simp only [inputDFA, InputShape] at h ⊢
  · subst w
    exact ⟨0, rfl⟩
  · obtain ⟨n, rfl⟩ := h
    exact ⟨n, rfl⟩
  · obtain ⟨n, rfl⟩ := h
    exact ⟨n + 1, List.replicate_succ'.symm⟩
  · obtain ⟨n, rfl⟩ := h
    exact ⟨n, 0, by simp [binaryInput, List.append_assoc]⟩
  · obtain ⟨n, s, rfl⟩ := h
    exact ⟨n, s + 1, by simp [binaryInput, List.replicate_succ', List.append_assoc]⟩

/-- The validator state records the shape of the complete input. -/
theorem inputShape (w : List Bool) : InputShape (inputDFA.eval w) w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b ih =>
      simpa only [DFA.eval_append_singleton] using
        inputShape_step (inputDFA.eval w) b w ih

/-- Every accepted word has exactly the required two positive unary blocks. -/
theorem input_shape {w : List Bool} (hw : w ∈ inputDFA.accepts) :
    ∃ n s, w = binaryInput (n + 1) (s + 1) := by
  have hq : inputDFA.eval w = .right := hw
  simpa only [hq, InputShape] using inputShape w

/-- True bits stay within the corresponding unary block. -/
theorem eval_replicate (q : InputState) (hq : inputDFA.step q true = q) (n : ℕ) :
    inputDFA.evalFrom q (List.replicate n true) = q := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, DFA.evalFrom_cons, hq] using ih

/-- Both positive unary parameters pass the validator. -/
theorem binaryInput_mem (n s : ℕ) : binaryInput (n + 1) (s + 1) ∈ inputDFA.accepts := by
  change inputDFA.evalFrom .start (binaryInput (n + 1) (s + 1)) = .right
  rw [binaryInput, List.replicate_succ, List.cons_append, DFA.evalFrom_cons]
  change inputDFA.evalFrom .left
    (List.replicate n true ++ false :: List.replicate (s + 1) true) = .right
  rw [DFA.evalFrom_of_append, eval_replicate .left rfl n, DFA.evalFrom_cons]
  change inputDFA.evalFrom .separator (List.replicate (s + 1) true) = .right
  rw [List.replicate_succ, DFA.evalFrom_cons]
  exact eval_replicate .right rfl s

/-- Reading the first block recovers its unary parameter. -/
theorem inputVariables_binaryInput (n s : ℕ) : inputVariables (binaryInput n s) = n := by
  simp [inputVariables, binaryInput, List.takeWhile]

/-- Reading the second block recovers its unary parameter. -/
theorem inputSize_binaryInput (n s : ℕ) : inputSize (binaryInput n s) = s := by
  rw [inputSize, inputVariables_binaryInput]
  simp [binaryInput]

/-- Literal unary input length is the sum of its parameters and one separator. -/
theorem binaryInput_length (n s : ℕ) : (binaryInput n s).length = n + s + 1 := by
  simp [binaryInput, Nat.add_assoc]

/-- The binary input maps to the source's literal unary tape word. -/
theorem map_binaryInput (n s : ℕ) : (binaryInput n s).map tapeBit = unaryInput n s := by
  simp [binaryInput, unaryInput, tapeBit]

/-- Bundle a source machine with its faithful binary alphabet codec. -/
abbrev binaryMachine {m : ℕ} (G : Machine m) : MathlibTM0.BinaryMachine where
  Alphabet := Alphabet
  State := Fin (m + 1)
  bit := tapeBit
  readBit a := if a = 1 then some false else if a = 2 then some true else none
  readBit_bit b := by cases b <;> decide
  readBit_blank := by decide
  code := G

/-- Bundling changes neither source configurations nor finite runs. -/
theorem binaryMachine_run {m : ℕ} (G : Machine m) (t : ℕ) (c : Config m) :
    (binaryMachine G).run t c = run G t c := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
      change (Turing.TM0.step G c).bind ((binaryMachine G).run t) =
        (Turing.TM0.step G c).bind (run G t)
      simp only [ih]

/-- The source's complete-output theorem is exactly the bundled contract. -/
theorem binaryMachine_outputs {m n s time : ℕ} {G : Machine m} {H : Output n}
    (h : OutputsWithin G s time H) :
    (binaryMachine G).OutputsWithin (binaryInput n s) (encodeOutput H) time := by
  obtain ⟨t, ht, c, hc, hh, ho⟩ := h
  refine ⟨t, ht, c, ?_, hh, ho⟩
  simpa only [binaryMachine_run, map_binaryInput] using hc

/-- Literal positive unary inputs yield the source's exact encoded hitting list. -/
theorem hittingGenerator_binaryInput (n s : ℕ) :
    hittingGenerator (binaryInput (n + 1) (s + 1)) =
      encodeOutput (hittingList (n + 1) (s + 1)) := by
  rw [hittingGenerator, ite_eq_left (binaryInput_mem n s),
    inputVariables_binaryInput, inputSize_binaryInput]

/-- The total source-compatible generator belongs to canonical polynomial time. -/
theorem hittingGenerator_mem_FP : hittingGenerator ∈ FP := by
  obtain ⟨m, G, C, k, _, _, hG⟩ := exists_uniform_generator
  apply MathlibTM0.BinaryMachine.mem_FP_on_dfa (M := binaryMachine G) inputDFA
    (p := Polynomial.C C * Polynomial.X ^ k)
    (q := Polynomial.C PolynomialBounds.outputConstant * Polynomial.X ^ 104)
  · intro w hw
    obtain ⟨n, s, rfl⟩ := input_shape hw
    rw [inputVariables_binaryInput, inputSize_binaryInput]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      binaryInput_length]
    exact binaryMachine_outputs (hG (n + 1) (s + 1) (by lia) (by lia))
  · intro w hw
    obtain ⟨n, s, rfl⟩ := input_shape hw
    rw [inputVariables_binaryInput, inputSize_binaryInput]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      binaryInput_length]
    exact hittingList_encoding_length_le (n + 1) (s + 1) (by lia)

end Complexity.RationalHitting.Internal
