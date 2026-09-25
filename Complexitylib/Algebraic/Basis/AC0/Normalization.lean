/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.AC0
public import Complexitylib.Algebraic.Parallel
public import Complexitylib.Algebraic.Translation.Block

/-!
# Dual-rail normalization for AC0 circuits

This module implements the local compiler underlying input-negation normal
form. Every Boolean value is represented by two wires carrying the value and
its complement. A source NOT swaps the two rails without adding a gate. A
source AND or OR produces both its ordinary output and its De Morgan dual,
using exactly two target gates.

The construction is semantic rather than syntactic: the same block
translation simulates both Boolean evaluation and the logical-depth
interpretation. Thus compilation preserves logical depth exactly and doubles
the charged AND/OR cost, including at fan-in zero.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace DualRail

/-- Encode a Boolean together with its complement. -/
def encode (value : Bool) : Fin 2 -> Bool :=
  ![value, !value]

/-- Duplicate a logical depth across both rails. -/
def duplicateDepth (depth : Nat) : Fin 2 -> Nat :=
  ![depth, depth]

/-- A NOT gate swaps the two rails without adding a gate. -/
def notCircuit : Circuit signature (1 * 2) 0 2 where
  program := .empty
  outputs := ![Block.inputWire (0 : Fin 1) (1 : Fin 2),
    Block.inputWire (0 : Fin 1) (0 : Fin 2)]

/-- The positive AND output of a dual-rail AND gadget. -/
def andPositiveLine (inputCount : Nat) :
    Line signature (inputCount * 2) 0 :=
  { op := .and inputCount
    wires := fun input => Block.inputWire input (0 : Fin 2) }

/-- The complemented output of a dual-rail AND gadget, computed by OR. -/
def andNegativeLine (inputCount : Nat) :
    Line signature (inputCount * 2) 1 :=
  { op := .or inputCount
    wires := fun input => Block.inputWire input (1 : Fin 2) }

@[simp] theorem andPositiveLine_eval
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U)
    (gates : Fin 0 -> U) :
    (andPositiveLine inputCount).eval target input gates =
      target (.and inputCount)
        (fun argument => input (finProdFinEquiv (argument, 0))) := by
  unfold andPositiveLine Line.eval
  congr 1
  funext argument
  simp [Block.inputWire, Function.comp_apply]

@[simp] theorem andNegativeLine_eval
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U)
    (gates : Fin 1 -> U) :
    (andNegativeLine inputCount).eval target input gates =
      target (.or inputCount)
        (fun argument => input (finProdFinEquiv (argument, 1))) := by
  unfold andNegativeLine Line.eval
  congr 1
  funext argument
  simp [Block.inputWire, Function.comp_apply]

/-- The two-output gadget implementing AND and its complement. -/
def andCircuit (inputCount : Nat) :
    Circuit signature (inputCount * 2) 2 2 :=
  { program := (Program.empty.gate (andPositiveLine inputCount)).gate
      (andNegativeLine inputCount)
    outputs := ![Wire.gate (0 : Fin 2), Wire.gate (1 : Fin 2)] }

/-- The positive OR output of a dual-rail OR gadget. -/
def orPositiveLine (inputCount : Nat) :
    Line signature (inputCount * 2) 0 :=
  { op := .or inputCount
    wires := fun input => Block.inputWire input (0 : Fin 2) }

/-- The complemented output of a dual-rail OR gadget, computed by AND. -/
def orNegativeLine (inputCount : Nat) :
    Line signature (inputCount * 2) 1 :=
  { op := .and inputCount
    wires := fun input => Block.inputWire input (1 : Fin 2) }

@[simp] theorem orPositiveLine_eval
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U)
    (gates : Fin 0 -> U) :
    (orPositiveLine inputCount).eval target input gates =
      target (.or inputCount)
        (fun argument => input (finProdFinEquiv (argument, 0))) := by
  unfold orPositiveLine Line.eval
  congr 1
  funext argument
  simp [Block.inputWire, Function.comp_apply]

@[simp] theorem orNegativeLine_eval
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U)
    (gates : Fin 1 -> U) :
    (orNegativeLine inputCount).eval target input gates =
      target (.and inputCount)
        (fun argument => input (finProdFinEquiv (argument, 1))) := by
  unfold orNegativeLine Line.eval
  congr 1
  funext argument
  simp [Block.inputWire, Function.comp_apply]

/-- The two-output gadget implementing OR and its complement. -/
def orCircuit (inputCount : Nat) :
    Circuit signature (inputCount * 2) 2 2 :=
  { program := (Program.empty.gate (orPositiveLine inputCount)).gate
      (orNegativeLine inputCount)
    outputs := ![Wire.gate (0 : Fin 2), Wire.gate (1 : Fin 2)] }

/-- Number of gates in a dual-rail operation gadget. -/
def gateCount : Op -> Nat
  | .not => 0
  | .and _ | .or _ => 2

/-- Dual-rail compilation of arbitrary AC0 gates. -/
def translation : BlockTranslation signature signature 2 where
  gateCount := gateCount
  operation
    | .not => notCircuit
    | .and inputCount => andCircuit inputCount
    | .or inputCount => orCircuit inputCount

@[simp] theorem notCircuit_eval_zero
    (target : Interpretation signature U)
    (input : Fin (1 * 2) -> U) :
    notCircuit.eval target input 0 = input 1 := by
  rfl

@[simp] theorem notCircuit_eval_one
    (target : Interpretation signature U)
    (input : Fin (1 * 2) -> U) :
    notCircuit.eval target input 1 = input 0 := by
  rfl

@[simp] theorem andCircuit_eval_zero
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U) :
    (andCircuit inputCount).eval target input 0 =
      target (.and inputCount)
        (fun argument => input (finProdFinEquiv (argument, 0))) := by
  unfold andCircuit Circuit.eval
  simp only [Function.comp_apply]
  change
    ((Program.empty.gate (andPositiveLine inputCount)).gate
      (andNegativeLine inputCount)).trace
        target input (Wire.gate (0 : Fin 2)) = _
  rw [show (Wire.gate (0 : Fin 2) : Wire (inputCount * 2) 2) =
      (Wire.gate (0 : Fin 1) : Wire (inputCount * 2) 1).castSucc by rfl]
  rw [Program.trace_gate_castSucc]
  rw [show (Wire.gate (0 : Fin 1) : Wire (inputCount * 2) 1) =
    Fin.last (inputCount * 2 + 0) by rfl]
  rw [Program.trace_gate_last, andPositiveLine_eval]

@[simp] theorem andCircuit_eval_one
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U) :
    (andCircuit inputCount).eval target input 1 =
      target (.or inputCount)
        (fun argument => input (finProdFinEquiv (argument, 1))) := by
  unfold andCircuit Circuit.eval
  simp only [Function.comp_apply]
  change
    ((Program.empty.gate (andPositiveLine inputCount)).gate
      (andNegativeLine inputCount)).trace
        target input (Wire.gate (1 : Fin 2)) = _
  rw [show (Wire.gate (1 : Fin 2) : Wire (inputCount * 2) 2) =
      Fin.last (inputCount * 2 + 1) by rfl]
  rw [Program.trace_gate_last]
  exact andNegativeLine_eval inputCount target input _

@[simp] theorem orCircuit_eval_zero
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U) :
    (orCircuit inputCount).eval target input 0 =
      target (.or inputCount)
        (fun argument => input (finProdFinEquiv (argument, 0))) := by
  unfold orCircuit Circuit.eval
  simp only [Function.comp_apply]
  change
    ((Program.empty.gate (orPositiveLine inputCount)).gate
      (orNegativeLine inputCount)).trace
        target input (Wire.gate (0 : Fin 2)) = _
  rw [show (Wire.gate (0 : Fin 2) : Wire (inputCount * 2) 2) =
      (Wire.gate (0 : Fin 1) : Wire (inputCount * 2) 1).castSucc by rfl]
  rw [Program.trace_gate_castSucc]
  rw [show (Wire.gate (0 : Fin 1) : Wire (inputCount * 2) 1) =
    Fin.last (inputCount * 2 + 0) by rfl]
  rw [Program.trace_gate_last, orPositiveLine_eval]

@[simp] theorem orCircuit_eval_one
    (inputCount : Nat)
    (target : Interpretation signature U)
    (input : Fin (inputCount * 2) -> U) :
    (orCircuit inputCount).eval target input 1 =
      target (.and inputCount)
        (fun argument => input (finProdFinEquiv (argument, 1))) := by
  unfold orCircuit Circuit.eval
  simp only [Function.comp_apply]
  change
    ((Program.empty.gate (orPositiveLine inputCount)).gate
      (orNegativeLine inputCount)).trace
        target input (Wire.gate (1 : Fin 2)) = _
  rw [show (Wire.gate (1 : Fin 2) : Wire (inputCount * 2) 2) =
      Fin.last (inputCount * 2 + 1) by rfl]
  rw [Program.trace_gate_last]
  exact orNegativeLine_eval inputCount target input _

@[simp] theorem encode_zero (value : Bool) :
    encode value 0 = value := by
  simp [encode]

@[simp] theorem encode_one (value : Bool) :
    encode value 1 = !value := by
  simp [encode]

private theorem interpretation_and_eq_false
    (input : Fin n -> Bool) :
    interpretation (.and n) input = false <->
      Exists fun k => input k = false := by
  rw [Bool.eq_false_iff]
  constructor
  · intro resultNotTrue
    have notAllTrue : ¬ forall k, input k = true :=
      fun allTrue => resultNotTrue ((interpretation_and_eq_true input).2 allTrue)
    rw [Classical.not_forall] at notAllTrue
    obtain ⟨argument, argumentNotTrue⟩ := notAllTrue
    exact ⟨argument, Bool.eq_false_iff.mpr argumentNotTrue⟩
  · rintro ⟨argument, argumentFalse⟩ resultTrue
    have argumentTrue := (interpretation_and_eq_true input).1 resultTrue argument
    simp [argumentFalse] at argumentTrue

private theorem interpretation_or_eq_false
    (input : Fin n -> Bool) :
    interpretation (.or n) input = false <->
      forall k, input k = false := by
  rw [Bool.eq_false_iff]
  constructor
  · intro resultNotTrue argument
    apply Bool.eq_false_iff.mpr
    intro argumentTrue
    apply resultNotTrue
    exact (interpretation_or_eq_true input).2 ⟨argument, argumentTrue⟩
  · intro allFalse resultTrue
    obtain ⟨argument, argumentTrue⟩ :=
      (interpretation_or_eq_true input).1 resultTrue
    have argumentFalse := allFalse argument
    simp [argumentFalse] at argumentTrue

@[simp] theorem duplicateDepth_apply (depth : Nat) (rail : Fin 2) :
    duplicateDepth depth rail = depth := by
  have railCases : rail = 0 ∨ rail = 1 := by omega
  rcases railCases with rfl | rfl <;> simp [duplicateDepth]

theorem operation_encode
    (op : Op)
    (input : Fin (arity op) -> Bool) :
    encode (interpretation op input) =
      (translation.operation op).eval interpretation
        (Block.flatten (encode ∘ input)) := by
  cases op with
  | not =>
      funext rail
      have railCases : rail = 0 ∨ rail = 1 := by omega
      rcases railCases with rfl | rfl
      · change encode (!(input 0)) 0 =
          notCircuit.eval interpretation (Block.flatten (encode ∘ input)) 0
        rw [notCircuit_eval_zero]
        change encode (!(input 0)) 0 = encode (input 0) 1
        simp
      · change encode (!(input 0)) 1 =
          notCircuit.eval interpretation (Block.flatten (encode ∘ input)) 1
        rw [notCircuit_eval_one]
        change encode (!(input 0)) 1 = encode (input 0) 0
        simp
  | and inputCount =>
      funext rail
      have railCases : rail = 0 ∨ rail = 1 := by omega
      rcases railCases with rfl | rfl
      · change encode (interpretation (.and inputCount) input) 0 =
          (andCircuit inputCount).eval interpretation
            (Block.flatten (encode ∘ input)) 0
        rw [andCircuit_eval_zero]
        simp
      · change encode (interpretation (.and inputCount) input) 1 =
          (andCircuit inputCount).eval interpretation
            (Block.flatten (encode ∘ input)) 1
        rw [andCircuit_eval_one]
        simp only [encode_one, Block.flatten_apply, Function.comp_apply,
          encode_one]
        apply Bool.eq_iff_iff.mpr
        simp [interpretation_and_eq_false]
  | or inputCount =>
      funext rail
      have railCases : rail = 0 ∨ rail = 1 := by omega
      rcases railCases with rfl | rfl
      · change encode (interpretation (.or inputCount) input) 0 =
          (orCircuit inputCount).eval interpretation
            (Block.flatten (encode ∘ input)) 0
        rw [orCircuit_eval_zero]
        simp
      · change encode (interpretation (.or inputCount) input) 1 =
          (orCircuit inputCount).eval interpretation
            (Block.flatten (encode ∘ input)) 1
        rw [orCircuit_eval_one]
        simp only [encode_one, Block.flatten_apply, Function.comp_apply,
          encode_one]
        apply Bool.eq_iff_iff.mpr
        simp [interpretation_or_eq_false]

/-- Boolean dual-rail simulation. -/
def booleanSimulation :
    BlockSimulation translation interpretation interpretation :=
  BlockSimulation.ofPreserves encode operation_encode

theorem operation_duplicateDepth
    (op : Op)
    (input : Fin (arity op) -> Nat) :
    duplicateDepth (logicalDepthInterpretation op input) =
      (translation.operation op).eval logicalDepthInterpretation
        (Block.flatten (duplicateDepth ∘ input)) := by
  cases op with
  | not =>
      funext rail
      have railCases : rail = 0 ∨ rail = 1 := by omega
      rcases railCases with rfl | rfl
      · change duplicateDepth (input 0) 0 =
          notCircuit.eval logicalDepthInterpretation
            (Block.flatten (duplicateDepth ∘ input)) 0
        rw [notCircuit_eval_zero]
        change duplicateDepth (input 0) 0 = duplicateDepth (input 0) 1
        simp
      · change duplicateDepth (input 0) 1 =
          notCircuit.eval logicalDepthInterpretation
            (Block.flatten (duplicateDepth ∘ input)) 1
        rw [notCircuit_eval_one]
        change duplicateDepth (input 0) 1 = duplicateDepth (input 0) 0
        simp
  | and inputCount =>
      funext rail
      have railCases : rail = 0 ∨ rail = 1 := by omega
      rcases railCases with rfl | rfl
      · change duplicateDepth (logicalDepthInterpretation (.and inputCount) input) 0 =
          (andCircuit inputCount).eval logicalDepthInterpretation
            (Block.flatten (duplicateDepth ∘ input)) 0
        rw [andCircuit_eval_zero]
        simp
      · change duplicateDepth (logicalDepthInterpretation (.and inputCount) input) 1 =
          (andCircuit inputCount).eval logicalDepthInterpretation
            (Block.flatten (duplicateDepth ∘ input)) 1
        rw [andCircuit_eval_one]
        simp [logicalDepthInterpretation]
  | or inputCount =>
      funext rail
      have railCases : rail = 0 ∨ rail = 1 := by omega
      rcases railCases with rfl | rfl
      · change duplicateDepth (logicalDepthInterpretation (.or inputCount) input) 0 =
          (orCircuit inputCount).eval logicalDepthInterpretation
            (Block.flatten (duplicateDepth ∘ input)) 0
        rw [orCircuit_eval_zero]
        simp [logicalDepthInterpretation]
      · change duplicateDepth (logicalDepthInterpretation (.or inputCount) input) 1 =
          (orCircuit inputCount).eval logicalDepthInterpretation
            (Block.flatten (duplicateDepth ∘ input)) 1
        rw [orCircuit_eval_one]
        simp [logicalDepthInterpretation]

/-- Logical-depth dual-rail simulation. -/
def depthSimulation :
    BlockSimulation translation logicalDepthInterpretation
      logicalDepthInterpretation :=
  BlockSimulation.ofPreserves duplicateDepth operation_duplicateDepth

theorem pullCost_andOrCost (op : Op) :
    translation.pullCost andOrCost op = 2 * andOrCost op := by
  cases op <;> simp [translation, gateCount, notCircuit, andCircuit,
    orCircuit, andPositiveLine, andNegativeLine, orPositiveLine,
    orNegativeLine, BlockTranslation.pullCost, Circuit.cost, Program.cost,
    andOrCost]

/-! ## Whole-circuit normalization -/

/-- The first `g` input-negation gates over an `n`-input namespace. -/
def inputNegationProgram (n : Nat) :
    (g : Nat) -> g <= n -> Program signature n g
  | 0, _ => .empty
  | g + 1, bound =>
      (inputNegationProgram n g
        (Nat.le_trans (Nat.le_succ g) bound)).gate {
        op := .not
        wires := fun _ => Wire.input
          ⟨g, Nat.lt_of_succ_le bound⟩
      }

@[simp] private theorem inputNegationProgram_eval
    (bound : g <= n)
    (input : Fin n -> Bool)
    (gate : Fin g) :
    (inputNegationProgram n g bound).eval interpretation input gate =
      !input (Fin.castLE bound gate) := by
  induction g with
  | zero => exact Fin.elim0 gate
  | succ g inductionHypothesis =>
      refine Fin.lastCases ?_ (fun priorGate => ?_) gate
      · rw [inputNegationProgram, Program.eval_gate_last]
        simp [Line.eval, interpretation]
        rw [show (⟨g, by omega⟩ : Fin (n + g)) =
            (Wire.input (⟨g, Nat.lt_of_succ_le bound⟩ : Fin n) :
              Wire n g) by
          apply Fin.ext
          rfl]
        rw [Fin.addCases_left]
        apply congrArg input
        apply Fin.ext
        rfl
      · rw [inputNegationProgram, Program.eval_gate_castSucc]
        rw [inductionHypothesis]
        congr 2

/-- Generate the positive and negative literal rails for every input. The
encoder has one NOT gate per input, and each such gate reads that input
directly. -/
def inputEncoder (n : Nat) : Circuit signature n n (n * 2) where
  program := inputNegationProgram n n (Nat.le_refl n)
  outputs := Block.flatten fun input rail =>
    Fin.cases (Wire.input input) (fun _ => Wire.gate input) rail

/-- The input encoder computes each input together with its complement. -/
@[simp] theorem inputEncoder_eval
    (input : Fin n -> Bool) :
    (inputEncoder n).eval interpretation input =
      Block.flatten (encode ∘ input) := by
  funext output
  obtain ⟨⟨sourceInput, rail⟩, rfl⟩ := finProdFinEquiv.surjective output
  have railCases : rail = 0 ∨ rail = 1 := by omega
  rcases railCases with rfl | rfl
  · simp [inputEncoder, Circuit.eval]
  · simp only [inputEncoder, Circuit.eval, Function.comp_apply,
      Block.flatten_apply, encode_one]
    change (inputNegationProgram n n (Nat.le_refl n)).trace
        interpretation input (Wire.gate sourceInput) = !input sourceInput
    rw [Program.trace_gateWire]
    exact inputNegationProgram_eval (Nat.le_refl n) input sourceInput

@[simp] private theorem inputNegationProgram_depth_eval
    (bound : g <= n)
    (input : Fin n -> Nat)
    (gate : Fin g) :
    (inputNegationProgram n g bound).eval
        logicalDepthInterpretation input gate =
      input (Fin.castLE bound gate) := by
  induction g with
  | zero => exact Fin.elim0 gate
  | succ g inductionHypothesis =>
      refine Fin.lastCases ?_ (fun priorGate => ?_) gate
      · rw [inputNegationProgram, Program.eval_gate_last]
        simp [Line.eval, logicalDepthInterpretation]
        rw [show (⟨g, by omega⟩ : Fin (n + g)) =
            (Wire.input (⟨g, Nat.lt_of_succ_le bound⟩ : Fin n) :
              Wire n g) by
          apply Fin.ext
          rfl]
        rw [Fin.addCases_left]
        apply congrArg input
        apply Fin.ext
        rfl
      · rw [inputNegationProgram, Program.eval_gate_castSucc]
        rw [inductionHypothesis]
        congr 1

/-- Input encoding adds no logical depth: both rails inherit their input's
arrival time. -/
@[simp] theorem inputEncoder_depth_eval
    (input : Fin n -> Nat) :
    (inputEncoder n).eval logicalDepthInterpretation input =
      Block.flatten (duplicateDepth ∘ input) := by
  funext output
  obtain ⟨⟨sourceInput, rail⟩, rfl⟩ := finProdFinEquiv.surjective output
  have railCases : rail = 0 ∨ rail = 1 := by omega
  rcases railCases with rfl | rfl
  · simp [inputEncoder, Circuit.eval]
  · simp only [inputEncoder, Circuit.eval, Function.comp_apply,
      Block.flatten_apply, duplicateDepth_apply]
    change (inputNegationProgram n n (Nat.le_refl n)).trace
        logicalDepthInterpretation input (Wire.gate sourceInput) =
      input sourceInput
    rw [Program.trace_gateWire]
    exact inputNegationProgram_depth_eval
      (Nat.le_refl n) input sourceInput

@[simp] private theorem inputNegationProgram_andOrCost
    (bound : g <= n) :
    (inputNegationProgram n g bound).cost andOrCost = 0 := by
  induction g with
  | zero => rfl
  | succ g inductionHypothesis =>
      simp [inputNegationProgram, andOrCost, inductionHypothesis]

/-- Input encoding has zero charged AND/OR cost. -/
@[simp] theorem inputEncoder_andOrCost (n : Nat) :
    (inputEncoder n).cost andOrCost = 0 := by
  exact inputNegationProgram_andOrCost (Nat.le_refl n)

/-- Internal predicate used to prove that the compiled portion contains no
NOT gates. -/
private def NegationFree : Program signature n g -> Prop
  | .empty => True
  | .gate program line => NegationFree program ∧ line.op ≠ .not

private theorem negationFree_instantiate
    (source : Program signature n g)
    (ambient : Program signature n' h)
    (inputWires : Fin n -> Wire n' h)
    (sourceFree : NegationFree source)
    (ambientFree : NegationFree ambient) :
    NegationFree (source.instantiate ambient inputWires) := by
  induction source with
  | empty => simpa [Program.instantiate, NegationFree] using ambientFree
  | gate source line inductionHypothesis =>
      exact ⟨inductionHypothesis sourceFree.1,
        by simpa using sourceFree.2⟩

private theorem operation_negationFree (op : Op) :
    NegationFree (translation.operation op).program := by
  cases op <;> simp [translation, notCircuit, andCircuit, orCircuit,
    andPositiveLine, andNegativeLine, orPositiveLine, orNegativeLine,
    NegationFree]

private theorem compileProgram_negationFree
    (source : Program signature n g) :
    NegationFree (translation.compileProgram source).program := by
  induction source with
  | empty => simp [BlockTranslation.compileProgram, NegationFree]
  | gate source line inductionHypothesis =>
      simp only [BlockTranslation.compileProgram]
      exact negationFree_instantiate _ _ _
        (operation_negationFree line.op) inductionHypothesis

private theorem negationAtInput_map_of_ne
    (line : Line signature n g)
    (wireMap : Wire n g -> Wire n' h)
    (notNegation : line.op ≠ .not) :
    AC0.Line.NegationAtInput (line.mapWires wireMap) := by
  rcases line with ⟨op, wires⟩
  cases op <;>
    simp [AC0.Line.NegationAtInput, Algebraic.Line.mapWires] at notNegation ⊢

private theorem negationsAtInputs_instantiate_of_negationFree
    (source : Program signature n g)
    (ambient : Program signature n' h)
    (inputWires : Fin n -> Wire n' h)
    (sourceFree : NegationFree source)
    (ambientNormal : AC0.Program.NegationsAtInputs ambient) :
    AC0.Program.NegationsAtInputs
      (source.instantiate ambient inputWires) := by
  induction source with
  | empty => simpa [Program.instantiate] using ambientNormal
  | gate source line inductionHypothesis =>
      exact ⟨inductionHypothesis sourceFree.1,
        negationAtInput_map_of_ne line _ sourceFree.2⟩

private theorem inputNegationProgram_negationsAtInputs
    (bound : g <= n) :
    AC0.Program.NegationsAtInputs
      (inputNegationProgram n g bound) := by
  induction g with
  | zero => trivial
  | succ g inductionHypothesis =>
      refine ⟨inductionHypothesis _, ?_⟩
      refine ⟨⟨g, Nat.lt_of_succ_le bound⟩, ?_⟩
      apply Fin.ext
      rfl

/-- Every NOT in the input encoder reads an original input. -/
theorem inputEncoder_negationsAtInputs (n : Nat) :
    AC0.Program.NegationsAtInputs (inputEncoder n).program :=
  inputNegationProgram_negationsAtInputs (Nat.le_refl n)

/-- Project the positive rail of every compiled output. -/
def positiveOutputs
    (circuit : Circuit signature n g (m * 2)) :
    Circuit signature n g m :=
  circuit.mapOutputs fun output =>
    finProdFinEquiv (output, (0 : Fin 2))

/-- Eliminate every internal negation by dual-rail compilation. The resulting
circuit contains `n` input-literal NOT gates followed by a negation-free
compiled program. -/
def normalize (circuit : Circuit signature n g m) :
    Circuit signature n
      (n + translation.compiledGateCount circuit) m :=
  (positiveOutputs (translation.compile circuit)).comp (inputEncoder n)

/-- The normalized circuit satisfies the checked input-negation invariant. -/
theorem normalize_negationsAtInputs
    (circuit : Circuit signature n g m) :
    AC0.Program.NegationsAtInputs (normalize circuit).program := by
  apply negationsAtInputs_instantiate_of_negationFree
  · exact compileProgram_negationFree circuit.program
  · exact inputEncoder_negationsAtInputs n

@[simp] private theorem booleanSimulation_map (value : Bool) :
    booleanSimulation.map value = encode value := rfl

@[simp] private theorem depthSimulation_map (depth : Nat) :
    depthSimulation.map depth = duplicateDepth depth := rfl

/-- Normalization preserves the full output vector on every Boolean input. -/
@[simp] theorem normalize_eval
    (circuit : Circuit signature n g m)
    (input : Fin n -> Bool) :
    (normalize circuit).eval interpretation input =
      circuit.eval interpretation input := by
  funext output
  rw [normalize, Circuit.eval_comp, inputEncoder_eval]
  change (translation.compile circuit).eval interpretation
      (Block.flatten (encode ∘ input))
      (finProdFinEquiv (output, (0 : Fin 2))) = _
  have simulated := congrFun
    (booleanSimulation.map_compile_eval circuit input)
    (finProdFinEquiv (output, (0 : Fin 2)))
  change Block.flatten (encode ∘ circuit.eval interpretation input)
      (finProdFinEquiv (output, (0 : Fin 2))) =
    (translation.compile circuit).eval interpretation
      (Block.flatten (encode ∘ input))
      (finProdFinEquiv (output, (0 : Fin 2))) at simulated
  simpa using simulated.symm

/-- Normalization preserves the logical depth of every designated output. -/
@[simp] theorem normalize_logicalOutputDepths
    (circuit : Circuit signature n g m) :
    Circuit.logicalOutputDepths (normalize circuit) =
      Circuit.logicalOutputDepths circuit := by
  funext output
  rw [Circuit.logicalOutputDepths, normalize, Circuit.eval_comp,
    inputEncoder_depth_eval]
  change (translation.compile circuit).eval logicalDepthInterpretation
      (Block.flatten (duplicateDepth ∘ (fun _ : Fin n => 0)))
      (finProdFinEquiv (output, (0 : Fin 2))) = _
  have simulated := congrFun
    (depthSimulation.map_compile_eval circuit (fun _ : Fin n => 0))
    (finProdFinEquiv (output, (0 : Fin 2)))
  change Block.flatten
      (duplicateDepth ∘
        circuit.eval logicalDepthInterpretation (fun _ : Fin n => 0))
      (finProdFinEquiv (output, (0 : Fin 2))) =
    (translation.compile circuit).eval logicalDepthInterpretation
      (Block.flatten (duplicateDepth ∘ (fun _ : Fin n => 0)))
      (finProdFinEquiv (output, (0 : Fin 2))) at simulated
  simpa [Circuit.logicalOutputDepths] using simulated.symm

/-- Normalization preserves maximum logical depth exactly. -/
@[simp] theorem normalize_logicalDepth
    (circuit : Circuit signature n g m) :
    Circuit.logicalDepth (normalize circuit) =
      Circuit.logicalDepth circuit := by
  simp [Circuit.logicalDepth]

private theorem cost_two_mul_andOrCost
    (program : Program signature n g) :
    program.cost (fun op => 2 * andOrCost op) =
      2 * program.cost andOrCost := by
  induction program with
  | empty => rfl
  | gate program line inductionHypothesis =>
      simp [Program.cost, inductionHypothesis, Nat.mul_add]

/-- The compiled dual-rail DAG has exactly twice the source AND/OR cost. -/
@[simp] theorem compile_andOrCost
    (circuit : Circuit signature n g m) :
    (translation.compile circuit).cost andOrCost =
      2 * circuit.cost andOrCost := by
  rw [translation.compile_cost]
  have pulledCost : translation.pullCost andOrCost =
      fun op => 2 * andOrCost op := by
    funext op
    exact pullCost_andOrCost op
  rw [pulledCost]
  exact cost_two_mul_andOrCost circuit.program

/-- Whole-circuit normalization has exactly twice the source AND/OR cost. -/
@[simp] theorem normalize_andOrCost
    (circuit : Circuit signature n g m) :
    (normalize circuit).cost andOrCost =
      2 * circuit.cost andOrCost := by
  simp [normalize, positiveOutputs]

private theorem compileProgram_gateCount
    (program : Program signature n g) :
    (translation.compileProgram program).gateCount =
      2 * program.cost andOrCost := by
  induction program with
  | empty => rfl
  | gate program line inductionHypothesis =>
      change (translation.compileProgram program).gateCount +
          gateCount line.op =
        2 * (program.cost andOrCost + andOrCost line.op)
      rw [inductionHypothesis]
      cases line.op <;> simp [gateCount, andOrCost, Nat.mul_add]

/-- Normalization uses one input-literal gate per input and two gates per
charged source gate. -/
@[simp] theorem normalize_size
    (circuit : Circuit signature n g m) :
    (normalize circuit).size =
      n + 2 * circuit.cost andOrCost := by
  change n + translation.compiledGateCount circuit = _
  rw [BlockTranslation.compiledGateCount,
    compileProgram_gateCount circuit.program]
  rfl

/-! ## Family-level normalization -/

/-- Normalize every member of a circuit family. -/
def normalizeFamily
    (family : Circuit.Family signature m) :
    Circuit.Family signature m where
  gateCount := fun n =>
    n + translation.compiledGateCount (family.circuit n)
  circuit := fun n => normalize (family.circuit n)

/-- The member at width `n` is the normalization of the source member. -/
@[simp] theorem normalizeFamily_circuit
    (family : Circuit.Family signature m)
    (n : Nat) :
    (normalizeFamily family).circuit n =
      normalize (family.circuit n) :=
  rfl

/-- Family normalization doubles charged cost pointwise. -/
@[simp] theorem normalizeFamily_cost
    (family : Circuit.Family signature m)
    (n : Nat) :
    (normalizeFamily family).cost andOrCost n =
      2 * family.cost andOrCost n := by
  change (normalize (family.circuit n)).cost andOrCost =
    2 * (family.circuit n).cost andOrCost
  exact normalize_andOrCost (family.circuit n)

/-- Family normalization has one input-literal gate per input and two gates
per charged source gate. -/
@[simp] theorem normalizeFamily_gateCount
    (family : Circuit.Family signature m)
    (n : Nat) :
    (normalizeFamily family).gateCount n =
      n + 2 * family.cost andOrCost n := by
  change (normalize (family.circuit n)).size =
    n + 2 * (family.circuit n).cost andOrCost
  exact normalize_size (family.circuit n)

/-- Family normalization preserves logical depth pointwise. -/
@[simp] theorem normalizeFamily_logicalDepth
    (family : Circuit.Family signature m)
    (n : Nat) :
    Family.logicalDepth (normalizeFamily family) n =
      Family.logicalDepth family n := by
  change Circuit.logicalDepth (normalize (family.circuit n)) =
    Circuit.logicalDepth (family.circuit n)
  exact normalize_logicalDepth (family.circuit n)

/-- Family normalization preserves the computed target. -/
theorem normalizeFamily_computes
    (family : Circuit.Family signature m)
    (target : Target.Family Bool m)
    (computes : family.Computes interpretation target) :
    (normalizeFamily family).Computes interpretation target := by
  intro n input
  change (normalize (family.circuit n)).eval interpretation input =
    target n input
  exact (normalize_eval (family.circuit n) input).trans (computes n input)

/-- Every normalized family member has only input-level negations. -/
theorem normalizeFamily_negationsAtInputs
    (family : Circuit.Family signature m) :
    Family.NegationsAtInputs (normalizeFamily family) := by
  intro n
  exact normalize_negationsAtInputs (family.circuit n)

/-- Polynomial AND/OR cost is preserved by family normalization. -/
theorem normalizeFamily_hasPolynomialCost
    (family : Circuit.Family signature m)
    (bounded : family.HasPolynomialCost andOrCost) :
    (normalizeFamily family).HasPolynomialCost andOrCost := by
  obtain ⟨coefficient, degree, bound⟩ := bounded
  refine ⟨2 * coefficient, degree, ?_⟩
  intro n
  rw [normalizeFamily_cost]
  calc
    2 * family.cost andOrCost n <=
        2 * (coefficient * (n + 1) ^ degree) :=
      Nat.mul_le_mul_left 2 (bound n)
    _ = (2 * coefficient) * (n + 1) ^ degree := by
      rw [Nat.mul_assoc]

/-- Normalization turns polynomial charged cost into polynomial total gate
count, with the explicit bound
`(2 * coefficient + 1) * (n + 1) ^ (degree + 1)`. -/
theorem normalizeFamily_hasPolynomialSize
    (family : Circuit.Family signature m)
    (bounded : family.HasPolynomialCost andOrCost) :
    (normalizeFamily family).HasPolynomialSize := by
  obtain ⟨coefficient, degree, bound⟩ := bounded
  refine ⟨2 * coefficient + 1, degree + 1, ?_⟩
  intro n
  change (normalizeFamily family).gateCount n <= _
  rw [normalizeFamily_gateCount]
  have basePositive : 0 < n + 1 := by omega
  have inputBound : n <= (n + 1) ^ (degree + 1) :=
    (Nat.le_succ n).trans (Nat.le_pow (by omega))
  have powerBound :
      (n + 1) ^ degree <= (n + 1) ^ (degree + 1) :=
    Nat.pow_le_pow_right basePositive (Nat.le_succ degree)
  calc
    n + 2 * family.cost andOrCost n <=
        (n + 1) ^ (degree + 1) +
          2 * (coefficient * (n + 1) ^ degree) :=
      Nat.add_le_add inputBound (Nat.mul_le_mul_left 2 (bound n))
    _ <= (n + 1) ^ (degree + 1) +
          2 * (coefficient * (n + 1) ^ (degree + 1)) := by
      apply Nat.add_le_add_left
      simpa [Nat.mul_assoc] using
        Nat.mul_le_mul_left (2 * coefficient) powerBound
    _ = (2 * coefficient + 1) * (n + 1) ^ (degree + 1) := by
      simp [Nat.add_mul, Nat.mul_assoc, Nat.add_comm]

/-- Constant logical depth is preserved by family normalization. -/
theorem normalizeFamily_hasConstantLogicalDepth
    (family : Circuit.Family signature m)
    (bounded : Family.HasConstantLogicalDepth family) :
    Family.HasConstantLogicalDepth (normalizeFamily family) := by
  obtain ⟨depth, bound⟩ := bounded
  exact ⟨depth, fun n => by simpa using bound n⟩

/-- Every raw small-depth family has an equivalent checked family. -/
theorem normalizeFamily_isSmallDepth
    (family : Circuit.Family signature 1)
    (smallDepth : Family.IsRawSmallDepth family) :
    Family.IsSmallDepth (normalizeFamily family) :=
  ⟨normalizeFamily_hasPolynomialCost family smallDepth.1,
    normalizeFamily_hasConstantLogicalDepth family smallDepth.2,
    normalizeFamily_negationsAtInputs family⟩

end DualRail

/-- Raw and input-negation-normalized presentations define the same
nonuniform AC0 class. -/
theorem rawComputable_iff_computable
    (target : Target.Family Bool 1) :
    RawComputable target <-> Computable target := by
  constructor
  · rintro ⟨family, computes, smallDepth⟩
    exact ⟨DualRail.normalizeFamily family,
      DualRail.normalizeFamily_computes family target computes,
      DualRail.normalizeFamily_isSmallDepth family smallDepth⟩
  · rintro ⟨family, computes, smallDepth⟩
    exact ⟨family, computes, smallDepth.raw⟩

end AC0
end Algebraic
