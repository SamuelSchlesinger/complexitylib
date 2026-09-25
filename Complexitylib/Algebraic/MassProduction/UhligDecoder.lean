/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Arithmetic
public import Complexitylib.Algebraic.MassProduction.UhligRoutingCircuit

/-!
# Uhlig decoder circuits

This module specifies the XOR decoder over one completed routing/resource
state and implements it with shared linear-size Boolean folds. The final
theorems identify the decoder's output with the semantic value selected by
each request pair and give its exact gate cost.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace UhligCircuit

open scoped BigOperators

/-! ## Generic expression compatibility names -/

/-- Compatibility name for generic De Morgan expression input mapping. -/
abbrev reindexExpression
    (inputMap : Fin sourceInputs -> Fin targetInputs)
    (expression : DeMorgan.Expression sourceInputs) :
    DeMorgan.Expression targetInputs :=
  expression.mapInputs inputMap

theorem reindexExpression_eval
    (inputMap : Fin sourceInputs -> Fin targetInputs)
    (expression : DeMorgan.Expression sourceInputs)
    (input : Fin targetInputs -> Bool) :
    (reindexExpression inputMap expression).eval input =
      expression.eval (input ∘ inputMap) :=
  DeMorgan.Expression.mapInputs_eval inputMap expression input

theorem reindexExpression_gateCount
    (inputMap : Fin sourceInputs -> Fin targetInputs)
    (expression : DeMorgan.Expression sourceInputs) :
    (reindexExpression inputMap expression).gateCount =
      expression.gateCount :=
  DeMorgan.Expression.mapInputs_gateCount inputMap expression

theorem reindexExpression_standardCost
    (inputMap : Fin sourceInputs -> Fin targetInputs)
    (expression : DeMorgan.Expression sourceInputs) :
    (reindexExpression inputMap expression).standardCost =
      expression.standardCost :=
  DeMorgan.Expression.mapInputs_standardCost inputMap expression

/-- Compatibility name for the generic De Morgan XOR expression. -/
abbrev xorExpression
    (left right : DeMorgan.Expression inputs) :
    DeMorgan.Expression inputs :=
  DeMorgan.Expression.xor left right

theorem xorExpression_eval
    (left right : DeMorgan.Expression inputs)
    (input : Fin inputs -> Bool) :
    (xorExpression left right).eval input =
      left.eval input + right.eval input :=
  DeMorgan.Expression.xor_eval left right input

/-- Compatibility name for the generic finite XOR expression fold. -/
abbrev finXor
    (count : Nat)
    (terms : Fin count -> DeMorgan.Expression inputs) :
    DeMorgan.Expression inputs :=
  DeMorgan.Expression.finXor count terms

theorem finXor_eval
    (count : Nat)
    (terms : Fin count -> DeMorgan.Expression inputs)
    (input : Fin inputs -> Bool) :
    (finXor count terms).eval input =
      Finset.univ.sum fun index => (terms index).eval input :=
  DeMorgan.Expression.finXor_eval count terms input

/-- Number of original input wires in one batched Uhlig layer. -/
@[reducible] def layerInputCount
    (prefixWidth suffixWidth pairs : Nat) : Nat :=
  (2 * pairs) * (prefixWidth + suffixWidth)

/-- Number of resource-result wires in one batched Uhlig layer. -/
@[reducible] def layerResourceOutputCount (prefixWidth pairs : Nat) : Nat :=
  (prefixLast prefixWidth + 2) * pairs

/-- Original inputs followed by every `(resource, pair)` result. -/
@[reducible] def layerStateCount
    (prefixWidth suffixWidth pairs : Nat) : Nat :=
  layerInputCount prefixWidth suffixWidth pairs +
    layerResourceOutputCount prefixWidth pairs

/-- Read the original-input prefix of a layer state. -/
def originalInputFromState
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    Fin (layerInputCount prefixWidth suffixWidth pairs) -> Bool :=
  fun input => state
    (Fin.castAdd (layerResourceOutputCount prefixWidth pairs) input)

/-- State wire carrying one resource result. -/
def resourceStateIndex
    (resource : Fin (prefixLast prefixWidth + 2))
    (pair : Fin pairs) :
    Fin (layerStateCount prefixWidth suffixWidth pairs) :=
  Fin.natAdd (layerInputCount prefixWidth suffixWidth pairs)
    (finProdFinEquiv (resource, pair))

/-- Embed one local pair input into the original-input prefix of a layer
state. -/
def stateLocalInputMap
    (pair : Fin pairs)
    (input : Fin (2 * (prefixWidth + suffixWidth))) :
    Fin (layerStateCount prefixWidth suffixWidth pairs) :=
  Fin.castAdd (layerResourceOutputCount prefixWidth pairs)
    (pairInputMap pair input)

/-- Prefix equality test for one request inside a layer state. -/
def stateSourceIndicatorExpression
    (pair : Fin pairs)
    (side : Fin 2)
    (source : Fin (prefixLast prefixWidth + 1)) :
    DeMorgan.Expression (layerStateCount prefixWidth suffixWidth pairs) :=
  (sourceIndicatorExpression (suffixWidth := suffixWidth) side source).mapInputs
    (stateLocalInputMap pair)

theorem stateSourceIndicatorExpression_eval_eq_true_iff
    (pair : Fin pairs)
    (side : Fin 2)
    (source : Fin (prefixLast prefixWidth + 1))
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (stateSourceIndicatorExpression pair side source).eval state = true <->
      requestSource (originalInputFromState state) pair side = source := by
  rw [stateSourceIndicatorExpression, DeMorgan.Expression.mapInputs_eval,
    sourceIndicatorExpression_eval_eq_true_iff]
  have composition : state ∘ stateLocalInputMap pair =
      originalInputFromState state ∘ pairInputMap pair := by
    rfl
  rw [composition, localSource_pairInputMap]

/-- Resource-result input expression for the decoder. -/
def resourceValueExpression
    (resource : Fin (prefixLast prefixWidth + 2))
    (pair : Fin pairs) :
    DeMorgan.Expression (layerStateCount prefixWidth suffixWidth pairs) :=
  .input (resourceStateIndex resource pair)

/-- One fixed decoder term: either the selected resource-result wire or the
free false constant. -/
def fixedResourceTermExpression
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1))
    (resource : Fin (prefixLast prefixWidth + 2)) :
    DeMorgan.Expression (layerStateCount prefixWidth suffixWidth pairs) :=
  let resources : Finset (Fin (prefixLast prefixWidth + 2)) :=
    Fin.cases (uhligRecoveryPair first second).1
      (fun _ => (uhligRecoveryPair first second).2) side
  if resource ∈ resources then resourceValueExpression resource pair
  else .constant false

/-- XOR decoder for fixed prefix values. -/
def fixedDecodedExpression
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    DeMorgan.Expression (layerStateCount prefixWidth suffixWidth pairs) :=
  DeMorgan.Expression.finXor (prefixLast prefixWidth + 2) fun resource =>
    fixedResourceTermExpression pair side first second resource

theorem fixedDecodedExpression_eval
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1))
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (fixedDecodedExpression pair side first second).eval state =
      let resources : Finset (Fin (prefixLast prefixWidth + 2)) :=
        Fin.cases (uhligRecoveryPair first second).1
          (fun _ => (uhligRecoveryPair first second).2) side
      resources.sum fun resource => state (resourceStateIndex resource pair) := by
  classical
  let resources : Finset (Fin (prefixLast prefixWidth + 2)) :=
    Fin.cases (uhligRecoveryPair first second).1
      (fun _ => (uhligRecoveryPair first second).2) side
  rw [fixedDecodedExpression, DeMorgan.Expression.finXor_eval]
  simp only [fixedResourceTermExpression]
  simp_rw [apply_ite (DeMorgan.Expression.eval state)]
  simp only [DeMorgan.Expression.eval, resourceValueExpression]
  change
    (Finset.univ.sum fun resource =>
      if resource ∈ resources then
        state (resourceStateIndex resource pair)
      else false) =
      resources.sum fun resource => state (resourceStateIndex resource pair)
  calc
    (Finset.univ.sum fun resource =>
        if resource ∈ resources then
          state (resourceStateIndex resource pair)
        else false) =
        resources.sum (fun resource =>
          if resource ∈ resources then
            state (resourceStateIndex resource pair)
          else false) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ resources)
      intro resource _inUniv notSelected
      simp [notSelected]
      rfl
    _ = resources.sum
        (fun resource => state (resourceStateIndex resource pair)) := by
      apply Finset.sum_congr rfl
      intro resource selected
      simp [selected]

/-- Runtime decoder selected by the two actual request prefixes. -/
def decodedExpression
    (pair : Fin pairs) (side : Fin 2) :
    DeMorgan.Expression (layerStateCount prefixWidth suffixWidth pairs) :=
  DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun first =>
    .and (stateSourceIndicatorExpression pair 0 first)
      (DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun second =>
        .and (stateSourceIndicatorExpression pair 1 second)
          (fixedDecodedExpression pair side first second))

/-- Semantic decoder on a completed layer state. -/
def decodedStateValue
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool)
    (pair : Fin pairs) (side : Fin 2) : Bool :=
  let original := originalInputFromState state
  let resources : Finset (Fin (prefixLast prefixWidth + 2)) :=
    Fin.cases
      (uhligRecoveryPair (requestSource original pair 0)
        (requestSource original pair 1)).1
      (fun _ =>
        (uhligRecoveryPair (requestSource original pair 0)
          (requestSource original pair 1)).2)
      side
  resources.sum fun resource => state (resourceStateIndex resource pair)

theorem decodedExpression_eval
    (pair : Fin pairs) (side : Fin 2)
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (decodedExpression pair side).eval state =
      decodedStateValue state pair side := by
  rw [decodedExpression, DeMorgan.Expression.finOr_eval]
  simp only [DeMorgan.Expression.eval]
  let first := requestSource (originalInputFromState state) pair 0
  let second := requestSource (originalInputFromState state) pair 1
  have firstTrue :
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 first).eval state = true :=
    (stateSourceIndicatorExpression_eval_eq_true_iff
      pair 0 first state).2 rfl
  have firstUnique : forall candidate,
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 candidate).eval state = true -> candidate = first := by
    intro candidate candidateTrue
    exact ((stateSourceIndicatorExpression_eval_eq_true_iff
      pair 0 candidate state).1 candidateTrue).symm
  rw [DeMorgan.Expression.finOrValue_oneHot
    (prefixLast prefixWidth + 1) first
    (fun candidate =>
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 candidate).eval state)
    (fun candidate =>
      (DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun other =>
        .and (stateSourceIndicatorExpression pair 1 other)
          (fixedDecodedExpression pair side candidate other)).eval state)
    firstTrue firstUnique]
  rw [DeMorgan.Expression.finOr_eval]
  simp only [DeMorgan.Expression.eval]
  have secondTrue :
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 second).eval state = true :=
    (stateSourceIndicatorExpression_eval_eq_true_iff
      pair 1 second state).2 rfl
  have secondUnique : forall candidate,
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 candidate).eval state = true -> candidate = second := by
    intro candidate candidateTrue
    exact ((stateSourceIndicatorExpression_eval_eq_true_iff
      pair 1 candidate state).1 candidateTrue).symm
  rw [DeMorgan.Expression.finOrValue_oneHot
    (prefixLast prefixWidth + 1) second
    (fun candidate =>
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 candidate).eval state)
    (fun candidate =>
      (fixedDecodedExpression pair side first candidate).eval state)
    secondTrue secondUnique]
  rw [fixedDecodedExpression_eval]
  rfl

/-! ## Decoder circuit -/

/-- Recover the pair and side represented by a row-major direct-product
output. -/
def decoderPairSide (output : Fin (2 * pairs)) : Fin pairs × Fin 2 :=
  finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 pairs) output)

/-- Decoder expression attached to one row-major output. -/
def decoderOutputExpression
    (output : Fin (2 * pairs)) :
    DeMorgan.Expression (layerStateCount prefixWidth suffixWidth pairs) :=
  let pairSide := decoderPairSide output
  decodedExpression pairSide.1 pairSide.2

/-- Gate count of one compiled decoder output. -/
@[reducible] noncomputable def decoderGateCount
    (prefixWidth suffixWidth pairs : Nat)
    (output : Fin (2 * pairs)) : Nat :=
  (decoderOutputExpression (prefixWidth := prefixWidth)
    (suffixWidth := suffixWidth) output).gateCount

/-- All requested outputs decoded in ordinary row-major order. -/
noncomputable def decoderCircuit
    (prefixWidth suffixWidth pairs : Nat) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      (Finset.univ.sum fun output : Fin (2 * pairs) =>
        decoderGateCount prefixWidth suffixWidth pairs output)
      (2 * pairs) :=
  Circuit.parallelFin (2 * pairs)
    (decoderGateCount prefixWidth suffixWidth pairs)
    (fun output =>
      (decoderOutputExpression (prefixWidth := prefixWidth)
        (suffixWidth := suffixWidth) output).circuit)

@[simp] theorem decoderCircuit_eval
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool)
    (output : Fin (2 * pairs)) :
    (decoderCircuit prefixWidth suffixWidth pairs).eval
        DeMorgan.interpretation state output =
      let pairSide := decoderPairSide output
      decodedStateValue state pairSide.1 pairSide.2 := by
  rw [decoderCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval, decoderOutputExpression,
    decodedExpression_eval]

@[simp] theorem decoderCircuit_cost
    (prefixWidth suffixWidth pairs : Nat) :
    (decoderCircuit prefixWidth suffixWidth pairs).cost
        DeMorgan.standardCost =
      Finset.univ.sum fun output : Fin (2 * pairs) =>
        (decoderOutputExpression (prefixWidth := prefixWidth)
          (suffixWidth := suffixWidth) output).standardCost := by
  simp [decoderCircuit]

/-! ## Shared linear-size Boolean folds -/

/-- Arithmetic XOR of all input wires.  Compiling the arithmetic addition
gate preserves sharing, so this avoids the duplication inherent in a
De Morgan formula for XOR. -/
def xorInputExpression (count : Nat) :
    Arithmetic.Expression Bool count :=
  DeMorgan.ArithmeticExpression.finSum count fun input => .input input

/-- Program-gate count of the shared XOR fold. -/
@[reducible] noncomputable def xorInputGateCount (count : Nat) : Nat :=
  DeMorgan.arithmeticTranslation.compiledGateCount
    (xorInputExpression count).circuit

/-- De Morgan circuit obtained by compiling the shared arithmetic XOR fold. -/
noncomputable def xorInputCircuit (count : Nat) :
    Circuit DeMorgan.signature count (xorInputGateCount count) 1 :=
  DeMorgan.ArithmeticExpression.circuit (xorInputExpression count)

@[simp] theorem xorInputCircuit_eval
    (count : Nat) (input : Fin count -> Bool) :
    (xorInputCircuit count).eval DeMorgan.interpretation input 0 =
      Finset.univ.sum input := by
  rw [xorInputCircuit, DeMorgan.ArithmeticExpression.circuit_eval,
    xorInputExpression, DeMorgan.ArithmeticExpression.finSum_eval]
  rfl

@[simp] theorem xorInputCircuit_cost (count : Nat) :
    (xorInputCircuit count).cost DeMorgan.standardCost = count * 4 := by
  rw [xorInputCircuit, DeMorgan.ArithmeticExpression.circuit_cost,
    xorInputExpression,
    DeMorgan.ArithmeticExpression.finSum_weightedCost]
  simp [Arithmetic.Expression.weightedCost]

/-- OR of all input wires. -/
def orInputExpression (count : Nat) : DeMorgan.Expression count :=
  DeMorgan.Expression.finOr count fun input => .input input

/-- Program-gate count of the shared OR fold. -/
@[reducible] def orInputGateCount (count : Nat) : Nat :=
  (orInputExpression count).gateCount

/-- De Morgan circuit implementing the shared OR fold. -/
def orInputCircuit (count : Nat) :
    Circuit DeMorgan.signature count (orInputGateCount count) 1 :=
  (orInputExpression count).circuit

@[simp] theorem orInputCircuit_eval
    (count : Nat) (input : Fin count -> Bool) :
    (orInputCircuit count).eval DeMorgan.interpretation input 0 =
      DeMorgan.Expression.finOrValue count input := by
  rw [orInputCircuit, DeMorgan.Expression.circuit_eval,
    orInputExpression, DeMorgan.Expression.finOr_eval]
  rfl

@[simp] theorem orInputCircuit_cost (count : Nat) :
    (orInputCircuit count).cost DeMorgan.standardCost = count := by
  rw [orInputCircuit, DeMorgan.Expression.circuit_cost,
    orInputExpression, DeMorgan.Expression.finOr_standardCost]
  simp [DeMorgan.Expression.standardCost]

/-- Produce all fixed-prefix resource terms before their shared XOR fold. -/
noncomputable def fixedResourceVectorCircuit
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        (fixedResourceTermExpression (suffixWidth := suffixWidth)
          pair side first second resource).gateCount)
      (prefixLast prefixWidth + 2) :=
  Circuit.parallelFin (prefixLast prefixWidth + 2)
    (fun resource =>
      (fixedResourceTermExpression (suffixWidth := suffixWidth)
        pair side first second resource).gateCount)
    (fun resource =>
      (fixedResourceTermExpression (suffixWidth := suffixWidth)
        pair side first second resource).circuit)

@[simp] theorem fixedResourceVectorCircuit_eval
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1))
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool)
    (resource : Fin (prefixLast prefixWidth + 2)) :
    (fixedResourceVectorCircuit (suffixWidth := suffixWidth)
      pair side first second).eval
        DeMorgan.interpretation state resource =
      (fixedResourceTermExpression (suffixWidth := suffixWidth)
        pair side first second resource).eval
        state := by
  rw [fixedResourceVectorCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval]

@[simp] theorem fixedResourceVectorCircuit_cost
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    (fixedResourceVectorCircuit (suffixWidth := suffixWidth)
      pair side first second).cost
        DeMorgan.standardCost = 0 := by
  rw [fixedResourceVectorCircuit, Circuit.cost_parallelFin]
  apply Finset.sum_eq_zero
  intro resource _member
  rw [DeMorgan.Expression.circuit_cost]
  unfold fixedResourceTermExpression
  dsimp only
  split <;> rfl

/-- Fixed-prefix decoder with a circuit-level shared XOR fold. -/
noncomputable def sharedFixedDecodedCircuit
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      ((Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
          (fixedResourceTermExpression (suffixWidth := suffixWidth)
            pair side first second resource).gateCount) +
        xorInputGateCount (prefixLast prefixWidth + 2))
      1 :=
  (xorInputCircuit (prefixLast prefixWidth + 2)).comp
    (fixedResourceVectorCircuit (suffixWidth := suffixWidth)
      pair side first second)

@[simp] theorem sharedFixedDecodedCircuit_eval
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1))
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
      pair side first second).eval
        DeMorgan.interpretation state 0 =
      let resources : Finset (Fin (prefixLast prefixWidth + 2)) :=
        Fin.cases (uhligRecoveryPair first second).1
          (fun _ => (uhligRecoveryPair first second).2) side
      resources.sum fun resource =>
        state (resourceStateIndex resource pair) := by
  calc
    (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
      pair side first second).eval
        DeMorgan.interpretation state 0 =
        Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
          (fixedResourceTermExpression (suffixWidth := suffixWidth)
            pair side first second resource).eval
            state := by
      rw [sharedFixedDecodedCircuit, Circuit.eval_comp,
        xorInputCircuit_eval]
      apply Finset.sum_congr rfl
      intro resource _member
      exact fixedResourceVectorCircuit_eval pair side first second state
        resource
    _ = (fixedDecodedExpression pair side first second).eval state := by
      rw [fixedDecodedExpression, DeMorgan.Expression.finXor_eval]
    _ = _ := fixedDecodedExpression_eval pair side first second state

@[simp] theorem sharedFixedDecodedCircuit_cost
    (pair : Fin pairs)
    (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
      pair side first second).cost
        DeMorgan.standardCost = 4 * (prefixLast prefixWidth + 2) := by
  rw [sharedFixedDecodedCircuit, Circuit.cost_comp,
    fixedResourceVectorCircuit_cost, xorInputCircuit_cost]
  omega

/-- Three-input postprocessor for one candidate prefix pair.  The second
source indicator is outermost so the row decoder has one-hot form. -/
def candidatePostprocessExpression : DeMorgan.Expression 3 :=
  .and (.input 1) (.and (.input 0) (.input 2))

@[simp] theorem candidatePostprocessExpression_eval
    (input : Fin 3 -> Bool) :
    candidatePostprocessExpression.eval input =
      (input 1 && (input 0 && input 2)) := rfl

/-- Program-gate count of one fully specified decoder candidate. -/
@[reducible] noncomputable def candidateDecodedGateCount
    (prefixWidth suffixWidth pairs : Nat)
    (pair : Fin pairs) (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) : Nat :=
  (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
      pair 0 first).gateCount +
    ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 second).gateCount +
      ((Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
          (fixedResourceTermExpression (suffixWidth := suffixWidth)
            pair side first second resource).gateCount) +
        xorInputGateCount (prefixLast prefixWidth + 2))) +
    candidatePostprocessExpression.gateCount

/-- Circuit for one hardwired pair of possible request prefixes. -/
noncomputable def candidateDecodedCircuit
    (pair : Fin pairs) (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      (candidateDecodedGateCount prefixWidth suffixWidth pairs
        pair side first second)
      1 :=
  candidatePostprocessExpression.circuit.comp
    ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
      pair 0 first).circuit.parallel
      ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 second).circuit.parallel
        (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
          pair side first second)))

@[simp] theorem candidateDecodedCircuit_eval
    (pair : Fin pairs) (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1))
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (candidateDecodedCircuit pair side first second).eval
        DeMorgan.interpretation state 0 =
      ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
          pair 1 second).eval state &&
        ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
            pair 0 first).eval state &&
          (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
            pair side first second).eval DeMorgan.interpretation state 0)) := by
  change
    (candidatePostprocessExpression.circuit.comp
      ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 first).circuit.parallel
        ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
          pair 1 second).circuit.parallel
          (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
            pair side first second)))).eval
        DeMorgan.interpretation state 0 = _
  rw [Circuit.eval_comp, DeMorgan.Expression.circuit_eval,
    candidatePostprocessExpression_eval, Circuit.eval_parallel,
    Circuit.eval_parallel]
  rw [show (1 : Fin 3) =
      Fin.natAdd 1 (Fin.castAdd 1 (0 : Fin 1)) by rfl,
    Fin.append_right, Fin.append_left]
  rw [show (0 : Fin 3) = Fin.castAdd 2 (0 : Fin 1) by rfl,
    Fin.append_left]
  rw [show (2 : Fin 3) =
      Fin.natAdd 1 (Fin.natAdd 1 (0 : Fin 1)) by rfl,
    Fin.append_right, Fin.append_right]
  rw [DeMorgan.Expression.circuit_eval,
    DeMorgan.Expression.circuit_eval]

/-- Program-gate count of one row of decoder candidates. -/
@[reducible] noncomputable def candidateRowGateCount
    (prefixWidth suffixWidth pairs : Nat)
    (pair : Fin pairs) (side : Fin 2)
    (first : Fin (prefixLast prefixWidth + 1)) : Nat :=
  (Finset.univ.sum fun second : Fin (prefixLast prefixWidth + 1) =>
      candidateDecodedGateCount prefixWidth suffixWidth pairs
        pair side first second) +
    orInputGateCount (prefixLast prefixWidth + 1)

/-- OR all candidates for the second request prefix while retaining one
fixed candidate for the first prefix. -/
noncomputable def candidateRowCircuit
    (pair : Fin pairs) (side : Fin 2)
    (first : Fin (prefixLast prefixWidth + 1)) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      (candidateRowGateCount prefixWidth suffixWidth pairs pair side first)
      1 :=
  (orInputCircuit (prefixLast prefixWidth + 1)).comp
    (Circuit.parallelFin (prefixLast prefixWidth + 1)
      (fun second => candidateDecodedGateCount
        prefixWidth suffixWidth pairs pair side first second)
      (fun second => candidateDecodedCircuit pair side first second))

@[simp] theorem candidateRowCircuit_eval
    (pair : Fin pairs) (side : Fin 2)
    (first : Fin (prefixLast prefixWidth + 1))
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (candidateRowCircuit pair side first).eval
        DeMorgan.interpretation state 0 =
      ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
          pair 0 first).eval state &&
        (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
          pair side first
          (requestSource (originalInputFromState state) pair 1)).eval
            DeMorgan.interpretation state 0) := by
  change
    ((orInputCircuit (prefixLast prefixWidth + 1)).comp
      (Circuit.parallelFin (prefixLast prefixWidth + 1)
        (fun second => candidateDecodedGateCount
          prefixWidth suffixWidth pairs pair side first second)
        (fun second =>
          candidateDecodedCircuit pair side first second))).eval
        DeMorgan.interpretation state 0 = _
  rw [Circuit.eval_comp, orInputCircuit_eval]
  have bankEval :
      (Circuit.parallelFin (prefixLast prefixWidth + 1)
        (fun second => candidateDecodedGateCount
          prefixWidth suffixWidth pairs pair side first second)
        (fun second => candidateDecodedCircuit pair side first second)).eval
          DeMorgan.interpretation state =
        fun second =>
          (candidateDecodedCircuit pair side first second).eval
            DeMorgan.interpretation state 0 := by
    funext second
    exact Circuit.eval_parallelFin _ _ _ _ _ second
  rw [bankEval]
  simp only [candidateDecodedCircuit_eval]
  let second := requestSource (originalInputFromState state) pair 1
  have secondTrue :
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 second).eval state = true :=
    (stateSourceIndicatorExpression_eval_eq_true_iff
      pair 1 second state).2 rfl
  have secondUnique : forall candidate,
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 candidate).eval state = true -> candidate = second := by
    intro candidate candidateTrue
    exact ((stateSourceIndicatorExpression_eval_eq_true_iff
      pair 1 candidate state).1 candidateTrue).symm
  exact DeMorgan.Expression.finOrValue_oneHot
    (prefixLast prefixWidth + 1) second
    (fun candidate =>
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 1 candidate).eval state)
    (fun candidate =>
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
          pair 0 first).eval state &&
        (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
          pair side first candidate).eval DeMorgan.interpretation state 0)
    secondTrue secondUnique

/-- Program-gate count of one complete shared output decoder. -/
@[reducible] noncomputable def sharedDecodedGateCount
    (prefixWidth suffixWidth pairs : Nat)
    (pair : Fin pairs) (side : Fin 2) : Nat :=
  (Finset.univ.sum fun first : Fin (prefixLast prefixWidth + 1) =>
      candidateRowGateCount prefixWidth suffixWidth pairs pair side first) +
    orInputGateCount (prefixLast prefixWidth + 1)

/-- Shared decoder for one requested output. -/
noncomputable def sharedDecodedCircuit
    (pair : Fin pairs) (side : Fin 2) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      (sharedDecodedGateCount prefixWidth suffixWidth pairs pair side)
      1 :=
  (orInputCircuit (prefixLast prefixWidth + 1)).comp
    (Circuit.parallelFin (prefixLast prefixWidth + 1)
      (fun first => candidateRowGateCount
        prefixWidth suffixWidth pairs pair side first)
      (fun first => candidateRowCircuit pair side first))

@[simp] theorem sharedDecodedCircuit_eval
    (pair : Fin pairs) (side : Fin 2)
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool) :
    (sharedDecodedCircuit pair side).eval
        DeMorgan.interpretation state 0 =
      decodedStateValue state pair side := by
  change
    ((orInputCircuit (prefixLast prefixWidth + 1)).comp
      (Circuit.parallelFin (prefixLast prefixWidth + 1)
        (fun first => candidateRowGateCount
          prefixWidth suffixWidth pairs pair side first)
        (fun first => candidateRowCircuit pair side first))).eval
        DeMorgan.interpretation state 0 = _
  rw [Circuit.eval_comp, orInputCircuit_eval]
  have bankEval :
      (Circuit.parallelFin (prefixLast prefixWidth + 1)
        (fun first => candidateRowGateCount
          prefixWidth suffixWidth pairs pair side first)
        (fun first => candidateRowCircuit pair side first)).eval
          DeMorgan.interpretation state =
        fun first =>
          (candidateRowCircuit pair side first).eval
            DeMorgan.interpretation state 0 := by
    funext first
    exact Circuit.eval_parallelFin _ _ _ _ _ first
  rw [bankEval]
  simp only [candidateRowCircuit_eval]
  let first := requestSource (originalInputFromState state) pair 0
  have firstTrue :
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 first).eval state = true :=
    (stateSourceIndicatorExpression_eval_eq_true_iff
      pair 0 first state).2 rfl
  have firstUnique : forall candidate,
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 candidate).eval state = true -> candidate = first := by
    intro candidate candidateTrue
    exact ((stateSourceIndicatorExpression_eval_eq_true_iff
      pair 0 candidate state).1 candidateTrue).symm
  rw [DeMorgan.Expression.finOrValue_oneHot
    (prefixLast prefixWidth + 1) first
    (fun candidate =>
      (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 candidate).eval state)
    (fun candidate =>
      (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
        pair side candidate
          (requestSource (originalInputFromState state) pair 1)).eval
            DeMorgan.interpretation state 0)
    firstTrue firstUnique]
  rw [sharedFixedDecodedCircuit_eval]
  rfl

/-- Gate count of the shared decoder attached to one row-major output. -/
@[reducible] noncomputable def sharedDecoderOutputGateCount
    (prefixWidth suffixWidth pairs : Nat)
    (output : Fin (2 * pairs)) : Nat :=
  let pairSide := decoderPairSide output
  sharedDecodedGateCount prefixWidth suffixWidth pairs
    pairSide.1 pairSide.2

/-- Shared decoders for all row-major outputs. -/
noncomputable def sharedDecoderCircuit
    (prefixWidth suffixWidth pairs : Nat) :
    Circuit DeMorgan.signature
      (layerStateCount prefixWidth suffixWidth pairs)
      (Finset.univ.sum fun output : Fin (2 * pairs) =>
        sharedDecoderOutputGateCount prefixWidth suffixWidth pairs output)
      (2 * pairs) :=
  Circuit.parallelFin (2 * pairs)
    (sharedDecoderOutputGateCount prefixWidth suffixWidth pairs)
    (fun output =>
      let pairSide := decoderPairSide output
      sharedDecodedCircuit pairSide.1 pairSide.2)

@[simp] theorem sharedDecoderCircuit_eval
    (state : Fin (layerStateCount prefixWidth suffixWidth pairs) -> Bool)
    (output : Fin (2 * pairs)) :
    (sharedDecoderCircuit prefixWidth suffixWidth pairs).eval
        DeMorgan.interpretation state output =
      let pairSide := decoderPairSide output
      decodedStateValue state pairSide.1 pairSide.2 := by
  rw [sharedDecoderCircuit, Circuit.eval_parallelFin]
  dsimp only
  exact sharedDecodedCircuit_eval
    (prefixWidth := prefixWidth) (suffixWidth := suffixWidth)
    (decoderPairSide output).1 (decoderPairSide output).2 state

@[simp] theorem sharedDecoderCircuit_cost
    (prefixWidth suffixWidth pairs : Nat) :
    (sharedDecoderCircuit prefixWidth suffixWidth pairs).cost
        DeMorgan.standardCost =
      Finset.univ.sum fun output : Fin (2 * pairs) =>
        let pairSide := decoderPairSide output
        (sharedDecodedCircuit (prefixWidth := prefixWidth)
          (suffixWidth := suffixWidth) pairSide.1 pairSide.2).cost
            DeMorgan.standardCost := by
  rw [sharedDecoderCircuit, Circuit.cost_parallelFin]

end UhligCircuit
end MassProduction
end Algebraic
