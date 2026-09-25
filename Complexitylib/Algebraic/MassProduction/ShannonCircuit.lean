/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Expression
public import Complexitylib.Algebraic.Semantics
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Native Shannon synthesis

This module gives an Algebraic-native version of the finite synthesis
construction used as the base case of the mass-production induction.  It
uses a shared circuit for all minterms, followed by a shared library of all
Boolean functions on a short address block.  No external circuit model and
no new type-class instances are used.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace ShannonSynthesis

open scoped BigOperators

/-- Canonical finite index of a Boolean vector. -/
noncomputable def bitVectorEquiv (width : Nat) :
    (Fin width -> Bool) ≃ Fin (2 ^ width) :=
  (Equiv.piCongrRight
      (fun _ : Fin width => finTwoEquiv.symm)).trans
    finFunctionFinEquiv

/-- Decode a canonical finite index back to its Boolean vector. -/
noncomputable def assignmentBits
    (width : Nat) (assignment : Fin (2 ^ width)) : Fin width -> Bool :=
  (bitVectorEquiv width).symm assignment

@[simp] theorem bitVectorEquiv_assignmentBits
    (assignment : Fin (2 ^ width)) :
    bitVectorEquiv width (assignmentBits width assignment) = assignment := by
  exact (bitVectorEquiv width).apply_symm_apply assignment

@[simp] theorem assignmentBits_bitVectorEquiv
    (input : Fin width -> Bool) :
    assignmentBits width (bitVectorEquiv width input) = input := by
  exact (bitVectorEquiv width).symm_apply_apply input

/-- A positive or negative occurrence of one input, according to the
expected Boolean value. -/
def matchingLiteral
    (index : Fin inputs) (expected : Bool) : DeMorgan.Expression inputs :=
  if expected then .input index else .not (.input index)

@[simp] theorem matchingLiteral_eval
    (index : Fin inputs)
    (expected : Bool)
    (input : Fin inputs -> Bool) :
    (matchingLiteral index expected).eval input =
      decide (input index = expected) := by
  cases actualEquation : input index <;> cases expected <;>
    simp [matchingLiteral, DeMorgan.Expression.eval, actualEquation]

theorem matchingLiteral_standardCost_le
    (index : Fin inputs) (expected : Bool) :
    (matchingLiteral index expected).standardCost <= 1 := by
  cases expected <;> simp [matchingLiteral,
    DeMorgan.Expression.standardCost]

/-- Index in the retained-state vector of a minterm from the previous
dimension. -/
def previousMintermInput
    (assignment : Fin (2 ^ width)) : Fin (2 ^ width + 1) :=
  Fin.castAdd 1 assignment

/-- Index in the retained-state vector of the newly prepended input bit. -/
def newHeadInput (width : Nat) : Fin (2 ^ width + 1) :=
  Fin.last (2 ^ width)

/-- The previous-dimension assignment required by a full assignment. -/
noncomputable def assignmentTailIndex
    (width : Nat) (assignment : Fin (2 ^ (width + 1))) : Fin (2 ^ width) :=
  bitVectorEquiv width (Fin.tail (assignmentBits (width + 1) assignment))

/-- One output of the layer which extends all `width`-bit minterms by one
new head bit. -/
noncomputable def extensionExpression
    (width : Nat) (assignment : Fin (2 ^ (width + 1))) :
    DeMorgan.Expression (2 ^ width + 1) :=
  .and (.input (previousMintermInput (assignmentTailIndex width assignment)))
    (matchingLiteral (newHeadInput width)
      (assignmentBits (width + 1) assignment 0))

/-- Program-gate count of one full minterm-extension layer. -/
@[reducible] noncomputable def extensionGateCount (width : Nat) : Nat :=
  ∑ assignment : Fin (2 ^ (width + 1)),
    (extensionExpression width assignment).gateCount

/-- Compute all extended minterms in parallel. -/
noncomputable def extensionCircuit (width : Nat) :
    Circuit DeMorgan.signature (2 ^ width + 1)
      (extensionGateCount width) (2 ^ (width + 1)) :=
  Circuit.parallelFin (2 ^ (width + 1))
    (fun assignment => (extensionExpression width assignment).gateCount)
    (fun assignment => (extensionExpression width assignment).circuit)

@[simp] theorem extensionCircuit_eval
    (state : Fin (2 ^ width + 1) -> Bool)
    (assignment : Fin (2 ^ (width + 1))) :
    (extensionCircuit width).eval DeMorgan.interpretation state assignment =
      (state (previousMintermInput (assignmentTailIndex width assignment)) &&
        decide (state (newHeadInput width) =
          assignmentBits (width + 1) assignment 0)) := by
  unfold extensionCircuit extensionGateCount
  rw [Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval]
  simp [extensionExpression, DeMorgan.Expression.eval]

theorem extensionCircuit_cost_le (width : Nat) :
    (extensionCircuit width).cost DeMorgan.standardCost <=
      2 * 2 ^ (width + 1) := by
  unfold extensionCircuit extensionGateCount
  rw [Circuit.cost_parallelFin]
  calc
    (∑ assignment : Fin (2 ^ (width + 1)),
        (extensionExpression width assignment).circuit.cost
          DeMorgan.standardCost) =
        ∑ assignment : Fin (2 ^ (width + 1)),
          (extensionExpression width assignment).standardCost := by
            apply Finset.sum_congr rfl
            intro assignment _membership
            rw [DeMorgan.Expression.circuit_cost]
    _ <= ∑ _assignment : Fin (2 ^ (width + 1)), 2 := by
      apply Finset.sum_le_sum
      intro assignment _membership
      simp only [extensionExpression, DeMorgan.Expression.standardCost]
      simpa [Nat.zero_add] using
        Nat.add_le_add_right (matchingLiteral_standardCost_le
          (newHeadInput width)
          (assignmentBits (width + 1) assignment 0)) 1
    _ = 2 * 2 ^ (width + 1) := by simp [Nat.mul_comm]

/-- Program-gate count of the shared all-minterms circuit. -/
@[reducible] noncomputable def mintermGateCount : Nat -> Nat
  | 0 => 1
  | width + 1 => mintermGateCount width + extensionGateCount width

/-- A shared circuit computing the indicator of every Boolean assignment.
The recursive layer prepends the new input bit, matching `Fin.cons`. -/
noncomputable def mintermCircuit : (width : Nat) ->
    Circuit DeMorgan.signature width (mintermGateCount width) (2 ^ width)
  | 0 => (DeMorgan.Expression.constant true).circuit
  | width + 1 =>
      let previous :=
        (mintermCircuit width).mapInputs (fun index => index.succ)
      let head :=
        (Circuit.id DeMorgan.signature (width + 1)).mapOutputs
          (fun _ : Fin 1 => (0 : Fin (width + 1)))
      let state := (previous.parallel head).castCounts rfl
        (Nat.add_zero _) rfl
      (extensionCircuit width).comp state

/-- Equality with a decoded assignment is exactly equality of the head bit
and equality of the encoded tail. -/
theorem assignment_eq_iff_head_tail
    (input : Fin (width + 1) -> Bool)
    (assignment : Fin (2 ^ (width + 1))) :
    bitVectorEquiv (width + 1) input = assignment ↔
      bitVectorEquiv width (Fin.tail input) =
          assignmentTailIndex width assignment ∧
        input 0 = assignmentBits (width + 1) assignment 0 := by
  rw [← (bitVectorEquiv (width + 1)).eq_symm_apply]
  constructor
  · intro inputEquality
    subst input
    exact ⟨rfl, rfl⟩
  · rintro ⟨tailEquality, headEquality⟩
    let decoded := assignmentBits (width + 1) assignment
    have tails : Fin.tail input = Fin.tail decoded := by
      apply (bitVectorEquiv width).injective
      simpa only [assignmentTailIndex, decoded]
        using tailEquality
    calc
      input = Fin.cons (input 0) (Fin.tail input) :=
        (Fin.cons_self_tail input).symm
      _ = Fin.cons (decoded 0) (Fin.tail decoded) := by
        rw [headEquality, tails]
      _ = decoded := Fin.cons_self_tail decoded

/-- The Boolean conjunction used by an extension layer is the indicator of
the represented full assignment. -/
theorem assignmentIndicator_extension
    (input : Fin (width + 1) -> Bool)
    (assignment : Fin (2 ^ (width + 1))) :
    (decide (bitVectorEquiv width (Fin.tail input) =
          assignmentTailIndex width assignment) &&
        decide (input 0 = assignmentBits (width + 1) assignment 0)) =
      decide (bitVectorEquiv (width + 1) input = assignment) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact (assignment_eq_iff_head_tail input assignment).symm

/-- Every output of the shared minterm circuit is the exact indicator of its
canonical Boolean assignment. -/
@[simp] theorem mintermCircuit_eval
    (width : Nat)
    (input : Fin width -> Bool)
    (assignment : Fin (2 ^ width)) :
    (mintermCircuit width).eval DeMorgan.interpretation input assignment =
      decide (bitVectorEquiv width input = assignment) := by
  induction width with
  | zero =>
      have inputUnique : input = fun index => Fin.elim0 index := by
        funext index
        exact Fin.elim0 index
      have assignmentUnique : assignment = 0 := by
        apply Fin.ext
        omega
      subst input
      subst assignment
      simp only [mintermCircuit]
      rw [DeMorgan.Expression.circuit_eval]
      change true = decide (bitVectorEquiv 0 (fun index => Fin.elim0 index) = 0)
      rw [show bitVectorEquiv 0 (fun index => Fin.elim0 index) = 0 by
        apply Fin.ext
        omega]
      rfl
  | succ width inductionHypothesis =>
      rw [mintermCircuit, Circuit.eval_comp, extensionCircuit_eval]
      simp only [Circuit.eval_castCounts, Fin.cast_refl, Function.comp_id,
        Circuit.eval_parallel, id_eq]
      rw [show previousMintermInput
            (assignmentTailIndex width assignment) =
          Fin.castAdd 1 (assignmentTailIndex width assignment) by rfl,
        Fin.append_left, Circuit.eval_mapInputs, inductionHypothesis]
      rw [show newHeadInput width = Fin.natAdd (2 ^ width) (0 : Fin 1) by
        apply Fin.ext
        simp [newHeadInput], Fin.append_right,
        Circuit.eval_mapOutputs, Function.comp_apply, Circuit.eval_id]
      exact assignmentIndicator_extension input assignment

/-- The complete shared minterm table costs at most four gates per Boolean
assignment. -/
theorem mintermCircuit_cost_le (width : Nat) :
    (mintermCircuit width).cost DeMorgan.standardCost <= 4 * 2 ^ width := by
  induction width with
  | zero =>
      simp only [mintermCircuit]
      rw [DeMorgan.Expression.circuit_cost]
      exact Nat.zero_le _
  | succ width inductionHypothesis =>
      rw [mintermCircuit, Circuit.cost_comp, Circuit.cost_castCounts,
        Circuit.cost_parallel, Circuit.cost_mapInputs,
        Circuit.cost_mapOutputs, Circuit.cost_id]
      have layerBound := extensionCircuit_cost_le width
      simp only [Nat.add_zero]
      have powerSucc : 2 ^ (width + 1) = 2 ^ width * 2 := by
        rw [Nat.pow_succ]
      omega

/-! ## The shared library of short-address Boolean functions -/

/-- One hardwired term in the truth-table disjunction for a short-address
function. -/
noncomputable def columnTerm
    (addressWidth : Nat)
    (pattern : Fin (2 ^ (2 ^ addressWidth)))
    (assignment : Fin (2 ^ addressWidth)) :
    DeMorgan.Expression (2 ^ addressWidth) :=
  if assignmentBits (2 ^ addressWidth) pattern assignment then
    .input assignment
  else
    .constant false

/-- The truth-table formula for one Boolean function of the address block,
evaluated on a one-hot vector of address minterms. -/
noncomputable def columnExpression
    (addressWidth : Nat)
    (pattern : Fin (2 ^ (2 ^ addressWidth))) :
    DeMorgan.Expression (2 ^ addressWidth) :=
  DeMorgan.Expression.finOr (2 ^ addressWidth)
    (columnTerm addressWidth pattern)

@[simp] theorem columnTerm_standardCost
    (addressWidth : Nat)
    (pattern : Fin (2 ^ (2 ^ addressWidth)))
    (assignment : Fin (2 ^ addressWidth)) :
    (columnTerm addressWidth pattern assignment).standardCost = 0 := by
  unfold columnTerm
  split <;> rfl

theorem columnExpression_standardCost
    (addressWidth : Nat)
    (pattern : Fin (2 ^ (2 ^ addressWidth))) :
    (columnExpression addressWidth pattern).standardCost =
      2 ^ addressWidth := by
  rw [columnExpression, DeMorgan.Expression.finOr_standardCost]
  simp

/-- A hardwired column formula reads the truth-table bit selected by a
one-hot minterm vector. -/
theorem columnExpression_eval_oneHot
    (addressWidth : Nat)
    (pattern : Fin (2 ^ (2 ^ addressWidth)))
    (flags : Fin (2 ^ addressWidth) -> Bool)
    (selected : Fin (2 ^ addressWidth))
    (selectedTrue : flags selected = true)
    (unique : forall assignment, flags assignment = true ->
      assignment = selected) :
    (columnExpression addressWidth pattern).eval flags =
      assignmentBits (2 ^ addressWidth) pattern selected := by
  rw [columnExpression, DeMorgan.Expression.finOr_eval]
  have termsEqual :
      (fun assignment =>
          (columnTerm addressWidth pattern assignment).eval flags) =
        (fun assignment => flags assignment &&
          assignmentBits (2 ^ addressWidth) pattern assignment) := by
    funext assignment
    unfold columnTerm
    cases bitEquation : assignmentBits (2 ^ addressWidth) pattern assignment <;>
      simp [DeMorgan.Expression.eval]
  rw [termsEqual]
  exact DeMorgan.Expression.finOrValue_oneHot
    (2 ^ addressWidth) selected flags
    (assignmentBits (2 ^ addressWidth) pattern)
    selectedTrue unique

/-- Program-gate count of the complete short-address function library. -/
@[reducible] noncomputable def libraryGateCount (addressWidth : Nat) : Nat :=
  ∑ pattern : Fin (2 ^ (2 ^ addressWidth)),
    (columnExpression addressWidth pattern).gateCount

/-- All Boolean functions of `addressWidth` inputs, sharing the same address
minterm vector. -/
noncomputable def libraryCircuit (addressWidth : Nat) :
    Circuit DeMorgan.signature (2 ^ addressWidth)
      (libraryGateCount addressWidth) (2 ^ (2 ^ addressWidth)) :=
  Circuit.parallelFin (2 ^ (2 ^ addressWidth))
    (fun pattern => (columnExpression addressWidth pattern).gateCount)
    (fun pattern => (columnExpression addressWidth pattern).circuit)

@[simp] theorem libraryCircuit_eval
    (addressWidth : Nat)
    (flags : Fin (2 ^ addressWidth) -> Bool)
    (pattern : Fin (2 ^ (2 ^ addressWidth))) :
    (libraryCircuit addressWidth).eval DeMorgan.interpretation flags pattern =
      (columnExpression addressWidth pattern).eval flags := by
  unfold libraryCircuit libraryGateCount
  rw [Circuit.eval_parallelFin, DeMorgan.Expression.circuit_eval]

theorem libraryCircuit_cost
    (addressWidth : Nat) :
    (libraryCircuit addressWidth).cost DeMorgan.standardCost =
      2 ^ (2 ^ addressWidth) * 2 ^ addressWidth := by
  unfold libraryCircuit libraryGateCount
  rw [Circuit.cost_parallelFin]
  calc
    (∑ pattern : Fin (2 ^ (2 ^ addressWidth)),
        (columnExpression addressWidth pattern).circuit.cost
          DeMorgan.standardCost) =
        ∑ pattern : Fin (2 ^ (2 ^ addressWidth)),
          (columnExpression addressWidth pattern).standardCost := by
            apply Finset.sum_congr rfl
            intro pattern _membership
            rw [DeMorgan.Expression.circuit_cost]
    _ = 2 ^ (2 ^ addressWidth) * 2 ^ addressWidth := by
      simp [columnExpression_standardCost]

/-- Composing the library after the shared minterm circuit evaluates the
canonical truth-table bit of the input address. -/
theorem library_after_minterms_eval
    (addressWidth : Nat)
    (input : Fin addressWidth -> Bool)
    (pattern : Fin (2 ^ (2 ^ addressWidth))) :
    (libraryCircuit addressWidth).eval DeMorgan.interpretation
        ((mintermCircuit addressWidth).eval DeMorgan.interpretation input)
        pattern =
      assignmentBits (2 ^ addressWidth) pattern
        (bitVectorEquiv addressWidth input) := by
  rw [libraryCircuit_eval]
  apply columnExpression_eval_oneHot addressWidth pattern
  · rw [mintermCircuit_eval]
    simp
  · intro assignment assignmentTrue
    rw [mintermCircuit_eval] at assignmentTrue
    simpa using (of_decide_eq_true assignmentTrue).symm

/-! ## Synthesis of an arbitrary split-input Boolean function -/

/-- The initial address block of a split input. -/
def addressInput
    (dataWidth : Nat)
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    Fin addressWidth -> Bool :=
  input ∘ Fin.castAdd dataWidth

/-- The final data block of a split input. -/
def dataInput
    (addressWidth : Nat)
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    Fin dataWidth -> Bool :=
  input ∘ Fin.natAdd addressWidth

theorem append_addressInput_dataInput
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    Fin.append (addressInput dataWidth input)
        (dataInput addressWidth input) = input := by
  funext index
  refine Fin.addCases (fun address => ?_) (fun data => ?_) index
  · simp [addressInput]
  · simp [dataInput]

/-- Gate count of the two shared minterm tables. -/
@[reducible] noncomputable def splitMintermGateCount
    (addressWidth dataWidth : Nat) : Nat :=
  mintermGateCount addressWidth + mintermGateCount dataWidth

/-- Compute all address and all data minterms in parallel. -/
noncomputable def splitMintermCircuit
    (addressWidth dataWidth : Nat) :
    Circuit DeMorgan.signature (addressWidth + dataWidth)
      (splitMintermGateCount addressWidth dataWidth)
      (2 ^ addressWidth + 2 ^ dataWidth) :=
  ((mintermCircuit addressWidth).mapInputs (Fin.castAdd dataWidth)).parallel
    ((mintermCircuit dataWidth).mapInputs (Fin.natAdd addressWidth))

@[simp] theorem splitMintermCircuit_eval
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    (splitMintermCircuit addressWidth dataWidth).eval
        DeMorgan.interpretation input =
      Fin.append
        ((mintermCircuit addressWidth).eval DeMorgan.interpretation
          (addressInput dataWidth input))
        ((mintermCircuit dataWidth).eval DeMorgan.interpretation
          (dataInput addressWidth input)) := by
  rw [splitMintermCircuit, Circuit.eval_parallel,
    Circuit.eval_mapInputs, Circuit.eval_mapInputs]
  rfl

/-- Gate count of the library stage, whose retained data minterms are free
wires. -/
@[reducible] noncomputable def libraryAndDataGateCount
    (addressWidth : Nat) : Nat :=
  libraryGateCount addressWidth

/-- Evaluate the complete address library while retaining every data
minterm. -/
noncomputable def libraryAndDataCircuit
    (addressWidth dataWidth : Nat) :
    Circuit DeMorgan.signature (2 ^ addressWidth + 2 ^ dataWidth)
      (libraryAndDataGateCount addressWidth)
      (2 ^ (2 ^ addressWidth) + 2 ^ dataWidth) :=
  (((libraryCircuit addressWidth).mapInputs
      (Fin.castAdd (2 ^ dataWidth))).parallel
    ((Circuit.id DeMorgan.signature
        (2 ^ addressWidth + 2 ^ dataWidth)).mapOutputs
      (Fin.natAdd (2 ^ addressWidth)))).castCounts rfl
        (Nat.add_zero _) rfl

@[simp] theorem libraryAndDataCircuit_eval
    (state : Fin (2 ^ addressWidth + 2 ^ dataWidth) -> Bool) :
    (libraryAndDataCircuit addressWidth dataWidth).eval
        DeMorgan.interpretation state =
      Fin.append
        ((libraryCircuit addressWidth).eval DeMorgan.interpretation
          (fun assignment => state (Fin.castAdd (2 ^ dataWidth) assignment)))
        (fun assignment =>
          state (Fin.natAdd (2 ^ addressWidth) assignment)) := by
  rw [libraryAndDataCircuit, Circuit.eval_castCounts]
  simp only [Fin.cast_refl, Function.comp_id, Circuit.eval_parallel,
    Circuit.eval_mapInputs, Circuit.eval_mapOutputs, Circuit.eval_id,
    id_eq]
  rfl

/-- The address truth-table column required when the data block has one
fixed assignment. -/
noncomputable def columnPattern
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (dataAssignment : Fin (2 ^ dataWidth)) :
    Fin (2 ^ (2 ^ addressWidth)) :=
  bitVectorEquiv (2 ^ addressWidth) fun addressAssignment =>
    function (Fin.append
      (assignmentBits addressWidth addressAssignment)
      (assignmentBits dataWidth dataAssignment))

@[simp] theorem assignmentBits_columnPattern
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (dataAssignment : Fin (2 ^ dataWidth))
    (addressAssignment : Fin (2 ^ addressWidth)) :
    assignmentBits (2 ^ addressWidth)
        (columnPattern function dataAssignment) addressAssignment =
      function (Fin.append
        (assignmentBits addressWidth addressAssignment)
        (assignmentBits dataWidth dataAssignment)) := by
  unfold columnPattern
  rw [assignmentBits_bitVectorEquiv]

/-- Input coordinate of a precomputed address-column value. -/
def columnInput
    (dataWidth : Nat)
    (pattern : Fin (2 ^ (2 ^ addressWidth))) :
    Fin (2 ^ (2 ^ addressWidth) + 2 ^ dataWidth) :=
  Fin.castAdd (2 ^ dataWidth) pattern

/-- Input coordinate of a retained data minterm. -/
def dataMintermInput
    (addressWidth : Nat)
    (assignment : Fin (2 ^ dataWidth)) :
    Fin (2 ^ (2 ^ addressWidth) + 2 ^ dataWidth) :=
  Fin.natAdd (2 ^ (2 ^ addressWidth)) assignment

/-- Combine one retained data minterm with the corresponding hardwired
address-function column. -/
noncomputable def rowExpression
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (dataAssignment : Fin (2 ^ dataWidth)) :
    DeMorgan.Expression (2 ^ (2 ^ addressWidth) + 2 ^ dataWidth) :=
  .and (.input (dataMintermInput addressWidth dataAssignment))
    (.input (columnInput dataWidth (columnPattern function dataAssignment)))

/-- OR the row terms to obtain the synthesized function. -/
noncomputable def synthesisExpression
    (function : ScalarFunction Bool (addressWidth + dataWidth)) :
    DeMorgan.Expression (2 ^ (2 ^ addressWidth) + 2 ^ dataWidth) :=
  DeMorgan.Expression.finOr (2 ^ dataWidth) (rowExpression function)

theorem synthesisExpression_standardCost
    (function : ScalarFunction Bool (addressWidth + dataWidth)) :
    (synthesisExpression function).standardCost = 2 * 2 ^ dataWidth := by
  rw [synthesisExpression, DeMorgan.Expression.finOr_standardCost]
  simp [rowExpression, DeMorgan.Expression.standardCost]
  omega

/-- Program-gate count of the complete native Shannon circuit. -/
@[reducible] noncomputable def synthesisGateCount
    (function : ScalarFunction Bool (addressWidth + dataWidth)) : Nat :=
  splitMintermGateCount addressWidth dataWidth +
    libraryAndDataGateCount addressWidth +
      (synthesisExpression function).gateCount

/-- Algebraic-native Shannon synthesis with a caller-selected address/data
split. -/
noncomputable def circuit
    (function : ScalarFunction Bool (addressWidth + dataWidth)) :
    Circuit DeMorgan.signature (addressWidth + dataWidth)
      (synthesisGateCount function) 1 :=
  (synthesisExpression function).circuit.comp
    ((libraryAndDataCircuit addressWidth dataWidth).comp
      (splitMintermCircuit addressWidth dataWidth))

/-- Intermediate values after both minterm tables and the address-function
library have been evaluated. -/
noncomputable def libraryState
    (addressWidth dataWidth : Nat)
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    Fin (2 ^ (2 ^ addressWidth) + 2 ^ dataWidth) -> Bool :=
  (libraryAndDataCircuit addressWidth dataWidth).eval
    DeMorgan.interpretation
    ((splitMintermCircuit addressWidth dataWidth).eval
      DeMorgan.interpretation input)

@[simp] theorem libraryState_column
    (input : Fin (addressWidth + dataWidth) -> Bool)
    (pattern : Fin (2 ^ (2 ^ addressWidth))) :
    libraryState addressWidth dataWidth input
        (columnInput dataWidth pattern) =
      assignmentBits (2 ^ addressWidth) pattern
        (bitVectorEquiv addressWidth (addressInput dataWidth input)) := by
  rw [libraryState, libraryAndDataCircuit_eval]
  unfold columnInput
  rw [Fin.append_left, splitMintermCircuit_eval]
  simp only [Fin.append_left]
  exact library_after_minterms_eval addressWidth
    (addressInput dataWidth input) pattern

@[simp] theorem libraryState_dataMinterm
    (input : Fin (addressWidth + dataWidth) -> Bool)
    (assignment : Fin (2 ^ dataWidth)) :
    libraryState addressWidth dataWidth input
        (dataMintermInput addressWidth assignment) =
      decide (bitVectorEquiv dataWidth (dataInput addressWidth input) =
        assignment) := by
  rw [libraryState, libraryAndDataCircuit_eval]
  unfold dataMintermInput
  rw [Fin.append_right, splitMintermCircuit_eval]
  simp only [Fin.append_right]
  exact mintermCircuit_eval dataWidth (dataInput addressWidth input)
    assignment

@[simp] theorem rowExpression_eval_libraryState
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (input : Fin (addressWidth + dataWidth) -> Bool)
    (dataAssignment : Fin (2 ^ dataWidth)) :
    (rowExpression function dataAssignment).eval
        (libraryState addressWidth dataWidth input) =
      (decide (bitVectorEquiv dataWidth (dataInput addressWidth input) =
          dataAssignment) &&
        function (Fin.append (addressInput dataWidth input)
          (assignmentBits dataWidth dataAssignment))) := by
  unfold rowExpression
  simp only [DeMorgan.Expression.eval, libraryState_dataMinterm,
    libraryState_column, assignmentBits_columnPattern,
    assignmentBits_bitVectorEquiv]

/-- The native Shannon circuit computes the supplied Boolean function. -/
theorem circuit_eval
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    (circuit function).eval DeMorgan.interpretation input 0 =
      function input := by
  rw [circuit, Circuit.eval_comp, Circuit.eval_comp,
    DeMorgan.Expression.circuit_eval]
  change (synthesisExpression function).eval
      (libraryState addressWidth dataWidth input) = function input
  rw [synthesisExpression, DeMorgan.Expression.finOr_eval]
  have rowValues :
      (fun dataAssignment =>
          (rowExpression function dataAssignment).eval
            (libraryState addressWidth dataWidth input)) =
        (fun dataAssignment =>
          decide (bitVectorEquiv dataWidth (dataInput addressWidth input) =
              dataAssignment) &&
            function (Fin.append (addressInput dataWidth input)
              (assignmentBits dataWidth dataAssignment))) := by
    funext dataAssignment
    exact rowExpression_eval_libraryState function input dataAssignment
  rw [rowValues]
  let selected := bitVectorEquiv dataWidth (dataInput addressWidth input)
  rw [DeMorgan.Expression.finOrValue_oneHot (2 ^ dataWidth) selected
    (fun dataAssignment => decide (selected = dataAssignment))
    (fun dataAssignment =>
      function (Fin.append (addressInput dataWidth input)
        (assignmentBits dataWidth dataAssignment)))]
  · rw [show assignmentBits dataWidth selected =
        dataInput addressWidth input by
      exact assignmentBits_bitVectorEquiv (dataInput addressWidth input)]
    rw [append_addressInput_dataInput]
  · simp
  · intro dataAssignment assignmentTrue
    exact (of_decide_eq_true assignmentTrue).symm

/-- Explicit cost ledger for the split synthesis construction. -/
@[reducible] def costBound (addressWidth dataWidth : Nat) : Nat :=
  4 * 2 ^ addressWidth + 4 * 2 ^ dataWidth +
    2 ^ (2 ^ addressWidth) * 2 ^ addressWidth +
      2 * 2 ^ dataWidth

theorem circuit_cost_le
    (function : ScalarFunction Bool (addressWidth + dataWidth)) :
    (circuit function).cost DeMorgan.standardCost <=
      costBound addressWidth dataWidth := by
  rw [circuit, Circuit.cost_comp, Circuit.cost_comp,
    splitMintermCircuit, Circuit.cost_parallel,
    Circuit.cost_mapInputs, Circuit.cost_mapInputs,
    libraryAndDataCircuit, Circuit.cost_castCounts,
    Circuit.cost_parallel, Circuit.cost_mapInputs,
    Circuit.cost_mapOutputs, Circuit.cost_id,
    libraryCircuit_cost, DeMorgan.Expression.circuit_cost,
    synthesisExpression_standardCost]
  unfold costBound
  have addressBound := mintermCircuit_cost_le addressWidth
  have dataBound := mintermCircuit_cost_le dataWidth
  omega

end ShannonSynthesis
end MassProduction
end Algebraic
