/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Cost
public import Mathlib.Data.Finset.Card

/-!
# Local approximation schemes for shared circuits

A local approximation scheme supplies an approximate interpretation of every
gate and a finite exception set on which that local replacement may be
incorrect.  Folding the scheme over a straight-line program unions the local
exception sets.  Consequently each gate is charged once, even when its value
fans out to many later gates.

This is deliberately independent of polynomials, probability, and any
particular circuit basis.  The monotone CLIQUE application uses bounded-width
DNF approximators and two different sample families with the same approximate
interpretation.
-/

@[expose] public section

namespace Algebraic
namespace Approximation

/-- A locally sound approximate interpretation on a finite sample space. -/
structure Scheme
    (exactInterpretation : Interpretation σ U)
    (approxInterpretation : Interpretation σ A)
    (decode : A → Sample → U)
    (exactInput : Sample → Fin n → U)
    (approxInput : Fin n → A)
    [DecidableEq Sample] where
  /-- One-sided correctness relation from exact to approximate values. -/
  relation : U → U → Prop
  /-- Local and inherited correctness compose. -/
  relation_trans : ∀ {left middle right},
    relation left middle → relation middle right → relation left right
  /-- Exact operations preserve the correctness relation pointwise. -/
  interpretation_preserves : ∀ op exactArguments approxArguments,
    (∀ input, relation (exactArguments input) (approxArguments input)) →
      relation (exactInterpretation op exactArguments)
        (exactInterpretation op approxArguments)
  /-- Maximum number of fresh exceptions charged to an operation. -/
  errorCost : OperationCost σ
  /-- Fresh exceptions for one concrete approximate gate application. -/
  exceptions : ∀ op : σ.Op,
    (Fin (σ.Arity op) → A) → Finset Sample
  /-- Approximate inputs are exact on every sample. -/
  input_correct : ∀ sample input,
    relation (exactInput sample input) (decode (approxInput input) sample)
  /-- A local gate is exact away from its fresh exceptions. -/
  gate_correct : ∀ op arguments sample,
    sample ∉ exceptions op arguments →
      relation
        (exactInterpretation op (fun input => decode (arguments input) sample))
        (decode (approxInterpretation op arguments) sample)
  /-- Each fresh exception set respects its advertised operation cost. -/
  exceptions_card_le : ∀ op arguments,
    (exceptions op arguments).card ≤ errorCost op

namespace Scheme

variable
    {exactInterpretation : Interpretation σ U}
    {approxInterpretation : Interpretation σ A}
    {decode : A → Sample → U}
    {exactInput : Sample → Fin n → U}
    {approxInput : Fin n → A}
    [DecidableEq Sample]

/-- The approximate argument tuple supplied to the next line. -/
def lineArguments
    (program : Program σ n g)
    (line : Line σ n g)
    (approxInterpretation : Interpretation σ A)
    (approxInput : Fin n → A) :
    Fin (σ.Arity line.op) → A :=
  program.trace approxInterpretation approxInput ∘ line.wires

/-- The union of all local exception sets created by a program. -/
def programExceptions
    (scheme : Scheme exactInterpretation approxInterpretation decode
      exactInput approxInput) :
    (program : Program σ n g) → Finset Sample
  | .empty => ∅
  | .gate prior line =>
      programExceptions scheme prior ∪
        scheme.exceptions line.op
          (lineArguments prior line approxInterpretation approxInput)

@[simp] theorem programExceptions_empty
    (scheme : Scheme exactInterpretation approxInterpretation decode
      exactInput approxInput) :
    scheme.programExceptions (Program.empty : Program σ n 0) = ∅ := rfl

@[simp] theorem programExceptions_gate
    (scheme : Scheme exactInterpretation approxInterpretation decode
      exactInput approxInput)
    (program : Program σ n g)
    (line : Line σ n g) :
    scheme.programExceptions (program.gate line) =
      scheme.programExceptions program ∪
        scheme.exceptions line.op
          (lineArguments program line approxInterpretation approxInput) := rfl

/-- The global exception set is bounded by the sum of local gate budgets. -/
theorem programExceptions_card_le_cost
    (scheme : Scheme exactInterpretation approxInterpretation decode
      exactInput approxInput)
    (program : Program σ n g) :
    (scheme.programExceptions program).card ≤
      program.cost scheme.errorCost := by
  induction program with
  | empty => simp
  | @gate g prior line inductionHypothesis =>
      exact (Finset.card_union_le _ _).trans <|
        Nat.add_le_add inductionHypothesis
          (scheme.exceptions_card_le line.op
            (lineArguments prior line approxInterpretation approxInput))

/-- Every approximate wire agrees with its exact sampled value away from the
single global exception set. -/
theorem program_correct
    (scheme : Scheme exactInterpretation approxInterpretation decode
      exactInput approxInput)
    (program : Program σ n g)
    (sample : Sample)
    (fresh : sample ∉ scheme.programExceptions program) :
    ∀ wire : Wire n g,
      scheme.relation
        (program.trace exactInterpretation (exactInput sample) wire)
        (decode (program.trace approxInterpretation approxInput wire) sample) := by
  induction program with
  | empty =>
      intro wire
      refine Fin.addCases (fun input => ?_) (fun gate => Fin.elim0 gate) wire
      rw [Program.trace_input, Program.trace_input]
      exact scheme.input_correct sample input
  | @gate g prior line inductionHypothesis =>
      simp only [programExceptions_gate, Finset.mem_union, not_or] at fresh
      intro wire
      refine Fin.lastCases ?_ (fun priorWire => ?_) wire
      · have approxLast := Program.trace_gate_last prior line
            approxInterpretation approxInput
        have exactLast := Program.trace_gate_last prior line
            exactInterpretation (exactInput sample)
        change scheme.relation
          ((prior.gate line).trace exactInterpretation (exactInput sample)
            (Fin.last (n + g)))
          (decode
            ((prior.gate line).trace approxInterpretation approxInput
              (Fin.last (n + g))) sample)
        rw [approxLast, exactLast]
        let arguments :=
          lineArguments prior line approxInterpretation approxInput
        have localCorrect := scheme.gate_correct line.op arguments sample fresh.2
        apply scheme.relation_trans
          (scheme.interpretation_preserves line.op
            (fun input =>
              prior.trace exactInterpretation (exactInput sample)
                (line.wires input))
            (fun input => decode (arguments input) sample) (fun input => ?_))
          localCorrect
        exact inductionHypothesis fresh.1 (line.wires input)
      · simpa only [Program.trace_gate_castSucc] using
          inductionHypothesis fresh.1 priorWire

/-- A circuit output is correct on every sample outside the union of its
local exceptions. -/
theorem circuit_correct
    (scheme : Scheme exactInterpretation approxInterpretation decode
      exactInput approxInput)
    (circuit : Circuit σ n g m)
    (output : Fin m)
    (sample : Sample)
    (fresh : sample ∉ scheme.programExceptions circuit.program) :
    scheme.relation
      (circuit.eval exactInterpretation (exactInput sample) output)
      (decode (circuit.eval approxInterpretation approxInput output) sample) := by
  exact scheme.program_correct circuit.program sample fresh
    (circuit.outputs output)

/-- Samples on which one approximate value violates a one-sided correctness
relation with a target. -/
def failures
    [Fintype Sample]
    (relation : U → U → Prop)
    [DecidableRel relation]
    (decode : A → Sample → U)
    (value : A)
    (target : Sample → U) : Finset Sample :=
  Finset.univ.filter fun sample =>
    ¬ relation (target sample) (decode value sample)

omit [DecidableEq Sample] in
@[simp] theorem mem_failures
    [Fintype Sample]
    (relation : U → U → Prop)
    [DecidableRel relation]
    (decode : A → Sample → U)
    (value : A)
    (target : Sample → U)
    (sample : Sample) :
    sample ∈ failures relation decode value target ↔
      ¬ relation (target sample) (decode value sample) := by
  simp [failures]

/-- The failure set of a correctly computed target is contained in the
scheme's global exception set. -/
theorem failures_subset_programExceptions
    [Fintype Sample]
    (scheme : Scheme exactInterpretation approxInterpretation decode
      exactInput approxInput)
    [DecidableRel scheme.relation]
    (circuit : Circuit σ n g 1)
    (target : Sample → U)
    (computes : ∀ sample,
      circuit.eval exactInterpretation (exactInput sample) 0 = target sample) :
    failures scheme.relation decode
        (circuit.eval approxInterpretation approxInput 0) target ⊆
      scheme.programExceptions circuit.program := by
  intro sample disagreement
  by_contra fresh
  rw [mem_failures] at disagreement
  apply disagreement
  rw [← computes sample]
  exact scheme.circuit_correct circuit 0 sample fresh

/-- Total sampled failure is at most the sum of local approximation
errors, with sharing charged once. -/
theorem failures_card_le_cost
    [Fintype Sample]
    (scheme : Scheme exactInterpretation approxInterpretation decode
      exactInput approxInput)
    [DecidableRel scheme.relation]
    (circuit : Circuit σ n g 1)
    (target : Sample → U)
    (computes : ∀ sample,
      circuit.eval exactInterpretation (exactInput sample) 0 = target sample) :
    (failures scheme.relation decode
      (circuit.eval approxInterpretation approxInput 0) target).card ≤
        circuit.cost scheme.errorCost := by
  exact (Finset.card_le_card
    (scheme.failures_subset_programExceptions circuit target computes)).trans
      (scheme.programExceptions_card_le_cost circuit.program)

end Scheme

end Approximation
end Algebraic
