/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Dependency

/-!
# Semantic influence paths in De Morgan programs

When changing one input changes a charged gate, some first charged reader of
that input also changes and feeds the gate through the contracted charged graph.
This is the semantic cut lemma used by XOR gate elimination.
-/

@[expose] public section

namespace Algebraic
namespace DeMorgan

/-- Evaluate an initial charged gate through its two named argument wires. -/
theorem InitialChargedGate.gateFunction_eq_binaryEval
    {program : Program signature n g}
    (initial : InitialChargedGate program)
    (input : Fin n → Bool) :
    program.gateFunction interpretation initial.gate input =
      initial.op.eval
        (program.trace interpretation input initial.left)
        (program.trace interpretation input initial.right) := by
  calc
    program.gateFunction interpretation initial.gate input =
        (program.lines initial.gate).eval interpretation input
          (program.eval interpretation input) :=
      (program.lines_eval interpretation input initial.gate).symm
    _ = (binaryLine initial.op initial.left initial.right).eval interpretation
          input (program.eval interpretation input) := by rw [initial.line_eq]
    _ = _ := by rw [binaryLine_eval]

/-- Equal contracted argument values force an initial charged gate to agree. -/
theorem InitialChargedGate.gateFunction_eq_of_origins_eq
    {program : Program signature n g}
    (initial : InitialChargedGate program)
    (left right : Fin n → Bool)
    (left_eq : (origins program initial.left).eval program left =
      (origins program initial.left).eval program right)
    (right_eq : (origins program initial.right).eval program left =
      (origins program initial.right).eval program right) :
    program.gateFunction interpretation initial.gate left =
      program.gateFunction interpretation initial.gate right := by
  calc
    program.gateFunction interpretation initial.gate left =
        initial.op.eval
          (program.trace interpretation left initial.left)
          (program.trace interpretation left initial.right) :=
      initial.gateFunction_eq_binaryEval left
    _ = initial.op.eval
          ((origins program initial.left).eval program left)
          ((origins program initial.right).eval program left) := by
      rw [origins_eval, origins_eval]
    _ = initial.op.eval
          ((origins program initial.left).eval program right)
          ((origins program initial.right).eval program right) := by
      rw [left_eq, right_eq]
    _ = initial.op.eval
          (program.trace interpretation right initial.left)
          (program.trace interpretation right initial.right) := by
      rw [origins_eval, origins_eval]
    _ = program.gateFunction interpretation initial.gate right :=
      (initial.gateFunction_eq_binaryEval right).symm

/--
A charged path that starts at a direct reader whose value changes between two
assignments.  The difference proof is stored only at the first gate; later gates
are connected structurally.
-/
inductive DifferingPath
    (program : Program signature n g)
    (selected : Fin n)
    (left right : Fin n → Bool) : Fin g → Prop
  | direct {gate} :
      ReadsInput program gate selected →
      program.gateFunction interpretation gate left ≠
        program.gateFunction interpretation gate right →
      DifferingPath program selected left right gate
  | step {source target} :
      DifferingPath program selected left right source →
      UsesGate program source target →
      DifferingPath program selected left right target

/-- Extend a differing path through an appended program gate. -/
theorem DifferingPath.castSucc
    {program : Program signature n g}
    {selected : Fin n}
    {left right : Fin n → Bool}
    {gate : Fin g}
    (path : DifferingPath program selected left right gate)
    (line : Line signature n g) :
    DifferingPath (program.gate line) selected left right gate.castSucc := by
  induction path with
  | direct reads different =>
      apply DifferingPath.direct (reads.castSucc line)
      simpa using different
  | step prior uses inductionHypothesis =>
      exact .step inductionHypothesis (uses.castSucc line)

/-- Expose the first differing direct reader on a differing path. -/
theorem DifferingPath.exists_first
    {program : Program signature n g}
    {selected : Fin n}
    {left right : Fin n → Bool}
    {endpoint : Fin g}
    (path : DifferingPath program selected left right endpoint) :
    ∃ first,
      ReadsInput program first selected ∧
      program.gateFunction interpretation first left ≠
        program.gateFunction interpretation first right ∧
      (first = endpoint ∨ ∃ next, UsesGate program first next) := by
  induction path with
  | direct reads different => exact ⟨_, reads, different, Or.inl rfl⟩
  | @step source target prior uses inductionHypothesis =>
      obtain ⟨first, reads, different, atSource | ⟨next, firstUses⟩⟩ :=
        inductionHypothesis
      · subst source
        exact ⟨first, reads, different, Or.inr ⟨target, uses⟩⟩
      · exact ⟨first, reads, different, Or.inr ⟨next, firstUses⟩⟩

/--
If two assignments differ only at `selected` and a charged gate distinguishes
them, there is a differing path from a direct reader of `selected` to that gate.
-/
theorem differingPath_of_gate_ne
    (program : Program signature n g)
    (selected : Fin n)
    (left right : Fin n → Bool)
    (agree : ∀ input, input ≠ selected → left input = right input) :
    ∀ gate,
      ChargedGate program gate →
      program.gateFunction interpretation gate left ≠
        program.gateFunction interpretation gate right →
      DifferingPath program selected left right gate := by
  induction program with
  | empty =>
      intro impossible
      exact Fin.elim0 impossible
  | @gate g program line inductionHypothesis =>
      intro target charged different
      revert charged different
      refine Fin.lastCases (fun charged different => ?_)
        (fun oldGate charged different => ?_) target
      · have argumentDifferent : ∃ argument,
            program.trace interpretation left (line.wires argument) ≠
              program.trace interpretation right (line.wires argument) := by
          by_contra noneDifferent
          push Not at noneDifferent
          apply different
          simp only [Program.gateFunction_gate_last]
          unfold Line.eval
          congr 1
          funext argument
          simpa only [Program.trace, Function.comp_apply] using
            noneDifferent argument
        obtain ⟨argument, argumentDifferent⟩ := argumentDifferent
        have originDifferent :
            (origins program (line.wires argument)).eval program left ≠
              (origins program (line.wires argument)).eval program right := by
          intro equal
          apply argumentDifferent
          calc
            program.trace interpretation left (line.wires argument) =
                (origins program (line.wires argument)).eval program left :=
              (origins_eval program left (line.wires argument)).symm
            _ = (origins program (line.wires argument)).eval program right := equal
            _ = program.trace interpretation right (line.wires argument) :=
              origins_eval program right (line.wires argument)
        have valid := origins_valid program (line.wires argument)
        generalize origin_eq : origins program (line.wires argument) = origin
          at originDifferent valid
        cases origin with
        | constant value =>
            simp only [ResidualValue.eval_constant] at originDifferent
            exact False.elim (originDifferent rfl)
        | wire negated originWire =>
            rcases valid with ⟨input, wire_eq⟩ |
              ⟨source, wire_eq, sourceCharged⟩
            · subst originWire
              have input_eq : input = selected := by
                by_contra input_ne
                apply originDifferent
                cases negated <;>
                  simpa using agree input input_ne
              subst input
              have lineCharged : binaryCost line.op = 1 := by
                simpa [ChargedGate] using charged
              exact DifferingPath.direct
                (ReadsInput.last lineCharged origin_eq) different
            · subst originWire
              have sourceDifferent :
                  program.gateFunction interpretation source left ≠
                    program.gateFunction interpretation source right := by
                intro equal
                apply originDifferent
                cases negated <;> simpa using equal
              have lineCharged : binaryCost line.op = 1 := by
                simpa [ChargedGate] using charged
              exact DifferingPath.step
                ((inductionHypothesis source sourceCharged sourceDifferent).castSucc line)
                (UsesGate.last lineCharged origin_eq)
      · have priorCharged : ChargedGate program oldGate := by
          simpa using charged
        have priorDifferent :
            program.gateFunction interpretation oldGate left ≠
              program.gateFunction interpretation oldGate right := by
          simpa using different
        exact (inductionHypothesis oldGate priorCharged priorDifferent).castSucc line

end DeMorgan
end Algebraic
