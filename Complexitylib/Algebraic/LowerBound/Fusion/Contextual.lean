/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Translation.Contextual
public import Complexitylib.Algebraic.LowerBound.Fusion.Substitution

/-!
# Local Fusion properties under contextual compilation

If every atom in every contextual operation gadget satisfies a semantic
property, then every atom in the compiled target circuit satisfies it.  The
proof combines atom extraction under instantiation with contextual trace
preservation, so gadget inputs are rewritten to the shared context followed
by the actual source-operation arguments.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace ContextualTranslation

/-- A local target-atom property verified for every contextual gadget is
preserved by compilation of an entire source program. -/
theorem forall_atoms_compileProgram
    (translation : Algebraic.ContextualTranslation σ τ q)
    (source : Program σ n g)
    (interpretation : Interpretation τ U)
    (context : Fin q → U)
    (input : Fin n → U)
    (property : Atom τ U → Prop)
    (gadget : ∀ (operation : σ.Op)
      (arguments : Fin (σ.Arity operation) → U)
      (atom : Atom τ U),
      atom ∈ circuitAtoms (translation.operation operation) interpretation
        (Algebraic.ContextualTranslation.appendInputs context arguments) →
      property atom)
    (atom : Atom τ U)
    (present : atom ∈
      programAtoms interpretation
        (Algebraic.ContextualTranslation.appendInputs context input)
        (translation.compileProgram source).program) :
    property atom := by
  induction source with
  | empty =>
      simp [Algebraic.ContextualTranslation.compileProgram] at present
  | @gate g source line inductionHypothesis =>
      let prior := translation.compileProgram source
      let implementation := translation.operation line.op
      let implementationInputs :
          Fin (q + σ.Arity line.op) → Wire (q + n) prior.gateCount :=
        Fin.addCases
          (fun contextInput => Wire.input (Fin.castAdd n contextInput))
          (fun argument => prior.wires (line.wires argument))
      change atom ∈ programAtoms interpretation
        (Algebraic.ContextualTranslation.appendInputs context input)
        (implementation.program.instantiate prior.program
          implementationInputs) at present
      rw [programAtoms_instantiate] at present
      rcases List.mem_append.mp present with inPrior | inImplementation
      · exact inductionHypothesis inPrior
      · have implementationInput_eq :
            prior.program.trace interpretation
                  (Algebraic.ContextualTranslation.appendInputs context input) ∘
                implementationInputs =
              Algebraic.ContextualTranslation.appendInputs context
                (source.trace (translation.pull interpretation context) input ∘
                  line.wires) := by
          funext supplied
          refine Fin.addCases (fun contextInput => ?_)
            (fun argument => ?_) supplied
          · simp [implementationInputs,
              Algebraic.ContextualTranslation.appendInputs]
          · simpa [implementationInputs,
              Algebraic.ContextualTranslation.appendInputs,
              Function.comp_apply] using
                translation.compileProgram_trace source interpretation context
                  input (line.wires argument)
        rw [implementationInput_eq] at inImplementation
        apply gadget line.op
          (source.trace (translation.pull interpretation context) input ∘
            line.wires) atom
        simpa [circuitAtoms] using inImplementation

/-- Circuit-level form of `forall_atoms_compileProgram`. -/
theorem forall_atoms_compile
    (translation : Algebraic.ContextualTranslation σ τ q)
    (circuit : Circuit σ n m)
    (interpretation : Interpretation τ U)
    (context : Fin q → U)
    (input : Fin n → U)
    (property : Atom τ U → Prop)
    (gadget : ∀ (operation : σ.Op)
      (arguments : Fin (σ.Arity operation) → U)
      (atom : Atom τ U),
      atom ∈ circuitAtoms (translation.operation operation) interpretation
        (Algebraic.ContextualTranslation.appendInputs context arguments) →
      property atom)
    (atom : Atom τ U)
    (present : atom ∈ circuitAtoms (translation.compile circuit)
      interpretation
        (Algebraic.ContextualTranslation.appendInputs context input)) :
    property atom := by
  exact forall_atoms_compileProgram translation circuit.program interpretation
    context input property gadget atom present

end ContextualTranslation
end Fusion
end Algebraic
