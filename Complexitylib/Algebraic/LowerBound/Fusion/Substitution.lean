/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Framework
public import Complexitylib.Algebraic.Substitution

/-!
# Fusion atoms under circuit substitution

Atom extraction is compatible with causal program instantiation: the ambient
atoms occur first, followed by the source atoms evaluated under the values of
the supplied ambient wires.  This is the semantic gate-list analogue of
`Program.instantiate_trace` and is the reusable bridge for proving local
Fusion restrictions after circuit compilation.
-/

@[expose] public section

namespace Algebraic
namespace Fusion

/-- Instantiating a source program appends exactly its semantic atoms after
the ambient atoms, with source inputs interpreted by the supplied wires. -/
theorem programAtoms_instantiate
    (source : Program σ n g)
    (ambient : Program σ n' h)
    (inputWires : Fin n → Wire n' h)
    (interpretation : Interpretation σ U)
    (input : Fin n' → U) :
    programAtoms interpretation input
        (source.instantiate ambient inputWires) =
      programAtoms interpretation input ambient ++
        programAtoms interpretation
          (ambient.trace interpretation input ∘ inputWires) source := by
  induction source with
  | empty =>
      simp [Program.instantiate]
  | @gate g source line inductionHypothesis =>
      have lastAtom :
          lineAtom
              (line.mapWires (Wire.Substitution.append inputWires g))
              (source.instantiate ambient inputWires) interpretation input =
            lineAtom line source interpretation
              (ambient.trace interpretation input ∘ inputWires) := by
        cases line with
        | mk op wires =>
            simp only [lineAtom, Line.mapWires]
            congr 1
            funext argument
            exact source.instantiate_trace ambient inputWires interpretation
              input (wires argument)
      simp [Program.instantiate, programAtoms_gate, inductionHypothesis,
        lastAtom, List.append_assoc]

/-- Continuing a program by another appends exactly the continuation's
semantic atoms, with its inputs interpreted by the feeding wires. -/
theorem programAtoms_append
    (ambient : Program σ n' h)
    (feed : Fin n → Wire n' h)
    (continuation : Program σ n g)
    (interpretation : Interpretation σ U)
    (input : Fin n' → U) :
    programAtoms interpretation input (ambient.append feed continuation) =
      programAtoms interpretation input ambient ++
        programAtoms interpretation
          (ambient.trace interpretation input ∘ feed) continuation := by
  induction continuation with
  | empty => simp [Cslib.Circuits.Program.append]
  | @gate g continuation line inductionHypothesis =>
      have lastAtom :
          lineAtom (line.mapWires (Cslib.Circuits.Program.appendWire feed))
              (ambient.append feed continuation) interpretation input =
            lineAtom line continuation interpretation
              (ambient.trace interpretation input ∘ feed) := by
        cases line with
        | mk op wires =>
            simp only [lineAtom, Line.mapWires]
            congr 1
            funext argument
            exact Cslib.Circuits.Program.trace_append_appendWire ambient feed interpretation
              input continuation (wires argument)
      simp [Cslib.Circuits.Program.append, programAtoms_gate, inductionHypothesis,
        lastAtom, List.append_assoc]

/-- Sequential composition concatenates the inner atoms with the outer atoms
evaluated on the inner circuit's outputs. -/
theorem circuitAtoms_comp
    (outer : Circuit σ m k)
    (inner : Circuit σ n m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    circuitAtoms (outer.comp inner) interpretation input =
      circuitAtoms inner interpretation input ++
        circuitAtoms outer interpretation
          (inner.eval interpretation input) :=
  programAtoms_append inner.program inner.outputs outer.program
    interpretation input

end Fusion
end Algebraic
