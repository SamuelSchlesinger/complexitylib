/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.BooleanDependency.Encoding.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Defs
public import Complexitylib.Mathlib.NatBits
public import Mathlib.Order.Sigma
public import Mathlib.Order.Sum.Order

/-!
# Bit encoding of explicit NW reconstruction programs -- definitions

Every stored Boolean in a reconstruction program is represented by one member
of a finite linearly ordered payload-index type: predecessor-table entries,
outside-seed bits, later-tail bits, and finally the candidate bit. Encoding the
associated Boolean function therefore produces one flat, canonically ordered
bit string. The polarity and coordinate remain explicit codec metadata.
-/


@[expose] public section

namespace Complexity

namespace NWDesign

/-- Lexicographically ordered indices of all stored predecessor-table
entries. -/
abbrev ReconstructionPredecessorPayloadIndex
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :=
  Lex (Σ previous : Finset.Iio current,
    BooleanDependency.OrderedAssignment
      (design.challengeOverlap current previous.1))

/-- Canonically ordered indices of every Boolean in a reconstruction payload. -/
abbrev ReconstructionPayloadIndex
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :=
  ReconstructionPredecessorPayloadIndex design current ⊕ₗ
    ((design.outsideCoordinates current) ⊕ₗ
      ((laterCoordinates current) ⊕ₗ Fin 1))

/-- Inject one predecessor-table entry into the total payload index. -/
def predecessorPayloadIndex
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (previous : Finset.Iio current)
    (assignment : design.challengeOverlap current previous.1 → Bool) :
    ReconstructionPayloadIndex design current :=
  toLex <| Sum.inl <| toLex <| ⟨previous, ⟨assignment⟩⟩

/-- Inject one outside-seed coordinate into the total payload index. -/
def outsidePayloadIndex
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength)
    (coordinate : design.outsideCoordinates current) :
    ReconstructionPayloadIndex design current :=
  toLex <| Sum.inr <| toLex <| Sum.inl coordinate

/-- Inject one later-tail coordinate into the total payload index. -/
def laterPayloadIndex
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (coordinate : laterCoordinates current) :
    ReconstructionPayloadIndex design current :=
  toLex <| Sum.inr <| toLex <| Sum.inr <| toLex <| Sum.inl coordinate

/-- Index of the final candidate bit in the total payload. -/
def candidatePayloadIndex
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) : ReconstructionPayloadIndex design current :=
  toLex <| Sum.inr <| toLex <| Sum.inr <| toLex <| Sum.inr 0

namespace ReconstructionProgram

/-- Regard the explicit program fields as one Boolean function on the total
payload-index type. -/
def booleanPayload
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    ReconstructionPayloadIndex design program.current → Bool :=
  fun index =>
    match ofLex index with
    | Sum.inl predecessor =>
        let entry := ofLex predecessor
        program.predecessor entry.1 entry.2.toFun
    | Sum.inr remainder =>
        match ofLex remainder with
        | Sum.inl coordinate => program.outside coordinate
        | Sum.inr tail =>
            match ofLex tail with
            | Sum.inl coordinate => program.later coordinate
            | Sum.inr _ => program.candidate

/-- Canonical flat encoding of all Boolean payload fields. The program's
polarity and coordinate are not included. -/
def encodeBooleanPayload
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) : List Bool :=
  BooleanDependency.encodeOrderedFunction program.booleanPayload

/-- Complete program-specific encoding: polarity, fixed-width hybrid
coordinate, and the flat Boolean reconstruction payload. The ambient design
parameters remain external to the codec. -/
def encode
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) : List Bool :=
  program.complement :: program.current.toBits ++ program.encodeBooleanPayload

end ReconstructionProgram

/-- Decode a flat Boolean payload using an externally supplied polarity and
hybrid coordinate. -/
def decodeReconstructionBooleanPayload?
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (complement : Bool) (current : Fin outputLength) (bits : List Bool) :
    Option design.ReconstructionProgram :=
  match BooleanDependency.decodeOrderedFunction?
      (index := ReconstructionPayloadIndex design current) bits with
  | none => none
  | some payload =>
      some {
        complement := complement
        current := current
        predecessor := fun previous assignment =>
          payload (predecessorPayloadIndex design current previous assignment)
        outside := fun coordinate =>
          payload (outsidePayloadIndex design current coordinate)
        later := fun coordinate =>
          payload (laterPayloadIndex design current coordinate)
        candidate := payload (candidatePayloadIndex design current)
      }

/-- Decode a complete reconstruction program relative only to its ambient
design parameters. -/
def decodeReconstructionProgram?
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) (bits : List Bool) :
    Option design.ReconstructionProgram :=
  match bits with
  | [] => none
  | complement :: body =>
      let coordinateWidth := Fin.bitWidth outputLength
      match Fin.fromBits? outputLength (body.take coordinateWidth) with
      | none => none
      | some current =>
          decodeReconstructionBooleanPayload? design complement current
            (body.drop coordinateWidth)

end NWDesign

end Complexity
