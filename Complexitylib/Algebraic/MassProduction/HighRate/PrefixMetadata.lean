/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.HighRate.BooleanRecovery
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchLookupBound
public import Complexitylib.Algebraic.MassProduction.Nonuniform.RecordArray
public import Complexitylib.Algebraic.MassProduction.RuntimeRequestData

/-!
# Shared prefix lookup for high-rate request metadata

One offline table maps each original source prefix to its code-copy,
information-point, and basis-bit coordinates. The whole batch shares this
table, including repeated prefixes. Suffixes are retained by free wiring.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate.PrefixMetadata

open Nonuniform RuntimePipeline

set_option backward.isDefEq.respectTransparency false

/-- Information-point bits followed by copy and basis-bit indices. -/
abbrev metadataWidth (dimension width copyBits selectorBits : Nat) : Nat := dimension * width + (copyBits + selectorBits)

/-- One request's metadata followed by its unchanged suffix. -/
abbrev payloadWidth (dimension width copyBits selectorBits suffixWidth : Nat) : Nat :=
  metadataWidth dimension width copyBits selectorBits + suffixWidth

/-- Offline metadata for one assigned source bit. -/
noncomputable def metadata (positive : 0 < width)
    (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Fin (2 ^ prefixWidth) ↪ InformationBit code copies)
    (copyBits selectorBits : Nat) (source : Fin (2 ^ prefixWidth)) :
    Fin (metadataWidth dimension width copyBits selectorBits) → Bool :=
  Fin.append (binaryExtensionVectorBits positive (placement source).2.1.val)
    (Fin.append (finiteIndexBits copyBits (placement source).1) (finiteIndexBits selectorBits (placement source).2.2))

/-- Target-field projection inside a processed request. -/
def targetProjection (dimension width copyBits selectorBits suffixWidth : Nat) (bit : Fin (dimension * width)) :
    Fin (payloadWidth dimension width copyBits selectorBits suffixWidth) :=
  Fin.castAdd suffixWidth (Fin.castAdd (copyBits + selectorBits) bit)

/-- Copy-index projection inside a processed request. -/
def copyProjection (dimension width copyBits selectorBits suffixWidth : Nat) (bit : Fin copyBits) :
    Fin (payloadWidth dimension width copyBits selectorBits suffixWidth) :=
  Fin.castAdd suffixWidth (Fin.natAdd (dimension * width) (Fin.castAdd selectorBits bit))

/-- Basis-bit projection inside a processed request. -/
def selectorProjection (dimension width copyBits selectorBits suffixWidth : Nat) (bit : Fin selectorBits) :
    Fin (payloadWidth dimension width copyBits selectorBits suffixWidth) :=
  Fin.castAdd suffixWidth (Fin.natAdd (dimension * width) (Fin.natAdd copyBits bit))

/-- Suffix projection inside a processed request. -/
def suffixProjection (dimension width copyBits selectorBits suffixWidth : Nat) (bit : Fin suffixWidth) :
    Fin (payloadWidth dimension width copyBits selectorBits suffixWidth) :=
  Fin.natAdd (metadataWidth dimension width copyBits selectorBits) bit

/-- Cost of one lookup shared by every request. -/
def costBound (requests prefixWidth dimension width copyBits selectorBits : Nat) : Nat :=
  256 * (2 ^ prefixWidth + requests) *
    (FiniteParameters.binaryDepth (2 ^ prefixWidth + requests) + prefixWidth +
      metadataWidth dimension width copyBits selectorBits + 2) ^ 5

/-- A concrete preprocessing circuit reads raw prefix/suffix requests and
returns their exact offline metadata and retained suffixes. -/
theorem existsCircuit (positive : 0 < width)
    (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Fin (2 ^ prefixWidth) ↪ InformationBit code copies)
    (requests suffixWidth copyBits selectorBits : Nat) :
    ∃ prepared : Circuit DeMorgan.signature (requests * (prefixWidth + suffixWidth))
      (requests * payloadWidth dimension width copyBits selectorBits suffixWidth),
      prepared.cost DeMorgan.standardCost ≤ costBound requests prefixWidth dimension width copyBits selectorBits ∧
      ∀ input request bit, prepared.eval DeMorgan.interpretation input (finProdFinEquiv (request, bit)) =
        Fin.append (metadata positive code placement copyBits selectorBits (requestSource input request))
          (requestSuffix input request) bit := by
  obtain ⟨lookup, lookupCorrect, lookupBound⟩ := BatchLookup.existsCircuit prefixWidth
    (metadataWidth dimension width copyBits selectorBits) requests
    (fun address => metadata positive code placement copyBits selectorBits (RuntimePacking.source address))
  let prefixIndex := fun index : Fin (requests * prefixWidth) =>
    let pair := (finProdFinEquiv (m := requests) (n := prefixWidth)).symm index
    finProdFinEquiv (pair.1, Fin.castAdd suffixWidth pair.2)
  let suffixWires := fun index : Fin (requests * suffixWidth) =>
    let pair := (finProdFinEquiv (m := requests) (n := suffixWidth)).symm index
    (DeMorgan.Wiring.input (finProdFinEquiv (pair.1, Fin.natAdd prefixWidth pair.2)) :
      DeMorgan.Wiring (requests * (prefixWidth + suffixWidth)))
  refine ⟨RecordArray.combine (lookup.mapInputs prefixIndex) (DeMorgan.Wiring.circuit suffixWires), ?_, ?_⟩
  · rw [RecordArray.combine_cost, Circuit.cost_mapInputs, DeMorgan.Wiring.circuit_cost, Nat.add_zero]
    exact lookupBound
  · intro input request bit
    rw [RecordArray.combine_eval]
    refine Fin.addCases (fun metadataBit => ?_) (fun suffixBit => ?_) bit
    · rw [Fin.append_left, Fin.append_left, Circuit.eval_mapInputs, lookupCorrect]
      congr 2
      funext addressBit
      simp only [Function.comp_apply, prefixIndex, Equiv.symm_apply_apply]
      rfl
    · rw [Fin.append_right, Fin.append_right, DeMorgan.Wiring.circuit_eval]
      simp only [suffixWires, Equiv.symm_apply_apply, DeMorgan.Wiring.eval_input]
      rfl

end Algebraic.MassProduction.HighRate.PrefixMetadata
