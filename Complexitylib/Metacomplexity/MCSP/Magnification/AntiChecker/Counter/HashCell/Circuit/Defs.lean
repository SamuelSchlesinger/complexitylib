/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.HashCell.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Hashing.Defs
public import Complexitylib.SAT.CircuitSatisfiability.Defs
public import Complexitylib.Circuits.Encoding

/-!
# Circuit predicates for anti-checker hash cells -- definitions

For fixed anti-checker parameters and one hash range width, a predicate circuit
reads the packed labeled samples and affine seed as a public prefix, followed by
one existential powered-survivor witness. Its canonical serialized code and a
zero ruler form a query to `CircuitSAT.extensionLanguage`.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Width of the powered survivor tuple quantified by one occupancy query. -/
@[reducible] def counterSurvivorPowerWidth (beta : PositiveRationalScale) (arity : ℕ) : ℕ :=
  survivorPowerWidth arity (smallThreshold beta arity) (roundPrecision arity)

/-- Width of the public labeled-sample and affine-seed prefix for one hash-cell
query. -/
def hashCellPublicWidth (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) : ℕ :=
  counterInputWidth arity prefixLength +
    PairwiseIndependentHash.affineSeedWidth
      (counterSurvivorPowerWidth beta arity) rangeWidth

instance (beta : PositiveRationalScale) (arity prefixLength rangeWidth : ℕ) :
    NeZero (hashCellPublicWidth beta arity prefixLength rangeWidth) :=
  ⟨by simp [hashCellPublicWidth, counterInputWidth]⟩

/-- Total input width of a hash-cell predicate circuit: public query bits
followed by the existential survivor tuple. -/
def hashCellPredicateInputWidth (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) : ℕ :=
  hashCellPublicWidth beta arity prefixLength rangeWidth +
    counterSurvivorPowerWidth beta arity

instance (beta : PositiveRationalScale) (arity prefixLength rangeWidth : ℕ) :
    NeZero (hashCellPredicateInputWidth beta arity prefixLength rangeWidth) :=
  ⟨by simp [hashCellPredicateInputWidth, hashCellPublicWidth,
    counterInputWidth]⟩

/-- Pack labeled samples and one affine seed into the public prefix of a
hash-cell predicate. -/
def hashCellPublicInput {arity prefixLength rangeWidth : ℕ}
    (beta : PositiveRationalScale)
    (input : BitString (counterInputWidth arity prefixLength))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (counterSurvivorPowerWidth beta arity) rangeWidth)) :
    BitString (hashCellPublicWidth beta arity prefixLength rangeWidth) :=
  Fin.append input seed

/-- A single-output circuit deciding the exact powered-survivor hash-cell
witness predicate from a public sample/seed prefix and an existential tuple. -/
structure HashCellPredicateCircuit (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) where
  /-- Number of internal gates in the predicate circuit. -/
  internalGates : ℕ
  /-- The fixed predicate circuit for these anti-checker parameters. -/
  circuit : Circuit Basis.andOr2
    (hashCellPredicateInputWidth beta arity prefixLength rangeWidth)
    1 internalGates
  /-- Exact agreement with the semantic hash-cell witness relation. -/
  implements : ∀ input seed witness,
    circuit.eval
        (Fin.append (hashCellPublicInput beta input seed) witness) 0 =
      decide (HashCellWitness arity (smallThreshold beta arity)
        (roundPrecision arity) rangeWidth input seed witness)

namespace HashCellPredicateCircuit

/-- Tagged serialized code of the positive-input predicate circuit. -/
def code {beta : PositiveRationalScale} {arity prefixLength rangeWidth : ℕ}
    (predicate : HashCellPredicateCircuit beta arity prefixLength rangeWidth) :
    List Bool :=
  true :: CircuitCode.encodeCircuit predicate.circuit

/-- The exact-width zero ruler for the existential powered-survivor tuple. -/
def ruler (beta : PositiveRationalScale) (arity : ℕ) : List Bool :=
  List.replicate (counterSurvivorPowerWidth beta arity) false

/-- Canonical fixed-prefix circuit-satisfiability query for one sample input
and affine hash seed. -/
def query {beta : PositiveRationalScale} {arity prefixLength rangeWidth : ℕ}
    (predicate : HashCellPredicateCircuit beta arity prefixLength rangeWidth)
    (input : BitString (counterInputWidth arity prefixLength))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (counterSurvivorPowerWidth beta arity) rangeWidth)) : List Bool :=
  pair predicate.code <| pair (hashCellPublicInput beta input seed).toList
    (ruler beta arity)

end HashCellPredicateCircuit

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
