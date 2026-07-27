/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Asymptotics
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control.Defs

/-!
# Compositional width bounds for binary routines -- definitions

`SpaceBoundByWidthAt` separates exact all-prefix resource accounting from the
final asymptotic argument. Its certificates compose along pure value effects,
while `BinaryForSpaceEnvelope` bounds an input-dependent loop by one envelope
covering every reachable comparison, body invocation, and successor.
-/

@[expose] public section

namespace Complexity

namespace BinaryRoutine

/-- A routine's advertised all-prefix space bound is logarithmic along one
input-indexed initial-space and pure-value trajectory. -/
def SpaceBoundInLogAt (routine : BinaryRoutine n)
    (initialSpace : ℕ → ℕ) (values : ℕ → BinaryValues n) : Prop :=
  (fun inputLength =>
    routine.spaceBound (initialSpace inputLength) (values inputLength)) =O
      (fun inputLength => Nat.log 2 inputLength)

/-- A routine's advertised all-prefix space is bounded by one fixed multiple
of the binary width of an input-indexed value, in addition to the incoming
space budget. This pointwise certificate composes before any asymptotic
reasoning is required. -/
def SpaceBoundByWidthAt (routine : BinaryRoutine n)
    (initialSpace : ℕ → ℕ) (values : ℕ → BinaryValues n)
    (width : ℕ → ℕ) : Prop :=
  ∃ constant, ∀ inputLength,
    routine.spaceBound (initialSpace inputLength) (values inputLength) ≤
      initialSpace inputLength + constant * (width inputLength).size +
        constant

/-- Pointwise width certificates for a list of routines, following the exact
pure effect after every prefix. -/
def SeqListSpaceBoundByWidthAt {n : ℕ} :
    List (BinaryRoutine n) → (ℕ → ℕ) → (ℕ → BinaryValues n) →
      (ℕ → ℕ) → Prop
  | [], _, _, _ => True
  | routine :: routines, initialSpace, values, width =>
      SpaceBoundByWidthAt routine initialSpace values width ∧
        SeqListSpaceBoundByWidthAt routines initialSpace
          (fun inputLength => routine.effect (values inputLength)) width

/-- A single pointwise upper bound for every component of one binary
count-up loop's advertised auxiliary-space budget. -/
structure BinaryForSpaceEnvelope (body : BinaryRoutine n)
    (counterIdx limitIdx : Fin n) (initialSpace : ℕ)
    (initial : BinaryValues n) (bound : ℕ) : Prop where
  /-- The full-width counter/limit comparison fits in the envelope. -/
  compareSpace :
    initialSpace + TM.binaryForCompareTime (initial limitIdx) ≤ bound
  /-- The zero-iteration base case fits in the envelope. -/
  initialSpace_le : initialSpace ≤ bound
  /-- Every reachable body invocation fits in the envelope. -/
  bodySpace : ∀ count,
    count < binaryForCount counterIdx limitIdx initial →
      body.spaceBound initialSpace
        (binaryForValues body counterIdx initial count) ≤ bound
  /-- Every reachable controller successor fits in the envelope. -/
  successorSpace : ∀ count,
    count < binaryForCount counterIdx limitIdx initial →
      let current := binaryForValues body counterIdx initial count
      initialSpace + TM.binarySuccTime (current counterIdx) ≤ bound

/-- A single input-indexed trajectory containing every reachable body-entry
state of a binary loop. Pairing the input index with an arbitrary iteration
index lets one `SpaceBoundByWidthAt` certificate expose a constant uniform in
both parameters. Out-of-range iterations are clamped to the last valid index;
the zero-iteration case is harmless because no body state is then queried. -/
def binaryForClampedValues (body : BinaryRoutine n)
    (counterIdx limitIdx : Fin n) (values : ℕ → BinaryValues n)
    (code : ℕ) : BinaryValues n :=
  let inputLength := (Nat.unpair code).1
  let total := binaryForCount counterIdx limitIdx (values inputLength)
  binaryForValues body counterIdx (values inputLength)
    (min (Nat.unpair code).2 (total - 1))

end BinaryRoutine

end Complexity
