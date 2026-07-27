/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Defs
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Internal

/-!
# Proof-carrying binary stream routines

`BinaryRoutine` is an experimental composition layer for append-only machines
whose complete work state is a vector of canonical rewound binary naturals.
Each routine carries a pure domain, exact value-vector effect, exact emitted
word, and explicit time/all-prefix-space bounds. `BinaryRoutine.Sound` ties
those fields to one `HoareTimeSpace` contract and transducer proof on every
canonical state in the domain.

The pure domain is deliberate: predecessor honestly requires a positive value,
while copying and gate emission honestly require their reusable scratch value
to be zero. Sequential composition conjoins those obligations at the correct
intermediate value vector. Loop, branch, and polynomial adapters are outside
this initial layer.

## Main results

- `BinaryRoutine.Sound.seq` composes proofs across `seqTM`.
- `BinaryRoutine.identity_sound` proves the empty-emission identity.
- `BinaryRoutine.emitBits_sound` adapts fixed-word emission.
- `BinaryRoutine.binarySucc_sound` and `binaryPred_sound` adapt arithmetic.
- `BinaryRoutine.binaryCopy_sound` adapts framed canonical copying.
- `BinaryRoutine.emitRawGateStep_sound` adapts one streaming raw gate.
-/

@[expose] public section

namespace Complexity

namespace BinaryRoutine

variable {n : ℕ}

/-- The canonical tape realizes its advertised natural value. -/
theorem natTape_hasBinaryNat (value : ℕ) :
    (natTape value).HasBinaryNat value :=
  natTape_hasBinaryNat_internal value

/-- Every canonical binary natural tape is parked. -/
theorem natTape_parked (value : ℕ) :
    TM.Parked (natTape value) :=
  natTape_parked_internal value

/-- Each tape in a canonical work vector realizes its corresponding value. -/
theorem workTapes_hasBinaryNat (values : BinaryValues n) (i : Fin n) :
    (workTapes values i).HasBinaryNat (values i) :=
  workTapes_hasBinaryNat_internal values i

/-- Every tape in a canonical work vector is parked. -/
theorem workTapes_parked (values : BinaryValues n) :
    ∀ i, TM.Parked (workTapes values i) :=
  workTapes_parked_internal values

/-- Updating one pure value is exactly a literal update of its canonical tape. -/
theorem workTapes_update (values : BinaryValues n) (idx : Fin n)
    (value : ℕ) :
    workTapes (Function.update values idx value) =
      Function.update (workTapes values) idx (natTape value) :=
  workTapes_update_internal values idx value

/-- Sound routines compose, with second-phase obligations and bounds evaluated
at the first routine's exact value effect. -/
theorem Sound.seq {first second : BinaryRoutine n}
    (hfirst : first.Sound) (hsecond : second.Sound) :
    (seq first second).Sound :=
  hfirst.seq_internal hsecond

/-- Strengthening a routine's pure precondition preserves soundness without
changing its concrete behavior or resource bounds. -/
theorem Sound.restrict {routine : BinaryRoutine n}
    (hsound : routine.Sound) (requires : BinaryValues n → Prop)
    (hrequires : ∀ values, requires values → routine.requires values) :
    (routine.restrict requires).Sound :=
  hsound.restrict_internal requires hrequires

/-- Fixed-word emission is sound; its all-prefix bound is obtained honestly
from its exact running time. -/
theorem emitBits_sound (word : List Bool) :
    (emitBits (n := n) word).Sound :=
  emitBits_sound_internal word

/-- Empty fixed-word emission is a sound routine identity. -/
theorem identity_sound : (identity (n := n)).Sound :=
  identity_sound_internal

/-- Canonical binary successor is a sound value-vector leaf. -/
theorem binarySucc_sound (idx : Fin n) :
    (binarySucc idx).Sound :=
  binarySucc_sound_internal idx

/-- Canonical positive binary predecessor is a sound value-vector leaf. Its
routine domain is exactly `0 < values idx`. -/
theorem binaryPred_sound (idx : Fin n) :
    (binaryPred idx).Sound :=
  binaryPred_sound_internal idx

/-- Framed canonical binary copying is sound when the three indices are
distinct; its routine domain records that the private counter value is zero. -/
theorem binaryCopy_sound
    (srcIdx dstIdx counterIdx : Fin n) :
    (binaryCopy srcIdx dstIdx counterIdx).Sound :=
  binaryCopy_sound_internal srcIdx dstIdx counterIdx

/-- One raw-gate stream step is a sound routine leaf. Its pure effect advances
only `availableIdx`, and its emitted word is exactly `RawGate.encode`. -/
theorem emitRawGateStep_sound
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx availableIdx input₀Idx input₁Idx : Fin n) :
    (emitRawGateStep op negated₀ negated₁ emitCounterIdx availableIdx
      input₀Idx input₁Idx).Sound :=
  emitRawGateStep_sound_internal op negated₀ negated₁ emitCounterIdx
    availableIdx input₀Idx input₁Idx

end BinaryRoutine

end Complexity
