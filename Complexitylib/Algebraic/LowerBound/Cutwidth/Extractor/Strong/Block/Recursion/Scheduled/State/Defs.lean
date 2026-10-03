/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Defs
public import Complexitylib.Encoding.Pairing
public import Mathlib.Logic.Function.Iterate

/-!
# Runtime numerical states for scheduled block recursion

The evolving state consists of the current block width and entropy
threshold. A transition computes the actual next condenser half-width and
divides the threshold by four. The local error exponent is fixed workspace.

The string codec is `pair (pair unaryWidth unaryEntropy) unaryError`.
Its step is total and uses the standard total pairing projections on
malformed inputs. Certificates for complete iteration require bounds on
every intermediate state.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Update the two runtime numerical parameters of one rate-three level. -/
def scheduledBlockStateStep (E : Nat) (state : Nat × Nat) : Nat × Nat :=
  (explicitCondenserHalfWidth state.1 state.2 E 3, state.2 / 4)

/-- Encode the evolving width and entropy together with the fixed local error exponent. -/
def encodeScheduledBlockState (E : Nat) (state : Nat × Nat) : List Bool :=
  pair (pair (List.replicate state.1 true) (List.replicate state.2 true))
    (List.replicate E true)

/-- One total uniform step on the nested unary state codec. -/
def scheduledBlockStateStepEval (z : List Bool) : List Bool :=
  pair
    (pair
      (List.replicate (explicitCondenserHalfWidth (pairFst (pairFst z)).length
        (pairSnd (pairFst z)).length (pairSnd z).length 3) true)
      (List.replicate ((pairSnd (pairFst z)).length / 4) true))
    (pairSnd z)

end Algebraic.Cutwidth.Extractor
