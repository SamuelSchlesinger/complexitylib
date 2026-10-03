/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.FiniteCounting
public import Complexitylib.Circuits.BitString

/-!
# Majority as the final sumset-extractor stage

Chattopadhyay and Liao, *Extractors for Sum of Two Sources* (2021), use majority
after their reduction to non-oblivious bit-fixing sources in the proof of
Theorem 2. This module gives that final deterministic operation, with ties
returning `false`, and the signed vote margin on any designated set of good
coordinates. It does not construct the preceding reduction.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Evaluate strict majority uniformly on an input of any length. The empty
input and ties return the one-bit verdict `false`. -/
def majorityEval (x : List Bool) : List Bool :=
  [Complexity.majority (fun i : Fin x.length => x[i])]

/-- The number of true votes minus false votes on the designated good
coordinates. -/
def voteMargin {n : Nat} (good : Finset (Fin n)) (x : Fin n → Bool) : Int :=
  2 * ((good.filter fun i => x i = true).card : Int) - good.card

end Algebraic.Cutwidth.Extractor
