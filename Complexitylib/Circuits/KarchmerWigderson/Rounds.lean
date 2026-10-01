/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.Rounds.Defs
public import Complexitylib.Circuits.KarchmerWigderson.Rounds.Internal

/-!
# General bounded-round Karchmer--Wigderson protocols

`RoundProtocol ι M d` sends at most `d` messages from the alphabet `M`.
Its output names a differing coordinate, with no monotonicity restriction.
`TopDown` develops the density-rectangle adversary for this model.
-/

public section

namespace Complexity.KarchmerWigderson.RoundProtocol

/-- Swapping all speakers swaps the input arguments to the protocol's run. -/
theorem run_swapPlayers {ι M : Type*} {d : ℕ} (P : RoundProtocol ι M d) (x y : ι → Bool) :
    P.swapPlayers.run x y = P.run y x := run_swapPlayers_internal P x y

/-- Player swapping gives a protocol for the complemented function. -/
theorem SolvesKW.swapPlayers {ι M : Type*} {d : ℕ} {P : RoundProtocol ι M d}
    {f : (ι → Bool) → Bool} (h : P.SolvesKW f) : P.swapPlayers.SolvesKW (fun x => !f x) :=
  SolvesKW.swapPlayers_internal h

end Complexity.KarchmerWigderson.RoundProtocol
