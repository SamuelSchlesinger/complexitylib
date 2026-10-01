/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.Rounds.Defs

/-!
# Player-swapping semantics

Swapping the speakers swaps the two inputs to the run. This gives the
complemented-function protocol with unchanged message and round bounds.
-/

public section

namespace Complexity.KarchmerWigderson.RoundProtocol

theorem run_swapPlayers_internal {ι M : Type*} :
    ∀ {d : ℕ} (P : RoundProtocol ι M d) (x y : ι → Bool),
    P.swapPlayers.run x y = P.run y x
  | _, .answer _, _, _ => rfl
  | _, .alice send next, x, y => run_swapPlayers_internal (next (send y)) x y
  | _, .bob send next, x, y => run_swapPlayers_internal (next (send x)) x y

theorem SolvesKW.swapPlayers_internal {ι M : Type*} {d : ℕ} {P : RoundProtocol ι M d}
    {f : (ι → Bool) → Bool} (h : P.SolvesKW f) : P.swapPlayers.SolvesKW (fun x => !f x) := by
  intro x y hx hy
  rw [run_swapPlayers_internal]
  exact (h y x (by simpa using hy) (by simpa using hx)).symm


end Complexity.KarchmerWigderson.RoundProtocol
