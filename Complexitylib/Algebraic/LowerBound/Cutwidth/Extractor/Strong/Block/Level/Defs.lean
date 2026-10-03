/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Defs

/-!
# One deterministic condense-then-split level

Apply a supplied condenser to every current block with the same fresh seed,
then split its pair outputs into consecutive half-blocks. The map specifies
only this deterministic operation; retaining prior seeds and sampling the
fresh seed are handled by `retainedSeedStep` in the statistical theorem.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Condense all blocks with one seed, then place each pair's two outputs consecutively. -/
def condenseSplitMap {α β Fresh : Type*} (C : α → Fresh → β × β)
    (t : Nat) (x : Fin t → α) (y : Fresh) : Fin (2 * t) → β :=
  splitBlockEquiv β t (fun i => C (x i) y)

end Algebraic.Cutwidth.Extractor
