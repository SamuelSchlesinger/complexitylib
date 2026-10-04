/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Shared.Matching.Internal

/-!
# Pairing conjunction gates with overlapping primary supports

Among actual conjunction gates with exactly two distinct direct primary inputs,
one can choose gate-disjoint intersecting pairs leaving at most `n / 2` gates.
This is a finite graph matching argument; no circuit semantic hypothesis is used.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Shared

/-- Pair exact-two conjunctions so at most half the input count remains unpaired. -/
theorem exists_pairing_le_half {n g : ℕ} (p : Program signature n g) :
    ∃ P : PrimaryPairing p, (exactTwo p).card ≤ 2 * P.pairs.card + n / 2 := by
  obtain ⟨P, disjoint⟩ := exists_pairing_disjoint_remaining p
  refine ⟨P, ?_⟩
  rw [P.card_exactTwo]
  exact Nat.add_le_add_left (P.card_remaining_le disjoint) _

/-- A denominator-free version of the maximal pairing bound. -/
theorem exists_pairing_two_mul_le {n g : ℕ} (p : Program signature n g) :
    ∃ P : PrimaryPairing p, 2 * (exactTwo p).card ≤ 4 * P.pairs.card + n := by
  obtain ⟨P, bound⟩ := exists_pairing_le_half p
  exact ⟨P, by lia⟩

end Algebraic.Aggregate.Geometry.Shared
