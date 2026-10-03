/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fintype.Card

/-!
# Universal finite hash families

Distinct inputs collide on at most a `1 / card Ω` fraction of seeds. The
division-free cardinality condition is meaningful even for empty types;
probability bounds separately require nonempty sampling types. Universality
does not assert independence of the two hash outputs.

This is Definition 2 of Barak, Dodis, Krawczyk, Pereira, Pietrzak, Standaert,
and Yu, *Leftover Hash Lemma, Revisited* (CRYPTO 2011), specialized to exact
universality and arbitrary finite output types.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- Distinct inputs collide on at most the reciprocal output-cardinality
fraction of the uniformly sampled seeds. -/
def UniversalHashFamily {α Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (E : α → Seed → Ω) : Prop :=
  ∀ x x', x ≠ x' →
    (Finset.univ.filter fun y => E x y = E x' y).card * Fintype.card Ω ≤
      Fintype.card Seed

end Algebraic.Cutwidth.Extractor
