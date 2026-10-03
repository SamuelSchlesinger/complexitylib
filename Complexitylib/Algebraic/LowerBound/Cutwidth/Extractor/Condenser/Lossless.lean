/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Internal

/-!
# Strong flat lossless condensation from full-neighbor expansion

For a uniform source on `P`, retain one original source point for every
reached output at each seed. If the output alphabet has at least `P.card`
elements, these assignments extend to injections on `P`, separately for
each seed. Thus the ideal output is uniform on `P.card` values conditional
on every seed, and the seed itself is preserved exactly. Full-neighbor
expansion bounds the fraction of changed source and seed pairs and hence
the discrepancy of every seeded output test.

This is the finite support argument underlying Guruswami, Umans, and
Vadhan (2009), Lemma 4.1, with completion inside each seed fiber:
https://salil.seas.harvard.edu/sites/g/files/omnuum4266/files/salil/files/acm2009.pdf.
The witness may depend on the source support and is not an evaluator.
Extending the result to nonuniform sources requires a separate decomposition
into flat sources; no such decomposition is assumed or supplied here.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- Complete one representative per reached output to an injection at each
seed. The number of unchanged original pairs is exactly the neighbor count.
The statement also holds for empty source, seed, and output types. -/
theorem exists_seedwise_injection {α Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (C : α → Seed → Ω) (P : Finset α) (capacity : P.card ≤ Fintype.card Ω) :
    ∃ g : Seed → (P ↪ Ω),
      ((Finset.univ : Finset (P × Seed)).filter
        fun xy => C xy.1.val xy.2 = g xy.2 xy.1).card = (seededNeighborSet C P).card :=
  Internal.exists_seedwise_injection C P capacity

/-- Coupling two seeded maps on the same uniform source and seed bounds every
test discrepancy by the fraction of pairs on which their outputs differ. -/
theorem seededTestProb_sub_le_disagreement {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] (C G : α → Seed → Ω) (T : Finset (Seed × Ω)) :
    |seededTestProb C T - seededTestProb G T| ≤
      (((Finset.univ : Finset (α × Seed)).filter
        fun xy => C xy.1 xy.2 ≠ G xy.1 xy.2).card : ℝ) /
          ((Fintype.card α : ℝ) * Fintype.card Seed) :=
  Internal.seededTestProb_sub_le_disagreement C G T

/-- Full-neighbor expansion gives error at most `ε` against an ideal seeded
output that, conditional on each seed, is uniform on `P.card` distinct values. -/
theorem exists_seedwise_injection_of_expansion {α Seed Ω : Type*}
    [Fintype Seed] [Nonempty Seed] [Fintype Ω]
    (C : α → Seed → Ω) (P : Finset α) (nonempty : P.Nonempty)
    (capacity : P.card ≤ Fintype.card Ω) {ε : ℝ}
    (expansion : (1 - ε) * P.card * Fintype.card Seed ≤ (seededNeighborSet C P).card) :
    ∃ g : Seed → (P ↪ Ω), ∀ T : Finset (Seed × Ω),
      |seededTestProb (fun x : P => C x.val) T -
        seededTestProb (fun x y => g y x) T| ≤ ε :=
  Internal.exists_seedwise_injection_of_expansion C P nonempty capacity expansion

end Algebraic.Cutwidth.Extractor
