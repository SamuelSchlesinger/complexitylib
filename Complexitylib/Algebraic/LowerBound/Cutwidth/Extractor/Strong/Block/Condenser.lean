/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser.Internal

/-!
# Condensing a block source with one shared seed

Apply a strong condenser to each of `t` source blocks with the same
independent uniform seed. The joint output, including that seed, is within
`t * ε` of a family of block sources at the condenser's output threshold.
The source blocks may be dependent. Every ideal conditional law is a
normalized block source; only the average distance over seeds is bounded.
Empty seed types follow the weighted definitions' zero-mass convention.

This proves the finite block-source condensing mechanism of
Chattopadhyay--Goodman--Liao, Lemma 5.5 of *Affine Extractors for Almost
Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/download/>.
The proof corrects conditional tails before their heads, using correlated
marginal replacement and exact averaging of conditional distances.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A shared uniform seed condenses every block, with one copy of the
seed retained and at most one condenser error per source block. -/
theorem WeightedStrongSeededCondenser.block {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω]
    {C : α → Seed → Ω} {Kin Kout : Nat} {ε : ℝ}
    (cond : WeightedStrongSeededCondenser C Kin Kout ε)
    {t : Nat} {p : (Fin t → α) → ℝ} (source : IsBlockSource p Kin) :
    ∃ q : Seed → (Fin t → Ω) → ℝ,
      (∀ y, IsBlockSource (q y) Kout) ∧
        weightDist (weightedSeededOutput p (fun x y i => C (x i) y))
          (seedFamilyWeight q) ≤ (t : ℝ) * ε :=
  Internal.weightedStrongSeededCondenser_block cond source

end Algebraic.Cutwidth.Extractor
