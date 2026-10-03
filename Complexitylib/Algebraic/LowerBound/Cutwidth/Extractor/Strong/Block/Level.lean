/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Level.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedStep.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Level.Internal

/-!
# A retained-seed condense-then-split level

An actual joint weighting may already differ from an ideal block-source
family at the earlier seeds. Introduce one fresh uniform seed, condense
all current blocks with that seed, and split each pair output. The old
joint error is retained, and each current block adds the condenser error
plus the splitting error. Both seed coordinates remain in the comparison.

The condensation bound is averaged over the earlier seeds while retaining
the fresh seed. It is not a separate error bound at each fresh seed. The
actual input weights need not be nonnegative or normalized for distance
contraction. The theorem also covers an empty fresh seed type under the
weighted definitions' zero-mass convention.

This is the finite combination of Chattopadhyay--Goodman--Liao,
Corollary 5.4 and Lemma 5.5, used in Theorem 5.6:
<https://eccc.weizmann.ac.il/report/2021/075/download/>.
It does not supply the full recursive schedule or an encoded runtime loop.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Carry an existing joint approximation through one fresh-seed condensation
and splitting level, retaining all earlier seeds and adding only the stated errors. -/
theorem WeightedStrongSeededCondenser.condenseSplit {Earlier Fresh α β : Type*}
    [Fintype Earlier] [Nonempty Earlier] [Fintype Fresh] [Fintype α] [Fintype β]
    {C : α → Fresh → β × β} {Kin k : Nat} {ε : ℝ}
    (cond : WeightedStrongSeededCondenser C Kin (2 ^ k) ε)
    {t m s e : Nat} {η : ℝ} (p : Earlier → (Fin t → α) → ℝ)
    (actual : Earlier × (Fin t → α) → ℝ)
    (source : ∀ y, IsBlockSource (p y) Kin)
    (close : weightDist actual (seedFamilyWeight p) ≤ η)
    (card : Fintype.card β = 2 ^ m) (width : s ≤ m) (entropy : m + s + e ≤ k) :
    ∃ q : Earlier × Fresh → (Fin (2 * t) → β) → ℝ,
      (∀ sy, IsBlockSource (q sy) (2 ^ s)) ∧
        weightDist (retainedSeedStep (fun _ => condenseSplitMap C t) actual)
          (seedFamilyWeight q) ≤ η + (t : ℝ) * (ε + ((2 : ℝ) ^ e)⁻¹) :=
  Internal.weightedStrongSeededCondenser_condenseSplit
    cond p actual source close card width entropy

end Algebraic.Cutwidth.Extractor
