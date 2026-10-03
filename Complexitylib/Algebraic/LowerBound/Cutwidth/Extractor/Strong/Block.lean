/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Internal.Two

/-!
# Structural laws for finite block sources

A block source satisfies a mass cap for each coordinate after fixing every
earlier coordinate. The caps survive taking prefixes, weakening the entropy
threshold, and mixing sources with normalized nonnegative weights. Zero
blocks impose only normalization; one block gives the usual point-mass cap.
For two blocks the definition is equivalent to the marginal and conditional
caps established by the separate Splitting module. A source with `t` blocks
and threshold `K` satisfies `(K^t)*p x ≤ 1` at every tuple. Using the alphabet
cardinality as the threshold forces the entire tuple to be uniform.

These are finite structural ingredients for the block-source arguments in
Chattopadhyay--Goodman--Liao, Section 5 of *Affine Extractors for Almost
Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
`Block.Condenser` uses these laws to condense all blocks with a shared seed.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Taking all coordinates leaves a tuple unchanged. -/
theorem blockPrefix_self {α : Type*} {t : Nat} (x : Fin t → α) :
    blockPrefix (Nat.le_refl t) x = x :=
  Internal.blockPrefix_self x

/-- Successive restrictions agree with a direct prefix restriction. -/
theorem blockPrefix_comp {α : Type*} {i j t : Nat} (hij : i ≤ j) (hjt : j ≤ t)
    (x : Fin t → α) :
    blockPrefix hij (blockPrefix hjt x) = blockPrefix (hij.trans hjt) x :=
  Internal.blockPrefix_comp hij hjt x

/-- The full prefix retains each original point weight. -/
theorem blockPrefixWeight_self {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin t → α) → ℝ) : blockPrefixWeight p (Nat.le_refl t) = p :=
  Internal.blockPrefixWeight_self p

/-- The unique empty prefix has the source's total mass. -/
theorem blockPrefixWeight_zero {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin t → α) → ℝ) (h : 0 ≤ t) (u : Fin 0 → α) :
    blockPrefixWeight p h u = ∑ x, p x :=
  Internal.blockPrefixWeight_zero p h u

/-- Marginalizing a prefix again agrees with marginalizing the original source. -/
theorem blockPrefixWeight_prefix {α : Type*} [Fintype α] {i j t : Nat}
    (p : (Fin t → α) → ℝ) (hij : i ≤ j) (hjt : j ≤ t) :
    blockPrefixWeight (blockPrefixWeight p hjt) hij =
      blockPrefixWeight p (hij.trans hjt) :=
  Internal.blockPrefixWeight_prefix p hij hjt

/-- Prefix weights commute with arbitrary finite linear combinations. -/
theorem blockPrefixWeight_mixture {α ι : Type*} [Fintype α] [Fintype ι] {i t : Nat}
    (p : ι → (Fin t → α) → ℝ) (w : ι → ℝ) (h : i ≤ t) (u : Fin i → α) :
    blockPrefixWeight (fun x => ∑ j, w j * p j x) h u =
      ∑ j, w j * blockPrefixWeight (p j) h u :=
  Internal.blockPrefixWeight_mixture p w h u

/-- A block source is a normalized nonnegative weighting. -/
theorem IsBlockSource.probability {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K) : IsProbabilityWeight p :=
  source.1

/-- Every one-block prefix extension obeys the conditional mass cap. -/
theorem IsBlockSource.cap {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K)
    (i : Fin t) (u : Fin (i.val + 1) → α) :
    (K : ℝ) * blockPrefixWeight p (Nat.succ_le_of_lt i.isLt) u ≤
      blockPrefixWeight p (Nat.le_of_lt i.isLt) (blockPrefix (Nat.le_succ i.val) u) :=
  source.2 i u

/-- With no blocks, there are no conditional caps to check. -/
theorem isBlockSource_zero_iff {α : Type*} [Fintype α]
    (p : (Fin 0 → α) → ℝ) (K : Nat) :
    IsBlockSource p K ↔ IsProbabilityWeight p :=
  Internal.blockSource_zero_iff p K

/-- A single block is a probability source with the ordinary point-mass cap. -/
theorem isBlockSource_one_iff {α : Type*} [Fintype α]
    (p : (Fin 1 → α) → ℝ) (K : Nat) :
    IsBlockSource p K ↔ IsProbabilityWeight p ∧ CappedWeight p K :=
  Internal.blockSource_one_iff p K

/-- Pair weights form a two-block source exactly when the first marginal
and every second-coordinate conditional satisfy the same threshold. -/
theorem isBlockSource_two_iff {α : Type*} [Fintype α] (p : α × α → ℝ) (K : Nat) :
    IsBlockSource (fun x : Fin 2 → α => p (x 0, x 1)) K ↔
      IsProbabilityWeight p ∧ CappedWeight (firstWeight p) K ∧
        ∀ a b, (K : ℝ) * p (a, b) ≤ firstWeight p a :=
  Internal.blockSource_two_iff p K

/-- A smaller threshold weakens every conditional cap. -/
theorem IsBlockSource.mono {α : Type*} [Fintype α] {t K L : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K) (threshold : L ≤ K) :
    IsBlockSource p L :=
  Internal.blockSource_mono source threshold

/-- Every initial sequence of blocks retains the block-source threshold. -/
theorem IsBlockSource.prefix {α : Type*} [Fintype α] {j t K : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K) (h : j ≤ t) :
    IsBlockSource (blockPrefixWeight p h) K :=
  Internal.blockSource_prefix source h

/-- Conditional caps multiply to give the full tuple a threshold of `K^t`. -/
theorem IsBlockSource.capped {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K) : CappedWeight p (K ^ t) :=
  Internal.blockSource_capped source

/-- Full conditional entropy in every block forces the full tuple to be uniform. -/
theorem IsBlockSource.eq_uniform {α : Type*} [Fintype α] {t : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p (Fintype.card α)) :
    p = uniformWeight (Fin t → α) :=
  Internal.blockSource_eq_uniform source

/-- Normalized nonnegative mixtures preserve all conditional prefix caps. -/
theorem IsBlockSource.mixture {α ι : Type*} [Fintype α] [Fintype ι] {t K : Nat}
    (p : ι → (Fin t → α) → ℝ) (w : ι → ℝ) (weights : IsProbabilityWeight w)
    (sources : ∀ j, IsBlockSource (p j) K) :
    IsBlockSource (fun x => ∑ j, w j * p j x) K :=
  Internal.blockSource_mixture p w weights sources

end Algebraic.Cutwidth.Extractor
