/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Mathlib.Data.Fin.Tuple.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Conditioning.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Conditioning.Internal.Prefix
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Conditioning.Internal.Prepend

/-!
# Head and tail conditioning for finite block sources

A nonempty block source splits into a normalized capped head distribution
and a normalized block-source tail for every head value. Positive rows use
their conditional distribution. Zero rows can copy a positive row because
their coefficient in the joint distribution is zero.

Conversely, a capped head and block-source tails form a block source.
The more general coefficient criterion combines tails with nonnegative
weights whose row totals form the prescribed capped head distribution;
it needs no positive-row assumptions or conditional division.

These are finite structural steps for the block-source argument in
Chattopadhyay--Goodman--Liao, Lemma 5.5 of *Affine Extractors for Almost
Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
`Block.Condenser` uses these laws to prove shared-seed condensation.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A nonempty prefix retains the head and restricts only the tail. -/
theorem blockPrefix_cons {α : Type*} {i t : Nat} (h : i ≤ t)
    (a : α) (z : Fin t → α) :
    blockPrefix (Nat.succ_le_succ h) (Fin.cons a z) = Fin.cons a (blockPrefix h z) :=
  Internal.blockPrefix_cons h a z

/-- Fixing a nonempty prefix is the corresponding prefix event in its head row. -/
theorem blockPrefixWeight_cons {α : Type*} [Fintype α] {i t : Nat}
    (p : (Fin (t + 1) → α) → ℝ) (h : i ≤ t) (a : α) (u : Fin i → α) :
    blockPrefixWeight p (Nat.succ_le_succ h) (Fin.cons a u) =
      blockPrefixWeight (fun z : Fin t → α => p (Fin.cons a z)) h u :=
  Internal.blockPrefixWeight_cons p h a u

/-- The head marginal counts every tail in the corresponding row. -/
theorem mapWeight_blockHead_apply {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin (t + 1) → α) → ℝ) (a : α) :
    mapWeight (fun x => x 0) p a = ∑ z : Fin t → α, p (Fin.cons a z) :=
  Internal.mapWeight_blockHead_apply p a

/-- The head inherits the block-source threshold. -/
theorem IsBlockSource.head_capped {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin (t + 1) → α) → ℝ} (source : IsBlockSource p K) :
    CappedWeight (mapWeight (fun x => x 0) p) K :=
  Internal.blockSource_head_capped source

/-- Disintegrate a nonempty tuple source into a capped head and normalized
block-source tails, completing zero-mass head rows without extra assumptions. -/
theorem IsBlockSource.exists_head_tail {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin (t + 1) → α) → ℝ} (source : IsBlockSource p K) :
    ∃ w : α → ℝ, ∃ q : α → (Fin t → α) → ℝ,
      IsProbabilityWeight w ∧ CappedWeight w K ∧
        (∀ a, IsBlockSource (q a) K) ∧
          ∀ a z, p (Fin.cons a z) = w a * q a z :=
  Internal.blockSource_exists_head_tail source

/-- Prepend a normalized capped head to a block-source tail for every head value. -/
theorem isBlockSource_prepend {α : Type*} [Fintype α] {t K : Nat}
    (w : α → ℝ) (tail : α → (Fin t → α) → ℝ)
    (head_prob : IsProbabilityWeight w) (head_cap : CappedWeight w K)
    (tail_source : ∀ a, IsBlockSource (tail a) K) :
    IsBlockSource (fun x : Fin (t + 1) → α => w (x 0) * tail (x 0) (Fin.tail x)) K :=
  Internal.blockSource_prepend w tail head_prob head_cap tail_source

/-- Nonnegative mixtures in each head row preserve all tail caps when
the row totals form a normalized capped head distribution. -/
theorem isBlockSource_of_prepend_mixture {α ι : Type*} [Fintype α] [Fintype ι] {t K : Nat}
    (r : (Fin (t + 1) → α) → ℝ) (target : α → ℝ)
    (tail : ι → (Fin t → α) → ℝ) (c : α → ι → ℝ)
    (target_prob : IsProbabilityWeight target) (target_cap : CappedWeight target K)
    (tail_source : ∀ a, IsBlockSource (tail a) K) (coeff_nonneg : ∀ h a, 0 ≤ c h a)
    (rows : ∀ h, ∑ a, c h a = target h)
    (factor : ∀ h z, r (Fin.cons h z) = ∑ a, c h a * tail a z) :
    IsBlockSource r K :=
  Internal.blockSource_of_prepend_mixture r target tail c target_prob target_cap
    tail_source coeff_nonneg rows factor

end Algebraic.Cutwidth.Extractor
