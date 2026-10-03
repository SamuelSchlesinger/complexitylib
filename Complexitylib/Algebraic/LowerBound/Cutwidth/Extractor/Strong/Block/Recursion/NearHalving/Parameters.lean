/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Internal

/-!
# Finite splitting and resource bounds for the near-halving schedule

The depth-dependent rate and entropy reserve certify both splitting
inequalities at every executed level. One initial logarithmic budget bounds
all actual rounded widths and field seeds. The full seed estimate includes
the final one-shot pair shared by all leaves. Total block payload stays at
most twice the initial width, and positive reserve bounds block counts too.

The entropy requirements are those of Chattopadhyay--Goodman--Liao,
Corollary 5.4 of *Affine Extractors for Almost Logarithmic Entropy*,
<https://eccc.weizmann.ac.il/report/2021/075/>. This schedule and its finite
arithmetic estimates are deductions from the checked paired-condenser API.
No asymptotic parameter choice or full runtime bound is asserted here.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Each split retains half the entropy after paying its exact reserve gap. -/
theorem nearHalvingBlockEntropy_succ (h Q : Nat) {i : Nat} (level : i < h) :
    nearHalvingBlockEntropy h Q i = 2 * nearHalvingBlockEntropy h Q (i + 1) + 2 ^ (h - i) * Q :=
  Internal.nearHalvingBlockEntropy_succ h Q level

/-- Every scheduled entropy threshold is bounded by the initial threshold. -/
theorem nearHalvingBlockEntropy_le_initial (h Q i : Nat) :
    nearHalvingBlockEntropy h Q i ≤ nearHalvingBlockEntropy h Q 0 :=
  Internal.nearHalvingBlockEntropy_le_initial h Q i

/-- The final entropy threshold is the depth-adjusted leaf reserve. -/
theorem nearHalvingBlockEntropy_last (h Q : Nat) :
    nearHalvingBlockEntropy h Q h = (8 * h + 8) * Q :=
  Internal.nearHalvingBlockEntropy_last h Q

/-- Every executed block holds its entropy and fits within the initial width. -/
theorem nearHalvingBlockWidth_bounds (N h Q E : Nat) (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (reserve : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q)
    {i : Nat} (level : i ≤ h) :
    nearHalvingBlockEntropy h Q i ≤ nearHalvingBlockWidth N h Q E i ∧
      nearHalvingBlockWidth N h Q E i ≤ N :=
  Internal.nearHalvingBlockWidth_bounds N h Q E capacity reserve level

/-- The global reserve certifies both entropy inequalities at every split. -/
theorem nearHalvingBlock_split_budget (N h Q E : Nat) (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (reserve : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q)
    {i : Nat} (level : i < h) :
    nearHalvingBlockEntropy h Q (i + 1) ≤ nearHalvingBlockWidth N h Q E (i + 1) ∧
      nearHalvingBlockWidth N h Q E (i + 1) + nearHalvingBlockEntropy h Q (i + 1) + E ≤
        nearHalvingBlockEntropy h Q i :=
  Internal.nearHalvingBlock_split_budget N h Q E capacity reserve level

/-- A supplied upper bound on the initial budget certifies all split inequalities. -/
theorem nearHalvingBlock_split_budget_of_bound (N h Q E T : Nat)
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (common : explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E ≤ T)
    (reserve : 12 * (nearHalvingBlockRate h + 1) * T + 4 * E ≤ Q) {i : Nat} (level : i < h) :
    nearHalvingBlockEntropy h Q (i + 1) ≤ nearHalvingBlockWidth N h Q E (i + 1) ∧
      nearHalvingBlockWidth N h Q E (i + 1) + nearHalvingBlockEntropy h Q (i + 1) + E ≤
        nearHalvingBlockEntropy h Q i :=
  Internal.nearHalvingBlock_split_budget_of_bound N h Q E T capacity common reserve level

/-- One reserve unit pays the final one-shot extractor entropy loss. -/
theorem nearHalvingBlockLeafLength_budget (h Q E : Nat) (reserve : 2 * E ≤ Q) :
    nearHalvingBlockLeafLength h Q + 2 * E ≤ nearHalvingBlockEntropy h Q h :=
  Internal.nearHalvingBlockLeafLength_budget h Q E reserve

/-- The aggregate entropy has an exact expression at every executed level. -/
theorem nearHalvingBlockEntropy_mass (h Q : Nat) {i : Nat} (level : i ≤ h) :
    2 ^ i * nearHalvingBlockEntropy h Q i = 2 ^ h * (8 * h + 8 + (h - i)) * Q :=
  Internal.nearHalvingBlockEntropy_mass h Q level

/-- The sum of the scheduled entropy thresholds never exceeds the initial entropy. -/
theorem nearHalvingBlockEntropy_mass_le (h Q : Nat) {i : Nat} (level : i ≤ h) :
    2 ^ i * nearHalvingBlockEntropy h Q i ≤ nearHalvingBlockEntropy h Q 0 :=
  Internal.nearHalvingBlockEntropy_mass_le h Q level

/-- The initial logarithmic budget bounds every actual internal field seed. -/
theorem nearHalvingBlockSeedWidth_le (N h Q E : Nat)
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (reserve : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q)
    {i : Nat} (level : i ≤ h) :
    nearHalvingBlockSeedWidth N h Q E i ≤
      6 * (nearHalvingBlockRate h + 1) *
        explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E :=
  Internal.nearHalvingBlockSeedWidth_le N h Q E capacity reserve level

/-- All blocks together occupy at most twice the initial width. -/
theorem nearHalvingBlock_payload_le (N h Q E : Nat) (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (reserve : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q)
    {i : Nat} (level : i ≤ h) : 2 ^ i * nearHalvingBlockWidth N h Q E i ≤ 2 * N :=
  Internal.nearHalvingBlock_payload_le N h Q E capacity reserve level

/-- Positive reserve bounds the number of blocks independently of their widths. -/
theorem nearHalvingBlock_count_le (h Q : Nat) (positive : 0 < Q) {i : Nat} (level : i ≤ h) :
    2 ^ i ≤ nearHalvingBlockEntropy h Q 0 :=
  Internal.nearHalvingBlock_count_le h Q positive level

/-- The complete seed bound includes every internal seed and the shared final pair. -/
theorem nearHalvingBlockSeedBits_le (N h Q E : Nat) (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (reserve : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q) :
    nearHalvingBlockSeedBits N h Q E ≤
      h * (6 * (nearHalvingBlockRate h + 1) *
        explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E) +
        (84 * (explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 1) +
          18 * nearHalvingBlockLeafLength h Q + 24 * E + 6) :=
  Internal.nearHalvingBlockSeedBits_le N h Q E capacity reserve

/-- A common logarithmic budget gives a direct bound on the complete seed. -/
theorem nearHalvingBlockSeedBits_le_of_bound (N h Q E T : Nat)
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (common : explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E ≤ T)
    (reserve : 12 * (nearHalvingBlockRate h + 1) * T + 4 * E ≤ Q) :
    nearHalvingBlockSeedBits N h Q E ≤
      h * (6 * (nearHalvingBlockRate h + 1) * T) +
        (84 * (T + 1) + 18 * nearHalvingBlockLeafLength h Q + 24 * E + 6) :=
  Internal.nearHalvingBlockSeedBits_le_of_bound N h Q E T capacity common reserve

/-- Exact accounting relates total output bits to the initial entropy. -/
theorem nearHalvingBlockOutputBits_accounting (h Q : Nat) :
    9 * nearHalvingBlockOutputBits h Q + 2 ^ h * Q = 8 * nearHalvingBlockEntropy h Q 0 :=
  Internal.nearHalvingBlockOutputBits_accounting h Q

/-- Total output has at least seven eighths of the initial entropy, without division. -/
theorem nearHalvingBlockOutputBits_lower (h Q : Nat) :
    7 * nearHalvingBlockEntropy h Q 0 ≤ 8 * nearHalvingBlockOutputBits h Q :=
  Internal.nearHalvingBlockOutputBits_lower h Q

end Algebraic.Cutwidth.Extractor
