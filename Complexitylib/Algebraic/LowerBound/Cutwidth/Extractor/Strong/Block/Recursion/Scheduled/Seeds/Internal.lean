/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Explicit
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Counting and bounding the scheduled field seeds

The nested seed tuple has one factor for each retained field seed. Exact
finite-field cardinalities turn this product into a power of two. Sparse
rounding and the finite width schedule then bound its exponent.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem card_binaryField (s : Nat) [Fintype (AdjoinRoot (binaryModulus s))] :
    Fintype.card (AdjoinRoot (binaryModulus s)) = 2 ^ (2 * 3 ^ s) := by
  simpa only [Nat.card_eq_fintype_card] using card_adjoinRoot_binaryModulus s

private theorem card_recursiveSeeds {Earlier : Type} {Fresh : Nat → Type}
    [Fintype Earlier] [∀ i, Fintype (Fresh i)] (initial : Nat) (bits : Nat → Nat)
    (first : Fintype.card Earlier = 2 ^ initial)
    (each : ∀ i, Fintype.card (Fresh i) = 2 ^ bits i) (h : Nat) :
    Fintype.card (RecursiveSeeds Earlier Fresh h) =
      2 ^ (initial + (Finset.range h).sum bits) := by
  induction h with
  | zero =>
    calc
      Fintype.card (RecursiveSeeds Earlier Fresh 0) = Fintype.card Earlier :=
        Fintype.card_congr (Equiv.refl Earlier)
      _ = _ := by simpa only [Finset.sum_range_zero, Nat.add_zero] using first
  | succ h ih =>
    change Fintype.card (RecursiveSeeds Earlier Fresh h × Fresh h) = _
    rw [Fintype.card_prod, ih, each, ← Nat.pow_add, Finset.sum_range_succ, Nat.add_assoc]

theorem card_scheduledBlockSeeds (n h Q E ell : Nat)
    [∀ s, Fintype (AdjoinRoot (binaryModulus s))] :
    Fintype.card (RecursiveSeeds (ScheduledInitialSeed n h Q E)
      (ScheduledLevelSeed n h Q E) h × ScheduledFinalSeed n h Q E ell) =
      2 ^ scheduledBlockSeedBits n h Q E ell := by
  have initial : Fintype.card (ScheduledInitialSeed n h Q E) =
      2 ^ sparseFieldBits 1 (explicitCondenserBudget n (recursiveBlockEntropy h Q 0) E) :=
    card_binaryField _
  have each (i : Nat) : Fintype.card (ScheduledLevelSeed n h Q E i) =
      2 ^ recursiveBlockSeedWidth (scheduledBlockInitialWidth n h Q E) h Q E i :=
    card_binaryField _
  rw [Fintype.card_prod, card_recursiveSeeds _ _ initial each]
  change 2 ^ _ *
    Fintype.card (AdjoinRoot (binaryModulus (oneShotCondenserExponent _ ell E)) ×
      AdjoinRoot (binaryModulus (oneShotHashExponent _ ell E))) = _
  rw [Fintype.card_prod, card_binaryField, card_binaryField, ← Nat.pow_add, ← Nat.pow_add]
  rfl

private theorem clog_two_mul_le (a b : Nat) :
    Nat.clog 2 (a * b) ≤ Nat.clog 2 a + Nat.clog 2 b := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by decide) a) (Nat.le_pow_clog (by decide) b)

private theorem initial_input_budget_le (n L E h : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) :
    explicitCondenserBudget n
      (recursiveBlockEntropy h (recursiveBlockReserve L E) 0) E ≤
      E + L + 2 * h + Nat.clog 2 (L + E + 1) + 18 := by
  let k := recursiveBlockEntropy h (recursiveBlockReserve L E) 0
  have first := clog_two_mul_le 9 (n + 1)
  have second := clog_two_mul_le (9 * (n + 1)) (k + 1)
  have nine : Nat.clog 2 9 = 4 := by decide
  have entropy := recursiveBlockEntropy_zero_clog_le L E h
  change Nat.clog 2 (k + 1) ≤ _ at entropy
  change explicitCondenserBudget n k E ≤ _
  unfold explicitCondenserBudget
  lia

private theorem final_seed_bits_le (n L E h : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (depth : h ≤ L) :
    let Q := recursiveBlockReserve L E
    let initial := scheduledBlockInitialWidth n h Q E
    let width := recursiveBlockWidth initial h Q E h
    2 * 3 ^ oneShotCondenserExponent width L E +
      2 * 3 ^ oneShotHashExponent width L E ≤
      84 * (E + 4 * h + 2 * Nat.clog 2 (L + E + 1) + 64 + 1) +
        18 * L + 24 * E + 6 := by
  let Q := recursiveBlockReserve L E
  let k := recursiveBlockEntropy h Q 0
  let initial := scheduledBlockInitialWidth n h Q E
  let width := recursiveBlockWidth initial h Q E h
  change 2 * 3 ^ oneShotCondenserExponent width L E +
    2 * 3 ^ oneShotHashExponent width L E ≤ _
  have capacity : k ≤ initial :=
    (recursiveBlockInitialWidth_bounds n L E h length).1
  have reserve := recursiveBlockReserve_budget n L E h length depth
  change 3 * (24 * explicitCondenserBudget initial k E) + 6 * E ≤ 2 * Q at reserve
  have width_le : width ≤ initial :=
    (recursiveBlockWidth_bounds initial h Q E capacity reserve le_rfl).2
  have entropy_le : L + 2 * E ≤ k := by
    have bound := recursiveBlockEntropy_reserve_le h Q 0
    change Q ≤ k at bound
    dsimp [Q, recursiveBlockReserve] at bound
    lia
  have final_budget := explicitCondenserBudget_mono (E := E + 1) width_le entropy_le
  have initial_budget := recursiveBlockInitialBudget_le n L E h length
  change explicitCondenserBudget initial k E ≤ _ at initial_budget
  have increment : explicitCondenserBudget initial k (E + 1) =
      explicitCondenserBudget initial k E + 1 := by
    unfold explicitCondenserBudget
    lia
  rw [increment] at final_budget
  have field := explicitCondenser_fieldBits_le width (L + 2 * E) (E + 1) 1
  change 2 * 3 ^ oneShotCondenserExponent width L E ≤
    12 * explicitCondenserBudget width (L + 2 * E) (E + 1) at field
  have seeds := oneShotSeedBits_le width L E
  lia

theorem scheduledBlockSeedBits_le (n L E h : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (depth : h ≤ L) :
    scheduledBlockSeedBits n h (recursiveBlockReserve L E) E L ≤
      8192 * (L + (h + 1) * (E + h + Nat.clog 2 (L + E + 1) + 1)) := by
  let Q := recursiveBlockReserve L E
  let k := recursiveBlockEntropy h Q 0
  let initial := scheduledBlockInitialWidth n h Q E
  let width := recursiveBlockWidth initial h Q E h
  let T := E + 4 * h + 2 * Nat.clog 2 (L + E + 1) + 64
  have capacity : k ≤ initial :=
    (recursiveBlockInitialWidth_bounds n L E h length).1
  have reserve := recursiveBlockReserve_budget n L E h length depth
  change 3 * (24 * explicitCondenserBudget initial k E) + 6 * E ≤ 2 * Q at reserve
  have budget : explicitCondenserBudget initial k E ≤ T :=
    recursiveBlockInitialBudget_le n L E h length
  have first : sparseFieldBits 1 (explicitCondenserBudget n k E) ≤
      12 * (E + L + 2 * h + Nat.clog 2 (L + E + 1) + 18) := by
    have rounding := explicitCondenser_fieldBits_le n k E 1
    have input := initial_input_budget_le n L E h length
    change explicitCondenserBudget n k E ≤ _ at input
    lia
  have middle : (Finset.range h).sum (recursiveBlockSeedWidth initial h Q E) ≤
      h * (24 * T) := by
    calc
      _ ≤ (Finset.range h).sum (fun _ => 24 * T) := by
        apply Finset.sum_le_sum
        intro i member
        exact (recursiveBlockSeedWidth_le initial h Q E capacity reserve
          (Nat.le_of_lt (Finset.mem_range.mp member))).trans (Nat.mul_le_mul_left 24 budget)
      _ = _ := by simp
  have last : 2 * 3 ^ oneShotCondenserExponent width L E +
      2 * 3 ^ oneShotHashExponent width L E ≤ 84 * (T + 1) + 18 * L + 24 * E + 6 :=
    final_seed_bits_le n L E h length depth
  change sparseFieldBits 1 (explicitCondenserBudget n k E) +
    (Finset.range h).sum (recursiveBlockSeedWidth initial h Q E) +
    (2 * 3 ^ oneShotCondenserExponent width L E +
      2 * 3 ^ oneShotHashExponent width L E) ≤ _
  calc
    _ ≤ 12 * (E + L + 2 * h + Nat.clog 2 (L + E + 1) + 18) + h * (24 * T) +
        (84 * (T + 1) + 18 * L + 24 * E + 6) :=
      Nat.add_le_add (Nat.add_le_add first middle) last
    _ ≤ _ := by dsimp only [T]; ring_nf; lia

end Algebraic.Cutwidth.Extractor.Internal
