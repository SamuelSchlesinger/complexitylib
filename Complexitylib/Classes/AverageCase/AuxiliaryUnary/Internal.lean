/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.AuxiliaryUnary.Defs
import Complexitylib.Classes.AverageCase.FiniteEnsemble.Internal

/-!
# The auxiliary-unary distribution -- proof internals

This layer proves the exact shape and finite counting laws of Hirahara's
auxiliary-unary distribution.
-/


public section

namespace Complexity

namespace AuxiliaryUnarySeed

theorem split_lt_internal {m : ℕ} (hm : 0 < m)
    (seed : AuxiliaryUnarySeed m) : seed.split < m := by
  have hsplit := seed.1.isLt
  simpa [split, Nat.max_eq_right (Nat.succ_le_iff.mpr hm)] using hsplit

theorem binary_length_internal {m : ℕ}
    (seed : AuxiliaryUnarySeed m) : seed.binary.length = seed.split := by
  simp [binary]

theorem unary_length_internal {m : ℕ}
    (seed : AuxiliaryUnarySeed m) : seed.unary.length = m - seed.split := by
  simp [unary]

theorem unary_length_pos_internal {m : ℕ} (hm : 0 < m)
    (seed : AuxiliaryUnarySeed m) : 0 < seed.unary.length := by
  rw [unary_length_internal]
  have hsplit := split_lt_internal hm seed
  omega

theorem component_length_sum_internal {m : ℕ}
    (seed : AuxiliaryUnarySeed m) :
    seed.binary.length + seed.unary.length = m := by
  rw [binary_length_internal, unary_length_internal,
    Nat.add_sub_of_le seed.splitLe]

theorem unpair?_sample_internal {m : ℕ}
    (seed : AuxiliaryUnarySeed m) :
    unpair? seed.sample = some (seed.binary, seed.unary) := by
  simp [sample]

theorem card_internal (m : ℕ) :
    Fintype.card (AuxiliaryUnarySeed m) = Nat.max 1 m * 2 ^ m := by
  simp [AuxiliaryUnarySeed]

theorem prefix_probability_internal {m n : ℕ} (hn : n ≤ m)
    (x : Fin n → Bool) :
    uniformProbability
        (Finset.univ.filter fun bits : Fin m → Bool =>
          (bitBlocks hn bits).1 = x) =
      1 / (2 : ℚ) ^ n := by
  calc
    uniformProbability
        (Finset.univ.filter fun bits : Fin m → Bool =>
          (bitBlocks hn bits).1 = x) =
        uniformProbability
          (Finset.univ.filter fun blocks :
              (Fin n → Bool) × (Fin (m - n) → Bool) => blocks.1 = x) :=
      uniformProbability_equiv_internal (bitBlocks hn)
        (fun blocks : (Fin n → Bool) × (Fin (m - n) → Bool) =>
          blocks.1 = x)
    _ = uniformProbability
          (Finset.univ.filter fun prefixBits : Fin n → Bool => prefixBits = x) *
        uniformProbability
          (Finset.univ.filter fun _suffix : Fin (m - n) → Bool => True) := by
      simpa only [and_true] using
        (uniformProbability_product_internal
          (fun prefixBits : Fin n → Bool => prefixBits = x)
          (fun _suffix : Fin (m - n) → Bool => True))
    _ = 1 / (2 : ℚ) ^ n := by
      rw [uniformProbability_eq_internal,
        show Finset.univ.filter (fun _suffix : Fin (m - n) → Bool => True) =
          Finset.univ by simp,
        uniformProbability_univ_internal, mul_one, card_finArrowBool]
      norm_cast

theorem prefix_event_probability_internal {m n : ℕ} (hn : n ≤ m)
    (event : Finset (Fin n → Bool)) :
    uniformProbability
        (Finset.univ.filter fun bits : Fin m → Bool =>
          (bitBlocks hn bits).1 ∈ event) =
      eventProb event := by
  calc
    uniformProbability
        (Finset.univ.filter fun bits : Fin m → Bool =>
          (bitBlocks hn bits).1 ∈ event) =
        uniformProbability
          (Finset.univ.filter fun blocks :
              (Fin n → Bool) × (Fin (m - n) → Bool) => blocks.1 ∈ event) :=
      uniformProbability_equiv_internal (bitBlocks hn)
        (fun blocks : (Fin n → Bool) × (Fin (m - n) → Bool) =>
          blocks.1 ∈ event)
    _ = uniformProbability
          (Finset.univ.filter fun prefixBits : Fin n → Bool => prefixBits ∈ event) *
        uniformProbability
          (Finset.univ.filter fun _suffix : Fin (m - n) → Bool => True) := by
      simpa only [and_true] using
        (uniformProbability_product_internal
          (fun prefixBits : Fin n → Bool => prefixBits ∈ event)
          (fun _suffix : Fin (m - n) → Bool => True))
    _ = eventProb event := by
      rw [show Finset.univ.filter
          (fun prefixBits : Fin n → Bool => prefixBits ∈ event) = event by
            ext
            simp,
        show Finset.univ.filter (fun _suffix : Fin (m - n) → Bool => True) =
          Finset.univ by simp,
        uniformProbability_univ_internal, mul_one]
      simp only [uniformProbability, eventProb, card_finArrowBool]
      norm_cast

theorem split_prefix_event_probability_internal {m : ℕ}
    (event : ∀ n, Finset (Fin n → Bool)) :
    uniformProbability
        (Finset.univ.filter fun seed : (Fin m) × (Fin m → Bool) =>
          (bitBlocks (Nat.le_of_lt seed.1.isLt) seed.2).1 ∈
            event seed.1.val) =
      (1 / (m : ℚ)) * ∑ n : Fin m, eventProb (event n.val) := by
  let selected : Finset ((Fin m) × (Fin m → Bool)) :=
    Finset.univ.filter fun seed =>
      (bitBlocks (Nat.le_of_lt seed.1.isLt) seed.2).1 ∈ event seed.1.val
  have hmaps : (selected : Set ((Fin m) × (Fin m → Bool))).MapsTo
      Prod.fst ((Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
    intro seed _hseed
    simp
  rw [show Finset.univ.filter
      (fun seed : (Fin m) × (Fin m → Bool) =>
        (bitBlocks (Nat.le_of_lt seed.1.isLt) seed.2).1 ∈
          event seed.1.val) = selected from rfl,
    uniformProbability_eq_sum_fiberwise_internal
      selected Finset.univ Prod.fst hmaps]
  have hfiber (n : Fin m) :
      uniformProbability (selected.filter fun seed => seed.1 = n) =
        (1 / (m : ℚ)) * eventProb (event n.val) := by
    rw [show selected.filter (fun seed => seed.1 = n) =
        Finset.univ.filter (fun seed : (Fin m) × (Fin m → Bool) =>
          seed.1 = n ∧
            (bitBlocks (Nat.le_of_lt n.isLt) seed.2).1 ∈ event n.val) by
      ext seed
      simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hmember, hsplit⟩
        subst n
        exact ⟨rfl, hmember⟩
      · rintro ⟨hsplit, hmember⟩
        subst n
        exact ⟨hmember, rfl⟩]
    rw [uniformProbability_product_internal
      (fun splitIndex : Fin m => splitIndex = n)
      (fun bits : Fin m → Bool =>
        (bitBlocks (Nat.le_of_lt n.isLt) bits).1 ∈ event n.val),
      uniformProbability_eq_internal n,
      Fintype.card_fin,
      prefix_event_probability_internal (Nat.le_of_lt n.isLt)]
  simp_rw [hfiber]
  rw [← Finset.mul_sum]

theorem split_prefix_probability_internal {m n : ℕ} (hn : n < m)
    (x : Fin n → Bool) :
    uniformProbability
        (Finset.univ.filter fun seed : AuxiliaryUnarySeed m =>
          seed.1.val = n ∧
            (bitBlocks (Nat.le_of_lt hn) seed.2).1 = x) =
      1 / ((m : ℚ) * (2 : ℚ) ^ n) := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hn
  have hmax : Nat.max 1 m = m :=
    Nat.max_eq_right (Nat.succ_le_iff.mpr hm)
  let selected : Fin (Nat.max 1 m) := ⟨n, by simpa [hmax] using hn⟩
  have hsplit :
      uniformProbability
          (Finset.univ.filter fun i : Fin (Nat.max 1 m) => i.val = n) =
        1 / (m : ℚ) := by
    rw [show
      Finset.univ.filter (fun i : Fin (Nat.max 1 m) => i.val = n) =
        {selected} by
      ext i
      simp [selected, Fin.ext_iff]]
    simp [uniformProbability, hmax]
  calc
    uniformProbability
        (Finset.univ.filter fun seed : AuxiliaryUnarySeed m =>
          seed.1.val = n ∧
            (bitBlocks (Nat.le_of_lt hn) seed.2).1 = x) =
        uniformProbability
            (Finset.univ.filter fun i : Fin (Nat.max 1 m) => i.val = n) *
          uniformProbability
            (Finset.univ.filter fun bits : Fin m → Bool =>
              (bitBlocks (Nat.le_of_lt hn) bits).1 = x) := by
      exact uniformProbability_product_internal
        (fun i : Fin (Nat.max 1 m) => i.val = n)
        (fun bits : Fin m → Bool =>
          (bitBlocks (Nat.le_of_lt hn) bits).1 = x)
    _ = (1 / (m : ℚ)) * (1 / (2 : ℚ) ^ n) := by
      rw [hsplit, prefix_probability_internal]
    _ = 1 / ((m : ℚ) * (2 : ℚ) ^ n) := by
      field_simp

theorem sample_eq_pair_iff_internal {m n : ℕ} (hn : n < m)
    (x : Fin n → Bool) (seed : AuxiliaryUnarySeed m) :
    seed.sample = pair (List.ofFn x) (List.replicate (m - n) true) ↔
      seed.1.val = n ∧
        (bitBlocks (Nat.le_of_lt hn) seed.2).1 = x := by
  constructor
  · intro hsample
    obtain ⟨hbinary, _hunary⟩ := pair_inj hsample
    have hlength := congrArg List.length hbinary
    have hsplit : seed.split = n := by
      simpa only [binary_length_internal, List.length_ofFn] using hlength
    subst n
    constructor
    · rfl
    · have hbits : seed.binaryBits = x := by
        apply List.ofFn_injective
        simpa only [binary] using hbinary
      simpa only [binaryBits] using hbits
  · rintro ⟨hsplit, hbits⟩
    have hsplit' : seed.split = n := by
      simpa only [split] using hsplit
    subst n
    unfold sample
    apply congrArg₂ pair
    · unfold binary
      apply List.ofFn_inj.mpr
      simp only [binaryBits]
      exact hbits
    · rfl

end AuxiliaryUnarySeed

namespace FiniteEnsemble

theorem mass_auxiliaryUnary_pair_internal {m n : ℕ} (hn : n < m)
    (x : Fin n → Bool) :
    auxiliaryUnary.mass m
        (pair (List.ofFn x) (List.replicate (m - n) true)) =
      1 / ((m : ℚ) * (2 : ℚ) ^ n) := by
  let := auxiliaryUnary.seedFintype m
  let := auxiliaryUnary.seedDecidableEq m
  change
    uniformProbability
        (Finset.univ.filter fun seed : AuxiliaryUnarySeed m =>
          seed.sample = pair (List.ofFn x) (List.replicate (m - n) true)) =
      1 / ((m : ℚ) * (2 : ℚ) ^ n)
  rw [show
    Finset.univ.filter
        (fun seed : AuxiliaryUnarySeed m =>
          seed.sample = pair (List.ofFn x) (List.replicate (m - n) true)) =
      Finset.univ.filter
        (fun seed : AuxiliaryUnarySeed m =>
          seed.1.val = n ∧
            (AuxiliaryUnarySeed.bitBlocks
              (Nat.le_of_lt hn) seed.2).1 = x) by
    ext seed
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact AuxiliaryUnarySeed.sample_eq_pair_iff_internal hn x seed]
  exact AuxiliaryUnarySeed.split_prefix_probability_internal hn x

end FiniteEnsemble

end Complexity
