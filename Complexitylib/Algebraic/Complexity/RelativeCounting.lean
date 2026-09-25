/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Complexity.Relative
public import Complexitylib.Algebraic.LowerBound.Counting.Sharp
public import Mathlib.Data.Rat.Cast.Order

/-!
# Counting circuits relative to a supplied family

For any fixed `sources : X → Fin n → U`, each circuit description determines
at most one target on `X`. The ordered-description bound therefore requires
no finiteness of `X` or `U`. A finite carrier additionally permits reuse of
the library's factorial-improved semantic count. These are versions of the
counting method in Boyack's Lemma 2.2.2 with explicit circuit conventions and
arbitrary finite arities; its displayed numerical bound is not copied.

The finite-menu and rational-fraction bounds apply to any finite target
family. Interpreting a fraction as a uniform probability requires that family
to be nonempty. Sources are fixed before sampling the target, though a choice
from a fixed finite menu can be made afterward.
-/

@[expose] public section

open Algebraic
open scoped Classical

namespace Cslib.Circuits.Circuit

variable {X : Type*}

/-- Targets obtainable within a gate budget from a fixed source family. -/
noncomputable def relativeFunctionsAtMost
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) (sources : X → Fin n → U)
    (m budget : Nat) : Finset (X → Fin m → U) :=
  Finset.univ.image fun circuit : BoundedCircuit σ n m budget =>
    fun x => circuit.eval interpretation (sources x)

/-- The counted set is exactly the set of targets within the relative budget. -/
theorem mem_relativeFunctionsAtMost_iff
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) (sources : X → Fin n → U)
    (target : X → Fin m → U) (budget : Nat) :
    target ∈ relativeFunctionsAtMost interpretation sources m budget ↔
      relativeGateComplexity interpretation target sources ≤ budget := by
  rw [relativeGateComplexity_le_iff]
  constructor
  · intro present
    obtain ⟨circuit, _, equal⟩ := Finset.mem_image.mp present
    exact ⟨circuit.2.1, circuit.2.2.le.trans (Nat.le_of_lt_succ circuit.1.isLt),
      fun x => congrFun equal x⟩
  · rintro ⟨circuit, bounded, computes⟩
    exact Finset.mem_image.mpr
      ⟨⟨⟨circuit.size, Nat.lt_succ_iff.mpr bounded⟩, circuit, rfl⟩,
        Finset.mem_univ _, funext computes⟩

/-- Fixed supplied functions produce at most one target per circuit description. -/
theorem card_relativeFunctionsAtMost_le
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) (sources : X → Fin n → U)
    (m budget : Nat) :
    (relativeFunctionsAtMost interpretation sources m budget).card ≤
      σ.orderedBudget n m budget :=
  Finset.card_image_le.trans_eq BoundedCircuit.card

/-- Relative easy functions are an image of ordinary easy functions. -/
theorem relativeFunctionsAtMost_eq_image
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) (sources : X → Fin n → U)
    (m budget : Nat) :
    relativeFunctionsAtMost interpretation sources m budget =
      (functionsAtMost interpretation n m budget).image (fun h => h ∘ sources) := by
  simp only [relativeFunctionsAtMost, functionsAtMost, Finset.image_image,
    BoundedCircuit.eval, Function.comp_def]

/-- The factorial-improved count also bounds relative complexity. It counts
semantic total extensions before restricting them to the supplied values. -/
theorem card_relativeFunctionsAtMost_le_sharpBudget
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) (sources : X → Fin n → U)
    (m budget : Nat) :
    (relativeFunctionsAtMost interpretation sources m budget).card ≤
      σ.sharpBudget n m budget := by
  rw [relativeFunctionsAtMost_eq_image]
  exact Finset.card_image_le.trans
    (card_functionsAtMost_le_sharpBudget interpretation n m budget)

/-- Either counting bound may be better at a particular finite budget, so
their minimum is also a valid bound. -/
theorem card_relativeFunctionsAtMost_le_min
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) (sources : X → Fin n → U)
    (m budget : Nat) :
    (relativeFunctionsAtMost interpretation sources m budget).card ≤
      min (σ.orderedBudget n m budget) (σ.sharpBudget n m budget) :=
  le_min (card_relativeFunctionsAtMost_le interpretation sources m budget)
    (card_relativeFunctionsAtMost_le_sharpBudget interpretation sources m budget)

/-- Any upper bound on the easy set gives a hard target in a larger family. -/
theorem exists_relative_hard_in_family_of_card_lt
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) (sources : X → Fin n → U)
    (family : Finset (X → Fin m → U)) (budget : Nat)
    (large : (relativeFunctionsAtMost interpretation sources m budget).card < family.card) :
    ∃ target ∈ family, (budget : ℕ∞) < relativeGateComplexity interpretation target sources := by
  obtain ⟨target, member, absent⟩ := Finset.exists_mem_notMem_of_card_lt_card large
  exact ⟨target, member, lt_of_not_ge fun easy => absent
    ((mem_relativeFunctionsAtMost_iff interpretation sources target budget).mpr easy)⟩

/-- Ordered-description counting against any finite target family. -/
theorem exists_relative_hard_in_family
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) (sources : X → Fin n → U)
    (family : Finset (X → Fin m → U)) (budget : Nat)
    (large : σ.orderedBudget n m budget < family.card) :
    ∃ target ∈ family, (budget : ℕ∞) < relativeGateComplexity interpretation target sources :=
  exists_relative_hard_in_family_of_card_lt interpretation sources family budget
    ((card_relativeFunctionsAtMost_le interpretation sources m budget).trans_lt large)

/-- Factorial-improved counting against any finite target family. -/
theorem exists_relative_hard_in_family_sharp
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) (sources : X → Fin n → U)
    (family : Finset (X → Fin m → U)) (budget : Nat)
    (large : σ.sharpBudget n m budget < family.card) :
    ∃ target ∈ family, (budget : ℕ∞) < relativeGateComplexity interpretation target sources :=
  exists_relative_hard_in_family_of_card_lt interpretation sources family budget
    ((card_relativeFunctionsAtMost_le_sharpBudget interpretation sources m budget).trans_lt large)

/-- A sufficiently large family contains a target hard for every source
family in a fixed finite menu. -/
theorem exists_relative_hard_for_all_sources
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) (menu : Finset (X → Fin n → U))
    (family : Finset (X → Fin m → U)) (budget : Nat)
    (large : menu.card * σ.orderedBudget n m budget < family.card) :
    ∃ target ∈ family, ∀ sources ∈ menu,
      (budget : ℕ∞) < relativeGateComplexity interpretation target sources := by
  let easy := menu.biUnion fun sources => relativeFunctionsAtMost interpretation sources m budget
  have small : easy.card ≤ menu.card * σ.orderedBudget n m budget := by
    calc
      easy.card ≤ ∑ sources ∈ menu,
          (relativeFunctionsAtMost interpretation sources m budget).card := Finset.card_biUnion_le
      _ ≤ ∑ _sources ∈ menu, σ.orderedBudget n m budget :=
        Finset.sum_le_sum fun sources _ => card_relativeFunctionsAtMost_le interpretation sources m budget
      _ = _ := by simp
  obtain ⟨target, member, absent⟩ := Finset.exists_mem_notMem_of_card_lt_card (small.trans_lt large)
  refine ⟨target, member, fun sources inMenu => lt_of_not_ge fun bounded => absent ?_⟩
  exact Finset.mem_biUnion.mpr ⟨sources, inMenu,
    (mem_relativeFunctionsAtMost_iff interpretation sources target budget).mpr bounded⟩

/-- Exact rational bound for the easy fraction of a finite target family. -/
theorem relative_easy_fraction_le
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) (sources : X → Fin n → U)
    (family : Finset (X → Fin m → U)) (budget : Nat) :
    ((family ∩ relativeFunctionsAtMost interpretation sources m budget).card : ℚ) / family.card ≤
      (σ.orderedBudget n m budget : ℚ) / family.card := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans
    (card_relativeFunctionsAtMost_le interpretation sources m budget)

/-- The factorial-improved count also bounds the uniform fraction. -/
theorem relative_easy_fraction_le_sharp
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) (sources : X → Fin n → U)
    (family : Finset (X → Fin m → U)) (budget : Nat) :
    ((family ∩ relativeFunctionsAtMost interpretation sources m budget).card : ℚ) / family.card ≤
      (σ.sharpBudget n m budget : ℚ) / family.card := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans
    (card_relativeFunctionsAtMost_le_sharpBudget interpretation sources m budget)

end Cslib.Circuits.Circuit

namespace Algebraic.Circuit

export Cslib.Circuits.Circuit
  (relativeFunctionsAtMost mem_relativeFunctionsAtMost_iff card_relativeFunctionsAtMost_le
   relativeFunctionsAtMost_eq_image card_relativeFunctionsAtMost_le_sharpBudget
   card_relativeFunctionsAtMost_le_min
   exists_relative_hard_in_family_of_card_lt exists_relative_hard_in_family
   exists_relative_hard_in_family_sharp exists_relative_hard_for_all_sources
   relative_easy_fraction_le relative_easy_fraction_le_sharp)

end Algebraic.Circuit
