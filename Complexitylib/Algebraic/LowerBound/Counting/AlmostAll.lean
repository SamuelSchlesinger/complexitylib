/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Counting.FinalTerm
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Almost-all circuit lower bounds

This file isolates the density language from any particular asymptotic gate
budget. The primary predicate is division-free; the final theorem translates
it to the conventional real-valued density limit.
-/

@[expose] public section

namespace Algebraic

/-! ## Easy and hard members of a finite family -/

/-- Members of a family that are easy at internal-gate budget `G`. -/
noncomputable def _root_.Cslib.Circuits.Circuit.easyInFamily
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    (G : Nat) : Finset (Target U n m) := by
  classical
  exact family.filter fun target =>
    target ∈ Circuit.functionsAtMost interpretation n m G

export Cslib.Circuits (Circuit.easyInFamily)

/-- Members of a family requiring more than `G` internal gates. -/
noncomputable def _root_.Cslib.Circuits.Circuit.hardInFamily
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    (G : Nat) : Finset (Target U n m) := by
  classical
  exact family.filter fun target =>
    target ∉ Circuit.functionsAtMost interpretation n m G

export Cslib.Circuits (Circuit.hardInFamily)

/-- Proportion of a finite family computed within gate budget `G`. -/
noncomputable def _root_.Cslib.Circuits.Circuit.easyDensity
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    (G : Nat) : Real :=
  (Circuit.easyInFamily interpretation family G).card / family.card

export Cslib.Circuits (Circuit.easyDensity)

theorem _root_.Cslib.Circuits.Circuit.mem_hardInFamily_iff
    [Fintype σ.Op] [Fintype U]
    {interpretation : Interpretation σ U}
    {family : Finset (Target U n m)}
    {target : Target U n m} :
    target ∈ Circuit.hardInFamily interpretation family G ↔
      target ∈ family ∧
        Circuit.GateHard interpretation G target := by
  classical
  rw [Circuit.hardInFamily, Finset.mem_filter,
    Circuit.not_mem_functionsAtMost_iff]

export Cslib.Circuits (Circuit.mem_hardInFamily_iff)

theorem _root_.Cslib.Circuits.Circuit.card_easyInFamily_le_sharpBudget
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    (G : Nat) :
    (Circuit.easyInFamily interpretation family G).card ≤
      σ.sharpBudget n m G := by
  classical
  have subset : Circuit.easyInFamily interpretation family G ⊆
      Circuit.functionsAtMost interpretation n m G := by
    intro target present
    exact (Finset.mem_filter.mp present).2
  exact (Finset.card_le_card subset).trans
    (Circuit.card_functionsAtMost_le_sharpBudget interpretation n m G)

export Cslib.Circuits (Circuit.card_easyInFamily_le_sharpBudget)

/-- Quantitative almost-all theorem: at most the sharp budget can be easy. -/
theorem _root_.Cslib.Circuits.Circuit.card_family_sub_sharpBudget_le_hardInFamily
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    (G : Nat) :
    family.card - σ.sharpBudget n m G ≤
      (Circuit.hardInFamily interpretation family G).card := by
  classical
  apply tsub_le_iff_right.mpr
  have partition := Finset.card_filter_add_card_filter_not
    (s := family)
    (p := fun target =>
      target ∉ Circuit.functionsAtMost interpretation n m G)
  have partitionEqual :
      (Circuit.hardInFamily interpretation family G).card +
          (Circuit.easyInFamily interpretation family G).card = family.card := by
    simpa [Circuit.hardInFamily, Circuit.easyInFamily] using partition
  rw [← partitionEqual]
  exact Nat.add_le_add_left
    (Circuit.card_easyInFamily_le_sharpBudget interpretation family G)
    (Circuit.hardInFamily interpretation family G).card

/-! ## Division-free asymptotic density -/

export Cslib.Circuits (Circuit.card_family_sub_sharpBudget_le_hardInFamily)

/-- A sequence of easy subsets is asymptotically negligible when every fixed
multiple of its cardinality is eventually bounded by the ambient family. This
is a division-free finite-set formulation of density tending to zero. -/
def _root_.Cslib.Circuits.Circuit.AsymptoticallyAlmostAllHard
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (m : Nat)
    (family : (n : Nat) → Finset (Target U n m))
    (gateBudget : Nat → Nat) : Prop :=
  ∀ K : Nat, ∀ᶠ n in Filter.atTop,
    K * (Circuit.easyInFamily interpretation (family n) (gateBudget n)).card ≤
      (family n).card

export Cslib.Circuits (Circuit.AsymptoticallyAlmostAllHard)

/-- Generic exact asymptotic Shannon theorem. Every fixed multiple of the
sharp description budget being eventually smaller than the family implies
that the easy subfamily has density zero. -/
theorem _root_.Cslib.Circuits.Circuit.asymptoticallyAlmostAllHard_of_sharpBudget
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (m : Nat)
    (family : (n : Nat) → Finset (Target U n m))
    (gateBudget : Nat → Nat)
    (negligible : ∀ K : Nat, ∀ᶠ n in Filter.atTop,
      K * σ.sharpBudget n m (gateBudget n) ≤ (family n).card) :
    Circuit.AsymptoticallyAlmostAllHard
      interpretation m family gateBudget := by
  intro K
  filter_upwards [negligible K] with n bounded
  exact (Nat.mul_le_mul_left K
    (Circuit.card_easyInFamily_le_sharpBudget
      interpretation (family n) (gateBudget n))).trans bounded

export Cslib.Circuits (Circuit.asymptoticallyAlmostAllHard_of_sharpBudget)

/-- Analytic form of the almost-all transfer theorem. It replaces the exact
sum of integer quotients by the real final-term envelope. -/
theorem _root_.Cslib.Circuits.Circuit.asymptoticallyAlmostAllHard_of_finalTerm
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (m : Nat)
    (family : (n : Nat) → Finset (Target U n m))
    (gateBudget : Nat → Nat)
    (enoughLines : ∀ᶠ n in Filter.atTop,
      gateBudget n ≤ σ.lineCount (n + gateBudget n))
    (negligible : ∀ K : Nat, ∀ᶠ n in Filter.atTop,
      (K : Real) * σ.finalTerm n m (gateBudget n) ≤ (family n).card) :
    Circuit.AsymptoticallyAlmostAllHard
      interpretation m family gateBudget := by
  intro K
  filter_upwards [enoughLines, negligible K] with n enough bounded
  have easyBound :
      ((Circuit.easyInFamily interpretation
        (family n) (gateBudget n)).card : Real) ≤
        σ.finalTerm n m (gateBudget n) := by
    calc
      ((Circuit.easyInFamily interpretation
          (family n) (gateBudget n)).card : Real) ≤
          (σ.sharpBudget n m (gateBudget n) : Real) := by
        exact_mod_cast Circuit.card_easyInFamily_le_sharpBudget
          interpretation (family n) (gateBudget n)
      _ ≤ _ := σ.sharpBudget_cast_le_finalTerm enough
  have castBound :
      ((K * (Circuit.easyInFamily interpretation
        (family n) (gateBudget n)).card : Nat) : Real) ≤
          ((family n).card : Real) := by
    rw [Nat.cast_mul]
    calc
      (K : Real) *
          (Circuit.easyInFamily interpretation
            (family n) (gateBudget n)).card ≤
          (K : Real) * σ.finalTerm n m (gateBudget n) :=
        mul_le_mul_of_nonneg_left easyBound (Nat.cast_nonneg K)
      _ ≤ ((family n).card : Real) := bounded
  exact_mod_cast castBound

/-! ## The full target space and conventional density -/

export Cslib.Circuits (Circuit.asymptoticallyAlmostAllHard_of_finalTerm)

/-- An asymptotically negligible easy subset leaves a hard target at every
sufficiently large width, provided the ambient families are nonempty. -/
theorem _root_.Cslib.Circuits.Circuit.AsymptoticallyAlmostAllHard.eventually_exists_hard
    [Fintype σ.Op] [Fintype U]
    {interpretation : Interpretation σ U}
    {m : Nat} {family : (n : Nat) → Finset (Target U n m)}
    {gateBudget : Nat → Nat}
    (hard : Circuit.AsymptoticallyAlmostAllHard interpretation m family gateBudget)
    (nonempty : ∀ᶠ n in Filter.atTop, 0 < (family n).card) :
    ∀ᶠ n in Filter.atTop, ∃ target ∈ family n,
      Circuit.GateHard interpretation (gateBudget n) target := by
  classical
  filter_upwards [hard 2, nonempty] with n bounded positive
  have smaller : (Circuit.easyInFamily interpretation (family n) (gateBudget n)).card <
      (family n).card := by omega
  obtain ⟨target, present, notEasy⟩ := Finset.exists_mem_notMem_of_card_lt_card smaller
  refine ⟨target, present, Circuit.not_mem_functionsAtMost_iff.mp ?_⟩
  intro easy
  exact notEasy (Finset.mem_filter.mpr ⟨present, easy⟩)

export Cslib.Circuits (Circuit.AsymptoticallyAlmostAllHard.eventually_exists_hard)

/-- The complete family of `m`-output functions on `n` inputs. -/
noncomputable def _root_.Cslib.Circuits.Circuit.fullFamily
    (U : Type*) [Fintype U] (m n : Nat) : Finset (Target U n m) := by
  classical
  exact Finset.univ

export Cslib.Circuits (Circuit.fullFamily)

@[simp] theorem _root_.Cslib.Circuits.Circuit.card_fullFamily
    (U : Type*) [Fintype U] (m n : Nat) :
    (Circuit.fullFamily U m n).card = Target.count U n m := by
  classical
  rw [Circuit.fullFamily, Finset.card_univ]
  rw [Target.count, Nat.card_eq_fintype_card]

export Cslib.Circuits (Circuit.card_fullFamily)

/-- The division-free almost-all predicate implies the conventional statement
that the real-valued density of easy functions tends to zero. -/
theorem _root_.Cslib.Circuits.Circuit.AsymptoticallyAlmostAllHard.tendsto_easyDensity_zero
    [Fintype σ.Op] [Fintype U]
    {interpretation : Interpretation σ U}
    {m : Nat}
    {family : (n : Nat) → Finset (Target U n m)}
    {gateBudget : Nat → Nat}
    (hard : Circuit.AsymptoticallyAlmostAllHard
      interpretation m family gateBudget)
    (familyNonempty : ∀ᶠ n in Filter.atTop, 0 < (family n).card) :
    Filter.Tendsto
      (fun n => Circuit.easyDensity interpretation (family n) (gateBudget n))
      Filter.atTop (nhds 0) := by
  unfold Circuit.easyDensity
  rw [tendsto_order]
  constructor
  · intro lower lowerNegative
    exact Filter.Eventually.of_forall fun n =>
      lowerNegative.trans_le (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · intro upper upperPositive
    obtain ⟨K, hK⟩ := exists_nat_gt ((1 : Real) / upper)
    have KPositive : (0 : Real) < K := by
      have reciprocalPositive : (0 : Real) < 1 / upper := by positivity
      linarith
    have reciprocalSmall : (1 : Real) / K < upper := by
      rw [div_lt_iff₀ KPositive]
      have := (div_lt_iff₀ upperPositive).mp hK
      nlinarith
    filter_upwards [hard K, familyNonempty] with n bounded familyPositive
    have castBound :
        (K : Real) *
            (Circuit.easyInFamily interpretation
              (family n) (gateBudget n)).card ≤
          (family n).card := by
      exact_mod_cast bounded
    have ratioBound :
        ((Circuit.easyInFamily interpretation
          (family n) (gateBudget n)).card : Real) /
            (family n).card ≤ (1 : Real) / K := by
      rw [div_le_div_iff₀ (by exact_mod_cast familyPositive) KPositive]
      simpa [mul_comm] using castBound
    exact ratioBound.trans_lt reciprocalSmall

export Cslib.Circuits (Circuit.AsymptoticallyAlmostAllHard.tendsto_easyDensity_zero)

end Algebraic
