/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.DirectProduct
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Uhlig's two-copy recovery code

This file formalizes the exact combinatorial core of the section "The
two-copy construction as disjoint recovery" in the
[Boolean mass-production manuscript](https://github.com/SamuelSchlesinger/boolean-mass-production).

For a nonempty family `f_0, ..., f_last`, the resource family is

* `g_0 = f_0`,
* `g_j = f_(j - 1) + f_j` at an interior boundary, and
* `g_(last + 1) = f_last`.

Addition is kept abstract. The recovery proof assumes explicitly that every
element is self-inverse, rather than introducing a typeclass instance. For
Boolean-valued functions, Mathlib's existing Boolean-ring addition is XOR.

Each target has a prefix and a suffix recovery set. The file proves both
recovery identities, proves the relevant sets disjoint for ordered requests,
and packages the comparator choice for requests arriving in either order.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

open scoped BigOperators

/-- The `last + 2` resource values associated with `last + 1` source values.
The parameter is the final source index, so the family is nonempty without a
separate positivity assumption. -/
def uhligResource
    [Add A]
    (values : Fin (last + 1) -> A) : Fin (last + 2) -> A :=
  Fin.cases (values 0) fun tail =>
    Fin.lastCases (values (Fin.last last))
      (fun index => values index.castSucc + values index.succ) tail

@[simp] theorem uhligResource_zero
    [Add A]
    (values : Fin (last + 1) -> A) :
    uhligResource values 0 = values 0 := rfl

theorem uhligResource_interior
    [Add A]
    (values : Fin (last + 1) -> A)
    (index : Fin last) :
    uhligResource values index.succ.castSucc =
      values index.castSucc + values index.succ := by
  simp [uhligResource]

@[simp] theorem uhligResource_last
    [Add A]
    (values : Fin (last + 1) -> A) :
    uhligResource values (Fin.last (last + 1)) =
      values (Fin.last last) := by
  unfold uhligResource
  rw [show Fin.last (last + 1) = (Fin.last last).succ by
    apply Fin.ext
    simp]
  rw [Fin.cases_succ, Fin.lastCases_last]

/-- The prefix representation of one source coordinate. -/
def uhligPrefixSet
    (target : Fin (last + 1)) : Finset (Fin (last + 2)) :=
  Finset.Iic target.castSucc

/-- The suffix representation of one source coordinate. -/
def uhligSuffixSet
    (target : Fin (last + 1)) : Finset (Fin (last + 2)) :=
  Finset.Ioi target.castSucc

@[simp] theorem mem_uhligPrefixSet
    (resource : Fin (last + 2))
    (target : Fin (last + 1)) :
    resource ∈ uhligPrefixSet target <-> resource.val <= target.val := by
  simp [uhligPrefixSet, Fin.le_def]

@[simp] theorem mem_uhligSuffixSet
    (resource : Fin (last + 2))
    (target : Fin (last + 1)) :
    resource ∈ uhligSuffixSet target <-> target.val < resource.val := by
  simp [uhligSuffixSet, Fin.lt_def]

/-- A prefix through `left` is disjoint from a suffix strictly after `right`
whenever `left <= right`. This is the scheduling invariant in Uhlig's
two-copy construction. -/
theorem uhligPrefixSet_disjoint_uhligSuffixSet
    {left right : Fin (last + 1)}
    (ordered : left <= right) :
    Disjoint (uhligPrefixSet left) (uhligSuffixSet right) := by
  rw [Finset.disjoint_left]
  intro resource inPrefix inSuffix
  rw [mem_uhligPrefixSet] at inPrefix
  rw [mem_uhligSuffixSet] at inSuffix
  exact (not_lt_of_ge (inPrefix.trans ordered)) inSuffix

/-- Prefix recovery telescopes to the requested value in any commutative
additive monoid in which every element is self-inverse. -/
theorem sum_uhligPrefixSet
    [AddCommMonoid A]
    (selfAdd : ∀ value : A, value + value = 0)
    (values : Fin (last + 1) -> A)
    (target : Fin (last + 1)) :
    ∑ resource ∈ uhligPrefixSet target, uhligResource values resource =
      values target := by
  induction target using Fin.induction with
  | zero =>
      change ∑ resource ∈ Finset.Iic (0 : Fin (last + 2)),
          uhligResource values resource = values 0
      rw [show (0 : Fin (last + 2)) = ⊥ by rfl, Finset.Iic_bot]
      rw [Finset.sum_singleton]
      rw [show (⊥ : Fin (last + 2)) = 0 by rfl, uhligResource_zero]
  | succ index ih =>
      have setStep :
          uhligPrefixSet index.succ =
            insert index.succ.castSucc (uhligPrefixSet index.castSucc) := by
        ext resource
        simp only [mem_uhligPrefixSet, Finset.mem_insert]
        simp only [Fin.val_succ, Fin.val_castSucc]
        constructor
        · intro bounded
          by_cases atBoundary : resource.val = index.val + 1
          · left
            apply Fin.ext
            exact atBoundary
          · right
            omega
        · intro member
          rcases member with atBoundary | bounded
          · subst resource
            exact le_rfl
          · omega
      rw [setStep, Finset.sum_insert]
      · rw [ih, uhligResource_interior]
        calc
          (values index.castSucc + values index.succ) +
                values index.castSucc =
              (values index.castSucc + values index.castSucc) +
                values index.succ := by
            ac_rfl
          _ = values index.succ := by
            rw [selfAdd, zero_add]
      · simp [uhligPrefixSet, Fin.le_def]

/-- The XOR-like sum of all resources is zero. -/
theorem sum_uhligResource_eq_zero
    [AddCommMonoid A]
    (selfAdd : ∀ value : A, value + value = 0)
    (values : Fin (last + 1) -> A) :
    ∑ resource, uhligResource values resource = 0 := by
  rw [Fin.sum_univ_castSucc]
  have initialResources :
      (∑ resource : Fin (last + 1),
          uhligResource values resource.castSucc) =
        values (Fin.last last) := by
    have recovered := sum_uhligPrefixSet selfAdd values (Fin.last last)
    rw [uhligPrefixSet, Fin.sum_Iic_castSucc] at recovered
    have lastEqTop : Fin.last last = (⊤ : Fin (last + 1)) := by
      apply Fin.ext
      simp
    simpa only [lastEqTop, Finset.Iic_top] using recovered
  rw [initialResources, uhligResource_last, selfAdd]

/-- Suffix recovery also telescopes to the requested value. -/
theorem sum_uhligSuffixSet
    [AddCommMonoid A]
    (selfAdd : ∀ value : A, value + value = 0)
    (values : Fin (last + 1) -> A)
    (target : Fin (last + 1)) :
    ∑ resource ∈ uhligSuffixSet target, uhligResource values resource =
      values target := by
  let prefixSum :=
    ∑ resource ∈ uhligPrefixSet target, uhligResource values resource
  let suffixSum :=
    ∑ resource ∈ uhligSuffixSet target, uhligResource values resource
  have disjoint :
      Disjoint (uhligPrefixSet target) (uhligSuffixSet target) :=
    uhligPrefixSet_disjoint_uhligSuffixSet le_rfl
  have unionAll :
      uhligPrefixSet target ∪ uhligSuffixSet target = Finset.univ := by
    ext resource
    simp only [Finset.mem_union, mem_uhligPrefixSet,
      mem_uhligSuffixSet, Finset.mem_univ, iff_true]
    omega
  have total :
      prefixSum + suffixSum = 0 := by
    change
      (∑ resource ∈ uhligPrefixSet target,
          uhligResource values resource) +
        (∑ resource ∈ uhligSuffixSet target,
          uhligResource values resource) = 0
    rw [← Finset.sum_union disjoint, unionAll]
    exact sum_uhligResource_eq_zero selfAdd values
  have prefixRecovers : prefixSum = values target :=
    sum_uhligPrefixSet selfAdd values target
  have equation : values target + suffixSum = 0 := by
    rw [← prefixRecovers]
    exact total
  change suffixSum = values target
  calc
    suffixSum = 0 + suffixSum := (zero_add suffixSum).symm
    _ = (values target + values target) + suffixSum := by
      rw [selfAdd]
    _ = values target + (values target + suffixSum) := by
      rw [add_assoc]
    _ = values target + 0 := by rw [equation]
    _ = values target := add_zero _

/-- Recovery sets chosen for two requests in their arrival order. The lower
request uses a prefix and the higher request uses a suffix; in the opposite
arrival order the two branches are swapped. -/
def uhligRecoveryPair
    (first second : Fin (last + 1)) :
    Finset (Fin (last + 2)) × Finset (Fin (last + 2)) :=
  if first <= second then
    (uhligPrefixSet first, uhligSuffixSet second)
  else
    (uhligSuffixSet first, uhligPrefixSet second)

/-- The recovery sets selected for any two requests are disjoint. -/
theorem uhligRecoveryPair_disjoint
    (first second : Fin (last + 1)) :
    Disjoint (uhligRecoveryPair first second).1
      (uhligRecoveryPair first second).2 := by
  by_cases ordered : first <= second
  · simpa [uhligRecoveryPair, ordered] using
      (uhligPrefixSet_disjoint_uhligSuffixSet ordered)
  · have reverseOrdered : second <= first := le_of_lt (lt_of_not_ge ordered)
    simpa [uhligRecoveryPair, ordered] using
      (uhligPrefixSet_disjoint_uhligSuffixSet reverseOrdered).symm

/-- Both sets selected by `uhligRecoveryPair` recover their corresponding
requests, in the original arrival order. -/
theorem uhligRecoveryPair_recovers
    [AddCommMonoid A]
    (selfAdd : ∀ value : A, value + value = 0)
    (values : Fin (last + 1) -> A)
    (first second : Fin (last + 1)) :
    (∑ resource ∈ (uhligRecoveryPair first second).1,
        uhligResource values resource) = values first ∧
      (∑ resource ∈ (uhligRecoveryPair first second).2,
        uhligResource values resource) = values second := by
  by_cases ordered : first <= second
  · simp only [uhligRecoveryPair, ordered]
    exact ⟨sum_uhligPrefixSet selfAdd values first,
      sum_uhligSuffixSet selfAdd values second⟩
  · simp only [uhligRecoveryPair, ordered]
    exact ⟨sum_uhligSuffixSet selfAdd values first,
      sum_uhligPrefixSet selfAdd values second⟩

/-- Uhlig's complete two-request invariant: the selected representations are
resource-disjoint and recover both requested values. -/
theorem uhlig_two_copy_disjoint_recovery
    [AddCommMonoid A]
    (selfAdd : ∀ value : A, value + value = 0)
    (values : Fin (last + 1) -> A)
    (first second : Fin (last + 1)) :
    Disjoint (uhligRecoveryPair first second).1
        (uhligRecoveryPair first second).2 ∧
      (∑ resource ∈ (uhligRecoveryPair first second).1,
          uhligResource values resource) = values first ∧
      (∑ resource ∈ (uhligRecoveryPair first second).2,
          uhligResource values resource) = values second := by
  exact ⟨uhligRecoveryPair_disjoint first second,
    uhligRecoveryPair_recovers selfAdd values first second⟩

/-- Function-valued Boolean specialization. Here resource addition is
pointwise XOR, exactly as in the manuscript. -/
theorem uhligBoolean_two_copy_disjoint_recovery
    (values : Fin (last + 1) -> Z -> Bool)
    (first second : Fin (last + 1)) :
    Disjoint (uhligRecoveryPair first second).1
        (uhligRecoveryPair first second).2 ∧
      (∑ resource ∈ (uhligRecoveryPair first second).1,
          uhligResource values resource) = values first ∧
      (∑ resource ∈ (uhligRecoveryPair first second).2,
          uhligResource values resource) = values second := by
  apply uhlig_two_copy_disjoint_recovery
  intro function
  funext input
  change (function input + function input : Bool) = 0
  exact neg_add_cancel _

end MassProduction
end Algebraic
