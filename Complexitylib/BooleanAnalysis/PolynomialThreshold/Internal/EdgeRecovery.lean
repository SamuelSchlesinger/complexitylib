/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.HilbertSchmidt
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.SignParity
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Gotsman--Linial: EdgeRecovery

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/EdgeRecovery.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# Recovering constant-sign edges from grading energy

The counting argument is separated from construction of the grading matrix.
Its hypotheses are explicit entrywise, total-energy, and distance-energy facts.
No edge-count or anticommutator conclusion is assumed.
-/

open scoped BigOperators

namespace BooleanAnalysis.PolynomialThreshold.Internal

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- A finite distance layer, also useful for weights indexed by ordered pairs. -/
def distanceShell (d : α → ℕ) (k : ℕ) : Finset α :=
  Finset.univ.filter fun a => d a = k

@[simp] theorem mem_distanceShell (d : α → ℕ) (k : ℕ) (a : α) :
    a ∈ distanceShell d k ↔ d a = k := by
  simp [distanceShell]

/-- Pointwise distance counting: distance-zero entries are the only possible
source of a deficit between total mass and distance-weighted mass. -/
theorem twice_mass_sub_neighbor_le_distance (d : α → ℕ) (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    2 * (∑ a, w a) - (∑ a ∈ distanceShell d 1, w a) ≤
      2 * (∑ a ∈ distanceShell d 0, w a) + ∑ a, (d a : ℝ) * w a := by
  have hpoint : ∀ a,
      2 * w a - (if d a = 1 then w a else 0) ≤
        2 * (if d a = 0 then w a else 0) + (d a : ℝ) * w a := by
    intro a
    by_cases h0 : d a = 0
    · simp [h0]
    by_cases h1 : d a = 1
    · rw [ite_eq_left h1, ite_eq_right h0, h1]
      norm_num
      linarith
    have h2 : 2 ≤ d a := by omega
    have h2R : (2 : ℝ) ≤ (d a : ℝ) := by exact_mod_cast h2
    simpa only [ite_eq_right h0, ite_eq_right h1, sub_zero, mul_zero, zero_add] using
      mul_le_mul_of_nonneg_right h2R (hw a)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun a _ => hpoint a
  simpa only [distanceShell, Finset.sum_filter, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum] using hsum

/-- The sum of the nonnegative neighbor deficits is controlled by twice the
distance-zero energy. Equivalently, `A₀ + F ≤ 2 A₀`. -/
theorem neighbor_deficit_le_twice_zero_mass (d : α → ℕ) (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (htotal : (∑ a, w a) = ((distanceShell d 1).card : ℝ) / 4)
    (henergy : (∑ a, (d a : ℝ) * w a) ≤ ∑ a, w a) :
    (∑ a ∈ distanceShell d 1, ((1 / 4 : ℝ) - w a)) ≤
      2 * (∑ a ∈ distanceShell d 0, w a) := by
  have hpoint := twice_mass_sub_neighbor_le_distance d w hw
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  linarith

/-- Restricting the nonnegative deficits to any chosen neighbor subset gives
the counting bound needed before applying the anticommutator identity. -/
theorem selected_neighbor_card_le_eight_mass (d : α → ℕ) (w : α → ℝ)
    (s : Finset α) (hs : s ⊆ distanceShell d 1)
    (hw : ∀ a, 0 ≤ w a)
    (hcap : ∀ a ∈ distanceShell d 1, w a ≤ (1 / 4 : ℝ))
    (htotal : (∑ a, w a) = ((distanceShell d 1).card : ℝ) / 4)
    (henergy : (∑ a, (d a : ℝ) * w a) ≤ ∑ a, w a) :
    (s.card : ℝ) ≤ 8 * ((∑ a ∈ distanceShell d 0, w a) + ∑ a ∈ s, w a) := by
  have hrestrict := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun a ha _ => sub_nonneg.mpr (hcap a ha))
  have hdeficit := neighbor_deficit_le_twice_zero_mass d w hw htotal henergy
  have hmass : 0 ≤ ∑ a ∈ s, w a := Finset.sum_nonneg fun a _ => hw a
  have hselected : (∑ a ∈ s, ((1 / 4 : ℝ) - w a)) =
      (s.card : ℝ) / 4 - ∑ a ∈ s, w a := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hselected] at hrestrict
  linarith

/-- On an equal-sign pair the anticommutator has four times the squared entry
mass. The diagonal is included as an equal-sign pair. -/
theorem anticommutator_entry_sq_of_same_sign [DecidableEq ι]
    (M : Matrix ι ι ℂ) (h : ι → ℝ) (hh : ∀ i, h i = 1 ∨ h i = -1)
    (i j : ι) (hij : h i = h j) :
    ‖(M * Matrix.diagonal (fun i => (h i : ℂ)) +
      Matrix.diagonal (fun i => (h i : ℂ)) * M) i j‖ ^ 2 =
      4 * ‖M i j‖ ^ 2 := by
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [← hij]
  have hfactor : M i j * (h i : ℂ) + (h i : ℂ) * M i j =
      (2 : ℂ) * (h i : ℂ) * M i j := by ring
  rw [hfactor]
  have hnorm : ‖(h i : ℂ)‖ = 1 := by
    rcases hh i with hi | hi <;> simp [hi]
  rw [norm_mul, norm_mul, hnorm]
  norm_num [mul_pow]

/-- The diagonal and a disjoint set of equal-sign neighbor entries contribute
four times their mass to the Hilbert--Schmidt squared norm. -/
theorem anticommutator_energy_ge_selected [DecidableEq ι]
    (ρ : ι → ι → ℕ) (hzero : ∀ i j, ρ i j = 0 → i = j)
    (M : Matrix ι ι ℂ) (h : ι → ℝ) (hh : ∀ i, h i = 1 ∨ h i = -1)
    (s : Finset (ι × ι))
    (hs : s ⊆ distanceShell (fun p : ι × ι => ρ p.1 p.2) 1)
    (hsign : ∀ p ∈ s, h p.1 = h p.2) :
    4 * ((∑ p ∈ distanceShell (fun p : ι × ι => ρ p.1 p.2) 0,
        ‖M p.1 p.2‖ ^ 2) + ∑ p ∈ s, ‖M p.1 p.2‖ ^ 2) ≤
      hsNormSq (M * Matrix.diagonal (fun i => (h i : ℂ)) +
        Matrix.diagonal (fun i => (h i : ℂ)) * M) := by
  classical
  let D := distanceShell (fun p : ι × ι => ρ p.1 p.2) 0
  let T := M * Matrix.diagonal (fun i => (h i : ℂ)) +
    Matrix.diagonal (fun i => (h i : ℂ)) * M
  have hdisj : Disjoint D s := by
    apply Finset.disjoint_left.mpr
    intro p hpD hps
    have h0 : ρ p.1 p.2 = 0 := by simpa only [D, mem_distanceShell] using hpD
    have h1 : ρ p.1 p.2 = 1 := by simpa only [mem_distanceShell] using hs hps
    omega
  have hsame : ∀ p ∈ D ∪ s, h p.1 = h p.2 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpD | hps
    · have h0 : ρ p.1 p.2 = 0 := by simpa only [D, mem_distanceShell] using hpD
      rw [hzero _ _ h0]
    · exact hsign p hps
  have hentries : (∑ p ∈ D ∪ s, 4 * ‖M p.1 p.2‖ ^ 2) =
      ∑ p ∈ D ∪ s, ‖T p.1 p.2‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro p hp
    exact (anticommutator_entry_sq_of_same_sign M h hh p.1 p.2 (hsame p hp)).symm
  have hsubset : (∑ p ∈ D ∪ s, ‖T p.1 p.2‖ ^ 2) ≤
      ∑ p : ι × ι, ‖T p.1 p.2‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun p _ _ => sq_nonneg ‖T p.1 p.2‖)
  have hsplit : (∑ p ∈ D ∪ s, 4 * ‖M p.1 p.2‖ ^ 2) =
      4 * ((∑ p ∈ D, ‖M p.1 p.2‖ ^ 2) + ∑ p ∈ s, ‖M p.1 p.2‖ ^ 2) := by
    rw [Finset.sum_union hdisj, ← Finset.mul_sum, ← Finset.mul_sum, mul_add]
  rw [← hentries, hsplit] at hsubset
  simpa only [D, T, hsNormSq, Fintype.sum_prod_type] using hsubset

/-- Abstract edge recovery from the exact finite matrix energy hypotheses.
The chosen set may be any subset of constant-sign distance-one pairs. -/
theorem edge_recovery_for_subset [DecidableEq ι]
    (ρ : ι → ι → ℕ) (hzero : ∀ i j, ρ i j = 0 → i = j)
    (M : Matrix ι ι ℂ) (h : ι → ℝ) (hh : ∀ i, h i = 1 ∨ h i = -1)
    (s : Finset (ι × ι))
    (hs : s ⊆ distanceShell (fun p : ι × ι => ρ p.1 p.2) 1)
    (hsign : ∀ p ∈ s, h p.1 = h p.2)
    (hcap : ∀ i j, ρ i j = 1 → ‖M i j‖ ^ 2 ≤ (1 / 4 : ℝ))
    (htotal : hsNormSq M =
      ((distanceShell (fun p : ι × ι => ρ p.1 p.2) 1).card : ℝ) / 4)
    (henergy : (∑ i, ∑ j, (ρ i j : ℝ) * ‖M i j‖ ^ 2) ≤ hsNormSq M) :
    (s.card : ℝ) ≤ 2 * hsNormSq
      (M * Matrix.diagonal (fun i => (h i : ℂ)) +
        Matrix.diagonal (fun i => (h i : ℂ)) * M) := by
  have hcount := selected_neighbor_card_le_eight_mass
    (fun p : ι × ι => ρ p.1 p.2) (fun p => ‖M p.1 p.2‖ ^ 2) s hs
    (fun p => sq_nonneg _) (fun p hp => hcap p.1 p.2 (by simpa only [mem_distanceShell] using hp))
    (by simpa only [hsNormSq, Fintype.sum_prod_type] using htotal)
    (by simpa only [hsNormSq, Fintype.sum_prod_type] using henergy)
  have hanti := anticommutator_energy_ge_selected ρ hzero M h hh s hs hsign
  linarith

/-- The edge-recovery inequality on the Boolean cube, from the three
matrix facts established by the grading and commutator constructions. -/
theorem edge_recovery {n : ℕ} (M : Matrix (Cube n) (Cube n) ℂ)
    (h : Cube n → ℝ) (hh : ∀ x, h x = 1 ∨ h x = -1)
    (htotal : hsNormSq M = (n : ℝ) * (2 : ℝ) ^ n / 4)
    (hdistance : (∑ x, ∑ y, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2) ≤ hsNormSq M)
    (hcap : ∀ x y, x ≠ y → ‖M x y‖ ^ 2 ≤ (1 / 4 : ℝ)) :
    ((orderedConstantEdges h).card : ℝ) ≤
      2 * hsNormSq (M * Matrix.diagonal (fun x => (h x : ℂ)) +
        Matrix.diagonal (fun x => (h x : ℂ)) * M) := by
  classical
  apply edge_recovery_for_subset (fun x y : Cube n => hammingDist x y)
    (fun _ _ hxy => hammingDist_eq_zero.mp hxy) M h hh (orderedConstantEdges h)
  · exact Finset.filter_subset _ _
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro x y hxy
    apply hcap x y
    intro heq
    subst y
    simp only [hammingDist_self, Nat.zero_ne_one] at hxy
  · change hsNormSq M = ((orderedNeighborPairs n).card : ℝ) / 4
    rw [card_orderedNeighborPairs]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using htotal
  · exact hdistance

end BooleanAnalysis.PolynomialThreshold.Internal

end Complexity
