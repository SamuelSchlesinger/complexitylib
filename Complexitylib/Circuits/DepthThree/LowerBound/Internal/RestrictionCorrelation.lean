/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Core
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.FiniteProbability
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Unrestricted depth-three lower bound: restriction correlation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionCorrelation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V]

/-- The finite family of CNF tests obeying the width bound. -/
def narrowTests (b : ℕ) : Finset (Cube V → Bool) := by
  classical
  exact Finset.univ.filter fun J => ∃ H : CNF V, H.WidthAtMost b ∧ H.eval = J

@[simp] theorem mem_narrowTests_iff (b : ℕ) (J : Cube V → Bool) :
    J ∈ narrowTests b ↔ ∃ H : CNF V, H.WidthAtMost b ∧ H.eval = J := by
  classical
  simp [narrowTests]

theorem eval_mem_narrowTests (b : ℕ) (H : CNF V) (hH : H.WidthAtMost b) :
    H.eval ∈ narrowTests b :=
  (mem_narrowTests_iff b H.eval).mpr ⟨H, hH, rfl⟩

theorem narrowTests_true_mem (b : ℕ) :
    (fun _ : Cube V => true) ∈ narrowTests b := by
  apply (mem_narrowTests_iff b _).mpr
  refine ⟨[], ?_, ?_⟩
  · simp [CNF.WidthAtMost]
  · funext x
    exact CNF.eval_nil x

theorem narrowTests_false_mem (b : ℕ) :
    (fun _ : Cube V => false) ∈ narrowTests b := by
  apply (mem_narrowTests_iff b _).mpr
  refine ⟨[∅], ?_, ?_⟩
  · simp [CNF.WidthAtMost]
  · funext x
    simp

theorem narrowTests_nonempty (b : ℕ) : (narrowTests (V := V) b).Nonempty :=
  ⟨_, narrowTests_true_mem b⟩

/-- Uniform correlation with the indicator of a Boolean test. -/
def corr (b : ℕ) (G : Cube V → ℝ) : ℝ :=
  (narrowTests b).sup' (narrowTests_nonempty b)
    (fun J => |finiteAvg (fun x => G x * indicator (J x))|)

theorem abs_table_corr_le (b : ℕ) (G : Cube V → ℝ)
    (J : Cube V → Bool) (hJ : J ∈ narrowTests b) :
    |finiteAvg (fun x => G x * indicator (J x))| ≤ corr b G :=
  Finset.le_sup' (fun J : Cube V → Bool => |finiteAvg (fun x => G x * indicator (J x))|) hJ

theorem abs_corr_le (b : ℕ) (G : Cube V → ℝ) (H : CNF V)
    (hH : H.WidthAtMost b) :
    |finiteAvg (fun x => G x * indicator (H.eval x))| ≤ corr b G :=
  abs_table_corr_le b G H.eval (eval_mem_narrowTests b H hH)

theorem abs_mean_le_corr (b : ℕ) (G : Cube V → ℝ) :
    |finiteAvg G| ≤ corr b G := by
  simpa using abs_table_corr_le b G (fun _ => true) (narrowTests_true_mem b)

theorem corr_nonneg (b : ℕ) (G : Cube V → ℝ) : 0 ≤ corr b G :=
  (abs_nonneg (finiteAvg G)).trans (abs_mean_le_corr b G)

theorem corr_le_of_forall (b : ℕ) (G : Cube V → ℝ) (c : ℝ)
    (h : ∀ H : CNF V, H.WidthAtMost b →
      |finiteAvg (fun x => G x * indicator (H.eval x))| ≤ c) :
    corr b G ≤ c := by
  apply Finset.sup'_le
  intro J hJ
  obtain ⟨H, hH, rfl⟩ := (mem_narrowTests_iff b J).mp hJ
  exact h H hH

theorem corr_attained (b : ℕ) (G : Cube V → ℝ) :
    ∃ H : CNF V, H.WidthAtMost b ∧
      corr b G = |finiteAvg (fun x => G x * indicator (H.eval x))| := by
  obtain ⟨J, hJ, heq⟩ := Finset.exists_mem_eq_sup' (narrowTests_nonempty (V := V) b)
    (fun J => |finiteAvg (fun x => G x * indicator (J x))|)
  obtain ⟨H, hH, rfl⟩ := (mem_narrowTests_iff b J).mp hJ
  exact ⟨H, hH, heq⟩

theorem corr_le_abs_mean (b : ℕ) (G : Cube V → ℝ) :
    corr b G ≤ finiteAvg (fun x => |G x|) := by
  apply corr_le_of_forall
  intro H _
  apply (finiteAvg_abs_le _).trans
  apply finiteAvg_mono
  intro x
  rw [abs_mul, abs_of_nonneg (indicator_nonneg (H.eval x))]
  exact mul_le_of_le_one_right (abs_nonneg _) (indicator_le_one _)

theorem corr_linearCombination_identity {ι : Type uDepth2} (s : Finset ι)
    (c : ι → ℝ) (H : ι → CNF V) (G : Cube V → ℝ) :
    finiteAvg (fun x => G x * ∑ i ∈ s, c i * indicator ((H i).eval x)) =
      ∑ i ∈ s, c i * finiteAvg (fun x => G x * indicator ((H i).eval x)) := by
  calc
    _ = finiteAvg (fun x => ∑ i ∈ s, c i * (G x * indicator ((H i).eval x))) := by
      apply finiteAvg_congr
      intro x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_left_comm _ _ _
    _ = ∑ i ∈ s, finiteAvg (fun x => c i * (G x * indicator ((H i).eval x))) :=
      finiteAvg_sum s _
    _ = _ := Finset.sum_congr rfl (fun i _ => finiteAvg_const_mul _ _)

theorem abs_corr_linearCombination_le {ι : Type uDepth3} (s : Finset ι)
    (c : ι → ℝ) (H : ι → CNF V) (b : ℕ) (G : Cube V → ℝ)
    (hH : ∀ i ∈ s, (H i).WidthAtMost b) :
    |finiteAvg (fun x => G x * ∑ i ∈ s, c i * indicator ((H i).eval x))| ≤
      (∑ i ∈ s, |c i|) * corr b G := by
  rw [corr_linearCombination_identity]
  calc
    _ ≤ ∑ i ∈ s, |c i * finiteAvg (fun x => G x * indicator ((H i).eval x))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |c i| * |finiteAvg (fun x => G x * indicator ((H i).eval x))| := by
      simp only [abs_mul]
    _ ≤ ∑ i ∈ s, |c i| * corr b G := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (abs_corr_le b G (H i) (hH i hi)) (abs_nonneg _)
    _ = (∑ i ∈ s, |c i|) * corr b G := (Finset.sum_mul _ _ _).symm

theorem abs_corr_convex_mixture_le {ι : Type uDepth4} (s : Finset ι)
    (w : ι → ℝ) (H : ι → CNF V) (b : ℕ) (G : Cube V → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hH : ∀ i ∈ s, (H i).WidthAtMost b) :
    |finiteAvg (fun x => G x * ∑ i ∈ s, w i * indicator ((H i).eval x))| ≤
      corr b G := by
  have hwabs : (∑ i ∈ s, |w i|) = 1 := by
    calc
      _ = ∑ i ∈ s, w i :=
        Finset.sum_congr rfl (fun i hi => abs_of_nonneg (hw i hi))
      _ = 1 := hsum
  simpa only [hwabs, one_mul] using abs_corr_linearCombination_le s w H b G hH

theorem abs_corr_uniform_mixture_le {ι : Type uDepth5} [Fintype ι] [Nonempty ι]
    (H : ι → CNF V) (b : ℕ) (G : Cube V → ℝ)
    (hH : ∀ i, (H i).WidthAtMost b) :
    |finiteAvg (fun x => G x * finiteAvg (fun i => indicator ((H i).eval x)))| ≤
      corr b G := by
  have hlin :
      finiteAvg (fun x => G x * finiteAvg (fun i => indicator ((H i).eval x))) =
        finiteAvg (fun i => finiteAvg (fun x => G x * indicator ((H i).eval x))) := by
    calc
      _ = finiteAvg (fun x => finiteAvg (fun i => G x * indicator ((H i).eval x))) :=
        finiteAvg_congr (fun x => (finiteAvg_const_mul (G x) _).symm)
      _ = _ := finiteAvg_comm _
  rw [hlin]
  calc
    _ ≤ finiteAvg (fun i => |finiteAvg (fun x => G x * indicator ((H i).eval x))|) :=
      finiteAvg_abs_le _
    _ ≤ finiteAvg (fun _ : ι => corr b G) :=
      finiteAvg_mono (fun i => abs_corr_le b G (H i) (hH i))
    _ = corr b G := finiteAvg_const _

end DepthThreeLowerBound

end

end Complexity
