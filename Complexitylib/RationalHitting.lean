/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
public import Complexitylib.RationalHitting.Evaluation
public import Complexitylib.RationalHitting.Internal.Main

/-!
# Rational hitting lists, nonzeroness, and admissibility

OpenAI's source constructs one uniform polynomial-time generator of rational
matrix hitting lists for noncommutative rational formulas:
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Main.lean

The source runtime counts ordinary transitions of a fixed finite-state Mathlib
`TM0` machine. Its inputs are two unary parameters separated by a nonblank
symbol, and its output is the complete canonical binary encoding of the list.
`Complexitylib.RationalHitting.PolynomialTime` transfers this generator to
canonical `FP`, returning empty output on malformed binary inputs.

The additional executable tests decide nonzeroness and admissibility using exact
rational matrix evaluation. The latter needs a list for two extra syntax nodes:
if `f` has a defined value, either `f` or `f + 1` has a nonzero value. Their
correctness theorems do not assert polynomial bit complexity of evaluation.
These are deductions from the source result, without a claim of new priority.
-/

@[expose] public section

namespace Complexity.RationalHitting

/-- The explicit, executable list of rational matrix substitutions. -/
def hittingList (n s : ℕ) : Output n := ExecutableGenerator.list n s

/-- The generated list hits every nonzero formula of bounded size with an invertible value. -/
theorem hittingList_hits (n s : ℕ) (hs : 1 ≤ s) : Hits s (hittingList n s) := by
  rw [hittingList, ExecutableGenerator.list_spec]
  exact Generator.list_hits n s hs

/-- The generated matrices have polynomially bounded dimension. -/
theorem hittingList_dimension_le (n s : ℕ) :
    (hittingList n s).dimension ≤ 256 * (n + s + 1) ^ 10 := by
  rw [hittingList, ExecutableGenerator.list_spec]
  exact Generator.list_dimension_bound n s

/-- The complete reduced-rational binary encoding has polynomial length. -/
theorem hittingList_encoding_length_le (n s : ℕ) (hn : 1 ≤ n) :
    (encodeOutput (hittingList n s)).length ≤
      PolynomialBounds.outputConstant * (n + s + 1) ^ 104 := by
  rw [hittingList, ExecutableGenerator.list_spec]
  exact Generator.list_output_bound n s hn

/-- A fixed finite-state Mathlib machine generates these exact lists in polynomial bit time. -/
theorem exists_uniform_generator :
    ∃ (m : ℕ) (G : Machine m) (C k : ℕ), 0 < C ∧ 0 < k ∧
      ∀ n s : ℕ, 1 ≤ n → 1 ≤ s →
        OutputsWithin G s (C * (n + s + 1) ^ k) (hittingList n s) :=
  ExecutableGenerator.implementation

/-- OpenAI's combined dimension, encoding-length, hitting, and finite-machine runtime theorem. -/
theorem exists_polynomial_hitting_generator : MainStatement := main

/-- Some matrix evaluation of the inverse is defined exactly when the formula is nonzero. -/
theorem admissible_inv_iff_nonzero {n : ℕ} (f : Formula n) :
    Admissible (.inv f) ↔ Nonzero f :=
  (hittingList_hits n (f.size + 2) (by lia)).admissible_inv_iff_nonzero f (by lia)

/-- Every nonempty matrix domain has a witness of polynomially bounded dimension. -/
theorem Admissible.exists_dimension_le {n : ℕ} {f : Formula n} (hf : Admissible f) :
    ∃ d, 0 < d ∧ d ≤ 256 * (n + f.size + 3) ^ 10 ∧
      ∃ (X : Tuple n d) (v : Mat d), Evaluates f X v := by
  obtain ⟨X, _, v, he⟩ :=
    ((hittingList_hits n (f.size + 2) (by lia)).admissible_iff f le_rfl).mp hf
  refine ⟨_, (hittingList n (f.size + 2)).dimension_pos, ?_, X, v, he⟩
  simpa only [Nat.add_assoc] using hittingList_dimension_le n (f.size + 2)

/-- Test whether the formula has a defined positive-dimensional rational matrix evaluation. -/
def Formula.admissible? {n : ℕ} (f : Formula n) : Bool :=
  (hittingList n (f.size + 2)).admissibilityTest f

/-- Test whether the formula has a defined nonzero rational matrix evaluation. -/
def Formula.nonzero? {n : ℕ} (f : Formula n) : Bool :=
  (hittingList n (f.size + 2)).nonzeroTest f

/-- The generated finite domain test is correct, with no promise on the formula. -/
theorem Formula.admissible?_eq_true_iff {n : ℕ} (f : Formula n) :
    f.admissible? = true ↔ Admissible f :=
  (hittingList_hits n (f.size + 2) (by lia)).admissibilityTest_eq_true_iff f le_rfl

/-- The generated finite nonzeroness test is correct, with no admissibility promise. -/
theorem Formula.nonzero?_eq_true_iff {n : ℕ} (f : Formula n) :
    f.nonzero? = true ↔ Nonzero f :=
  (hittingList_hits n (f.size + 2) (by lia)).nonzeroTest_eq_true_iff f (by lia)

/-- Computed decidability of the existence of a defined matrix evaluation. -/
instance decidableAdmissible {n : ℕ} (f : Formula n) : Decidable (Admissible f) :=
  decidable_of_iff (f.admissible? = true) f.admissible?_eq_true_iff

/-- Computed decidability of the existence of a defined nonzero matrix evaluation. -/
instance decidableNonzero {n : ℕ} (f : Formula n) : Decidable (Nonzero f) :=
  decidable_of_iff (f.nonzero? = true) f.nonzero?_eq_true_iff

end Complexity.RationalHitting
