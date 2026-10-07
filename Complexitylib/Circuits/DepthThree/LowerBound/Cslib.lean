/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Uniform
public import Complexitylib.Circuits.AC0.Normalization.Cslib
import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Cslib

/-!
# Unrestricted depth-three hardness for general CSLib circuits

The exactly balanced family belongs to canonical `P`. Every sufficiently large slice needs
more than `2 ^ (A * sqrt n)` gates, for every fixed `A > 0`, in the general unbounded AND/OR
model with free edge negations and output depth at most three. Gates may be shared, the
wiring need not be layered, and the designated output may be any wire.

This is a checked consequence of OpenAI's lower bound, balanced padding, and the library's
circuit normalization. No claim of research priority is made.
-/

public section

namespace Complexity.AC0Formula

/-- Normalize a depth-three formula in one polarity with at most twice its tree size plus one. -/
theorem depth_three_source (f : AC0Formula n) (hd : f.depth ≤ 3) :
    ∃ (b : Bool) (C : DepthThreeLowerBound.Circuit3 (Fin n)),
      C.gateCount ≤ 2 * f.size + 1 ∧
      C.Computes (fun x => Bool.xor (f.eval x) b) :=
  depth_three_source_proof f hd

end Complexity.AC0Formula

namespace Complexity.DepthThreeLowerBound

/-- Every CSLib unbounded AND/OR circuit of depth at most three converts to a
source three-layer circuit in one output polarity with polynomial gate overhead. -/
theorem cslib_depth_three_source {n : ℕ} [NeZero n]
    (c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1) (hd : c.depth ≤ 3) :
    ∃ (b : Bool) (C : Circuit3 (Fin n)),
      C.gateCount ≤ 2 * (2 * (n + c.size) + 1) ^ 4 + 1 ∧
      C.Computes (fun x => Bool.xor (c.eval Basis.unboundedAndOr.interpretation x 0) b) :=
  cslib_depth_three_source_proof c hd

/-- The balanced polynomial-time family is hard for all CSLib unbounded AND/OR
circuits of depth at most three. Edge negations are free, and only gates are counted. -/
theorem balancedFamily_cslib_lower_bound (A : ℝ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature (n + 1) 1,
        c.depth ≤ 3 →
        c.Computes Basis.unboundedAndOr.interpretation
          (Cslib.Circuits.single (balancedFamily n)) →
        (2 : ℝ) ^ (A * Real.sqrt (n + 1 : ℕ)) < (c.size : ℝ) :=
  balancedFamily_cslib_lower_bound_proof A hA

/-- An exactly balanced language in canonical `P` has the unrestricted depth-three lower bound
in CSLib's general circuit model, with arbitrary wiring and free negations. -/
theorem exists_balanced_language_in_P_cslib_depth_three_lower_bound :
    ∃ L : List Bool → Bool, {w | L w = true} ∈ P ∧
      (∀ n, (Finset.univ.filter fun x : Cube (Fin (n + 1)) => L (List.ofFn x) = true).card =
        2 ^ n) ∧
      ∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature (n + 1) 1,
          c.depth ≤ 3 →
          c.Computes Basis.unboundedAndOr.interpretation
            (Cslib.Circuits.single (fun x => L (List.ofFn x))) →
          (2 : ℝ) ^ (A * Real.sqrt (n + 1 : ℕ)) < (c.size : ℝ) := by
  refine ⟨balancedLanguage, balancedLanguage_mem_P, ?_, ?_⟩
  · intro n
    simpa only [balancedLanguage_ofFn, Algebraic.Cutwidth.accepting] using
      balancedFamily_card n
  · simpa only [balancedLanguage_ofFn] using balancedFamily_cslib_lower_bound

end Complexity.DepthThreeLowerBound
