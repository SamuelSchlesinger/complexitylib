/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Balanced

/-!
# An exactly balanced function hard for OR-AND-OR and AND-OR-AND

Balanced padding of OpenAI's hard language inherits its unrestricted
depth-three lower bound under both polarities. The proof reuses complexitylib's
existing balanced-padding construction and the source circuit substitution.

Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageLowerBound.lean
-/

public section

namespace Complexity.DepthThreeLowerBound

/-- Positive-length slices of the list language are the balanced finite functions. -/
theorem balancedLanguage_ofFn (n : ℕ) (x : Cube (Fin (n + 1))) :
    balancedLanguage (List.ofFn x) = balancedFamily n x :=
  balancedLanguage_ofFn_proof n x

/-- The De Morgan dual interpretation complements the circuit's original value. -/
theorem Circuit3.dualEval_eq_not_eval {V : Type*} (C : Circuit3 V) (x : Cube V) :
    C.dualEval x = !C.eval x :=
  C.dualEval_eq_not_eval_proof x

/-- Exactly half the inputs are accepted, including at the smallest padded dimension. -/
theorem balancedFamily_card (n : ℕ) :
    (Algebraic.Cutwidth.accepting (balancedFamily n)).card = 2 ^ n :=
  balancedFamily_card_proof n

/-- Both the balanced function and its complement need more than every fixed
square-root exponential number of OR-AND-OR gates. -/
theorem balancedFamily_lower_bound (A : ℝ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ b : Bool, ∀ D : Circuit3 (Fin (n + 1)),
      D.Computes (fun x => Bool.xor (balancedFamily n x) b) →
        (2 : ℝ) ^ (A * Real.sqrt (n + 1 : ℕ)) < (D.gateCount : ℝ) :=
  balancedFamily_lower_bound_proof A hA

/-- The same balanced family is hard for both unrestricted depth-three polarities. -/
theorem balancedFamily_both_polarities (A : ℝ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ D : Circuit3 (Fin (n + 1)),
      (D.Computes (balancedFamily n) ∨ D.ComputesDual (balancedFamily n)) →
        (2 : ℝ) ^ (A * Real.sqrt (n + 1 : ℕ)) < (D.gateCount : ℝ) :=
  balancedFamily_both_polarities_proof A hA

end Complexity.DepthThreeLowerBound
