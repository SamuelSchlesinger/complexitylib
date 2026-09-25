/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.ConditionalComplexity

/-!
# Lower bounds by parameterizing the original inputs

Constructing the tuple `(rho y, supplied (rho y))` and then applying a
conditional circuit computes the restricted target. The source tuple is
charged jointly, so any sharing in its implementation is retained.
-/

@[expose] public section

open Algebraic

namespace Cslib.Circuits.Circuit

/-- Build all restricted source values jointly, then run the conditional circuit. -/
theorem costComplexity_precomp_le_conditional_add
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (supplied : Target U n k) (map : Target U d n) :
    costComplexity interpretation operationCost (target ∘ map) ≤
      conditionalCostComplexity interpretation operationCost target supplied +
        costComplexity interpretation operationCost
          (fun input => Fin.append (map input) (supplied (map input))) :=
  relativeCostComplexity_precomp_triangle interpretation operationCost target
    (fun input => Fin.append input (supplied input)) map (fun input => input)

/-- A hard restricted target and a cheap joint source tuple give a lower
bound on conditional complexity. Natural subtraction truncates at zero. -/
theorem conditionalCostComplexity_lowerBound_of_precomp
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) (supplied : Target U n k) (map : Target U d n)
    (lower budget : Nat)
    (hard : (lower : ℕ∞) ≤ costComplexity interpretation operationCost (target ∘ map))
    (cheap : costComplexity interpretation operationCost
      (fun input => Fin.append (map input) (supplied (map input))) ≤ budget) :
    ((lower - budget : Nat) : ℕ∞) ≤
      conditionalCostComplexity interpretation operationCost target supplied := by
  have bound := hard.trans
    ((costComplexity_precomp_le_conditional_add interpretation operationCost target supplied map).trans
      (add_le_add le_rfl cheap))
  by_cases infinite : conditionalCostComplexity interpretation operationCost target supplied = ⊤
  · simp [infinite]
  · lift conditionalCostComplexity interpretation operationCost target supplied to Nat using infinite with value
    norm_cast at bound ⊢
    omega

end Cslib.Circuits.Circuit

namespace Algebraic.Circuit

export Cslib.Circuits.Circuit
  (costComplexity_precomp_le_conditional_add conditionalCostComplexity_lowerBound_of_precomp)

end Algebraic.Circuit
