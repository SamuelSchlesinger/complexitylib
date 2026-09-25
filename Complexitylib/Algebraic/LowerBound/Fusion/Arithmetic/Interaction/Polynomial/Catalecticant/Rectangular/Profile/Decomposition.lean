/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Decomposition
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Profile.Multiplication

/-!
# Waring decompositions as rectangular rank profiles

Uniform local Waring decompositions produce a constant rectangular rank
profile.  This small adapter keeps the generic profile API independent of the
chosen structural proof of its local bounds.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Profile
namespace Decomposition

noncomputable section

variable {K : Type} {C : Type}

/-- A uniform local Waring decomposition gives the same rank bound at every
rectangular split. -/
theorem multiplicationOutputRankAtMost
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (termCount : Nat)
    (restricted : Rectangular.Decomposition.AtMultiplications constant degree
      circuit termCount) :
    Profile.MultiplicationOutputRankAtMost constant degree degreeAtLeastTwo
      circuit (fun _ ↦ termCount) := by
  intro split
  exact Rectangular.Decomposition.multiplicationOutputRankAtMost_of_atMultiplications
    constant degree split.1 degreeAtLeastTwo circuit termCount restricted

/-- The profile-optimized lower bound obtained from a uniform local Waring
decomposition.  Keeping it in profile form lets later adapters combine it with
split-sensitive estimates without changing the circuit theorem. -/
theorem certifiedLowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (termCount : Nat)
    (termCountPositive : 0 < termCount)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (restricted : Rectangular.Decomposition.AtMultiplications constant degree
      circuit termCount) :
    Profile.certifiedLowerBound degree (fun _ ↦ termCount) ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  Profile.certifiedLowerBound_of_multiplicationOutputRankAtMost constant degree
    degreeAtLeastTwo (fun _ ↦ termCount) (fun _ ↦ termCountPositive)
    circuit constructs
    (multiplicationOutputRankAtMost constant degree degreeAtLeastTwo circuit
      termCount restricted)

end
end Decomposition
end Profile
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
