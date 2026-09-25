/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Profile

/-!
# Split-indexed restrictions on multiplication outputs

This is the atom-level entry point for proving a rectangular rank profile.
Different splits may use unrelated arguments to bound the same multiplication
output, while the profile theorem chooses the strongest resulting ratio.
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

noncomputable section

variable {K : Type} {C : Type}

/-- At every split, every evaluated multiplication output obeys the indicated
rectangular catalecticant rank bound. -/
def MultiplicationOutputRankAtMost
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (localRank : Fin (degree + 1) → Nat) : Prop :=
  ∀ split,
    Rectangular.MultiplicationOutputRankAtMost constant degree split.1
      degreeAtLeastTwo circuit (localRank split)

/-- Atom-level bounds at every split induce the corresponding circuit-local
rank profile. -/
theorem localRankAtMost_of_multiplicationOutputRankAtMost
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (localRank : Fin (degree + 1) → Nat)
    (bound : MultiplicationOutputRankAtMost constant degree degreeAtLeastTwo
      circuit localRank) :
    LocalRankAtMost constant degree degreeAtLeastTwo circuit localRank := by
  intro split
  exact Rectangular.localRankAtMost_of_multiplicationOutputRankAtMost
    constant degree split.1 degreeAtLeastTwo circuit (localRank split)
    (bound split)

/-- The optimized rectangular lower bound, stated directly from atom-level
rank restrictions. -/
theorem certifiedLowerBound_of_multiplicationOutputRankAtMost
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (localRank : Fin (degree + 1) → Nat)
    (rankPositive : ∀ split, 0 < localRank split)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (bound : MultiplicationOutputRankAtMost constant degree degreeAtLeastTwo
      circuit localRank) :
    certifiedLowerBound degree localRank ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  certifiedLowerBound_le_multiplicationCost constant degree degreeAtLeastTwo
    localRank rankPositive circuit constructs
    (localRankAtMost_of_multiplicationOutputRankAtMost constant degree
      degreeAtLeastTwo circuit localRank bound)

end
end Profile
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
