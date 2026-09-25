/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic.Compiler
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic.LowerJoinMeet

/-!
# Exact fusion completeness for binary cyclic circuits

This module composes the subset-closure compiler with finite-join lowering.
For finite set problems whose generators cover the ambient type, a pair cover
therefore yields an ordinary binary AND/OR least-fixed-point circuit with
exactly one AND per pair.  Together with cover extraction, this identifies the
two complexity measures exactly.
-/

@[expose] public section

namespace Algebraic
namespace Fusion

variable {Γ : Type*}

/-- Binary cyclic circuit compiled from a pair cover. -/
noncomputable def binaryCircuitOfPairCover
    (problem : SetProblem Γ) [Finite Γ]
    (cover : PairCover problem SemifilterClass.all) :=
  JoinMeetLowering.circuit
    (PairClosureCompiler.circuit problem cover.pairs)

/-- Proof-carrying binary cyclic construction compiled from a pair cover. -/
noncomputable def binaryConstructsOfPairCover
    (problem : SetProblem Γ) [Finite Γ]
    (generatorsCover : problem.GeneratorsCover)
    (cover : PairCover problem SemifilterClass.all) :
    (binaryCircuitOfPairCover problem cover).Constructs
      (problem := problem) (AndOr.setInterpretation Γ) :=
  JoinMeetLowering.constructs
    (PairClosureCompiler.circuit problem cover.pairs)
    (PairClosureCompiler.constructsOfPairCover problem generatorsCover cover)

/-- The binary compiler charges exactly one AND for every pair occurrence. -/
theorem binaryCircuitOfPairCover_cost
    (problem : SetProblem Γ) [Finite Γ]
    (cover : PairCover problem SemifilterClass.all) :
    (binaryCircuitOfPairCover problem cover).cost AndOr.andCost =
      cover.cost := by
  unfold binaryCircuitOfPairCover
  rw [JoinMeetLowering.circuit_cost,
    PairClosureCompiler.circuit_cost]
  rfl

/-- Under the explicit finiteness and generator-coverage hypotheses, binary
cyclic AND complexity is no larger than pair-cover complexity. -/
theorem andOrCyclicComplexity_le_pairCoverComplexity
    (problem : SetProblem Γ) [Finite Γ]
    (generatorsCover : problem.GeneratorsCover) :
    andOrCyclicComplexity problem ≤
      pairCoverComplexity problem SemifilterClass.all := by
  unfold pairCoverComplexity
  refine le_iInf fun cover => ?_
  calc
    andOrCyclicComplexity problem ≤
        ((binaryCircuitOfPairCover problem cover).cost
          AndOr.andCost : ℕ∞) :=
      andOrCyclicComplexity_le problem
        (binaryCircuitOfPairCover problem cover)
        (binaryConstructsOfPairCover problem generatorsCover cover)
    _ = (cover.cost : ℕ∞) := by
      rw [binaryCircuitOfPairCover_cost]

/-- Exact modern fusion characterization using the ordinary binary AND/OR
cyclic model. -/
theorem pairCoverComplexity_eq_andOrCyclicComplexity
    (problem : SetProblem Γ) [Finite Γ]
    (generatorsCover : problem.GeneratorsCover) :
    pairCoverComplexity problem SemifilterClass.all =
      andOrCyclicComplexity problem :=
  le_antisymm
    (pairCoverComplexity_le_andOrCyclicComplexity problem)
    (andOrCyclicComplexity_le_pairCoverComplexity problem generatorsCover)

end Fusion
end Algebraic
