/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Arithmetic.Power
public import Complexitylib.Algebraic.Applications.Hessian
public import Complexitylib.Algebraic.Applications.Waring
public import Complexitylib.Algebraic.LowerBound.AC0.ParitySeparation
public import Complexitylib.Algebraic.LowerBound.Counting.Shannon
public import Complexitylib.Algebraic.LowerBound.Hierarchy
public import Complexitylib.Algebraic.LowerBound.FanIn
public import Complexitylib.Algebraic.LowerBound.GateElimination.DeMorganXor
public import Complexitylib.Algebraic.LowerBound.Monotone.Clique.Exponential
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic.Complete
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Rectangle

/-!
# Curated applications

This facade gives short names to a deliberately small set of ready-to-use
compilers and flagship lower-bound endpoints. The defining modules remain the
source of truth for hypotheses and supporting theory.
-/

@[expose] public section

namespace Algebraic
namespace Applications

export Arithmetic.Power
  (binaryPowerGateCount
   binaryPowerCircuit
   binaryPowerCircuit_eval
   binaryPowerCircuit_multiplicationCost
   binaryPowerCircuit_additionCost)

export Circuit
  (card_inputSupport_le_size
   card_inputSupport_le_depth
   essential_le_size
   essential_le_depth
   asymptoticallyAlmostAllHard_shannon
   tendsto_easyDensity_zero_shannon
   tendsto_boolean_easyDensity_zero_shannon
   tendsto_finiteField_easyDensity_zero_shannon)

export Shannon (gateBudget)

export DeMorgan
  (xor_lowerBound
   eventually_exists_complexity_between
   polynomialSize_ssubset
   sizeClass_pow_ssubset)

export Fusion
  (pairCoverComplexity_eq_joinMeetCyclicComplexity
   pairCoverComplexity_eq_andOrCyclicComplexity)

export Fusion.SumOfTerms.Rectangle (diagonal_lowerBound)

export Monotone.Clique.Exponential
  (powSelf_lt_circuitSize
   twoPow_lt_circuitSize)

export AC0
  (parity_not_computable
   parity_not_raw_computable
   rawComputable_iff_computable)

end Applications
end Algebraic
