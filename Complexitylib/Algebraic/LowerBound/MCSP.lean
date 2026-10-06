/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.MCSP.Defs
public import Complexitylib.Algebraic.LowerBound.MCSP.Symmetry
public import Complexitylib.Algebraic.LowerBound.MCSP.SubcubeRepetition

/-!
# Minimum Circuit Size Problem (MCSP) lower bounds

This umbrella module exports the MCSP circuit and formula lower bound development:

* `Complexitylib.Algebraic.LowerBound.MCSP.Defs`: Truth-table indexing (`inputEquiv`,
  `truthTableEquiv`, `truthTableTargetEquiv`), subcube pairing (`muxTarget`, `pairTruthTable`),
  $\text{MCSP}[s]$ predicates (`mcspScalar`, `mcspTarget`, `mcspCostScalar`, `mcspCostTarget`,
  `yesSet`, `costYesSet`, `exactCostSet`), and DAG counting bounds on `|yesSet|`.
* `Complexitylib.Algebraic.LowerBound.MCSP.Symmetry`: Transitive truth-table coordinate symmetry
  (`xorTranslate`, `tableTranslate`), exact `DeMorgan.binaryCost` and `Binary.signature`
  invariance of $\text{MCSP}[s]$, essentiality of all $2^n$ truth-table coordinates, and
  unconditional $2^n \le 2 \cdot \text{size/cost}$ lower bounds.
* `Complexitylib.Algebraic.LowerBound.MCSP.SubcubeRepetition`: Exact-complexity subcube
  repetition (`costComplexity_muxTarget_self`, `costComplexity_muxTarget_ge_add_one`),
  Foundational Lemma B (`mcspCostScalar_pairTruthTable_left_eq_true_iff`,
  `mcspCostScalar_pairTruthTable_right_eq_true_iff`), single-cut communication lower bounds
  (`mcsp_singleCut_card_exactCostSet_le`), Khrapchenko sensitivity / formula / bounded-sharing
  De Morgan circuit lower bounds (`khrapchenkoBound_mcsp_lower_bound`,
  `mcsp_formula_leaves_lower_bound`, `mcsp_sharedGateCount_cost_lower_bound`), and Nechiporuk
  subfunction and `Binary.Formula` leaf lower bounds
  (`mcsp_card_image_restrictTo_le_subfunctions_leftBlock`,
  `mcsp_card_exactCostSet_le_subfunctions_leftHalf`,
  `mcsp_binaryFormula_leavesIn_leftBlock_lower_bound`,
  `mcsp_binaryFormula_leavesIn_leftHalf_lower_bound`).
-/
