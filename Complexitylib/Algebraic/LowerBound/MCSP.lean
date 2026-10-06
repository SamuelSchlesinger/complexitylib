/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.MCSP.Defs
public import Complexitylib.Algebraic.LowerBound.MCSP.Symmetry
public import Complexitylib.Algebraic.LowerBound.MCSP.SubcubeRepetition
public import Complexitylib.Algebraic.LowerBound.MCSP.NonVacuity

/-!
# Minimum Circuit Size Problem (MCSP) lower bounds

This umbrella module exports the MCSP circuit and formula lower bound development:

* `Complexitylib.Algebraic.LowerBound.MCSP.Defs`: Truth-table indexing (`inputEquiv`,
  `truthTableEquiv`, `truthTableTargetEquiv`), subcube pairing (`muxTarget`, `pairTruthTable`),
  $\text{MCSP}[s]$ predicates (`mcspScalar`, `mcspTarget`, `mcspCostScalar`, `mcspCostTarget`,
  `yesSet`, `costYesSet`, `exactCostSet`), and circuit-counting upper bounds on `|yesSet|`.
* `Complexitylib.Algebraic.LowerBound.MCSP.Symmetry`: Transitive truth-table coordinate symmetry
  (`xorTranslate`, `tableTranslate`), exact `DeMorgan.binaryCost` and `Binary.signature`
  invariance of $\text{MCSP}[s]$, essentiality of all $2^n$ truth-table coordinates whenever the
  predicate is non-constant, and the resulting $2^n \le \text{size} + 1$ and
  $2^n \le \text{binaryCost} + 1$ lower bounds.
* `Complexitylib.Algebraic.LowerBound.MCSP.SubcubeRepetition`: Exact-complexity subcube
  repetition (`costComplexity_muxTarget_self`, `costComplexity_muxTarget_ge_add_one`),
  Foundational Lemma B (`mcspCostScalar_pairTruthTable_left_eq_true_iff`,
  `mcspCostScalar_pairTruthTable_right_eq_true_iff`), single-cut communication lower bounds
  (`mcsp_singleCut_card_exactCostSet_le`), Khrapchenko sensitivity / formula / bounded-sharing
  De Morgan circuit lower bounds (`khrapchenkoBound_mcsp_lower_bound`,
  `mcsp_formula_leaves_lower_bound`, `mcsp_sharedGateCount_cost_lower_bound`), and Nechiporuk
  subfunction and `Binary.Formula` leaf lower bounds on left-half blocks
  (`mcsp_card_image_restrictTo_le_subfunctions_leftBlock`,
  `mcsp_card_exactCostSet_le_subfunctions_leftHalf`,
  `mcsp_binaryFormula_leavesIn_leftBlock_lower_bound`,
  `mcsp_binaryFormula_leavesIn_leftHalf_lower_bound`). These assume a truth table of exact
  `DeMorgan.binaryCost` complexity `s ≥ 1`, and the resulting bounds are linear in the number
  $N = 2^{n+1}$ of MCSP inputs.
* `Complexitylib.Algebraic.LowerBound.MCSP.NonVacuity`: A truth table of exact
  `DeMorgan.binaryCost` complexity `1` (`exactCostSet_deMorgan_one_nonempty`), non-constancy of
  the De Morgan cost predicate (`mcspCostScalar_deMorgan_succ_ne_of_mem_exactCostSet`), and
  hypothesis-free forms of the symmetry bounds
  (`mcspCostTarget_deMorgan_one_binaryCost_lower_bound`,
  `mcspCostTarget_deMorgan_one_size_lower_bound`, `mcsp_one_formula_leaves_lower_bound`).
-/
