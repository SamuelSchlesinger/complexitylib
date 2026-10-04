/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib
import Complexitylib.Classes.P.Cobham.Validation
import Complexitylib.Circuits.Encoding.Validation
import Complexitylib.Models.TuringMachine.Repetition.Validation
import Complexitylib.Models.TuringMachine.SingleTape.Validation
import Complexitylib.SAT.Tseitin.Machine.Validation

/-!
# Axiom guard

Asserts that every kernel declaration compiled from a `Complexitylib` module
depends only on the three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). Auditing definitions and opaque declarations as well as proofs
prevents nonstandard axioms from being hidden behind a non-theorem declaration.
Run with:

```bash
lake env lean scripts/AxiomGuard.lean
```

CI runs this on every push. `headlineTheorems` remains a readable index and a
rename smoke test; it does not determine the scope of the axiom audit.

## Scope

- **Every Complexitylib module.** The audit visits every constant stored for
  every `Complexitylib` module in the environment: the modules reached through
  the root `Complexitylib` import and the executable validation modules, which
  are imported explicitly above because they are intentionally absent from the
  public import graph. The `buildImport` check of `scripts/lint_style.py` keeps
  every module reachable from one of its `BUILD_ROOTS`, and
  `scripts/test_build_roots.py` checks that this file imports each of them.
  Declarations are selected
  by module of origin, not by name, so private and generated declarations and
  the library's extensions in foreign namespaces such as `Digraph`, `Nat`, and
  `Cslib.Circuits` are covered.
- **Transitive dependencies.** The axioms of a declaration are collected
  through every constant it uses, including constants from Mathlib and CSLib,
  so a nonstandard axiom anywhere below a library declaration is reported.
  `sorry` (`sorryAx`) is caught this way when a declaration depends on it.
  On the pinned toolchain (Lean v4.35.0-rc3) native evaluation no longer goes
  through `Lean.ofReduceBool`: `native_decide`, `decide +native`, and `bv_decide`
  each add an auxiliary axiom asserting the evaluated result, named like
  `t._native.native_decide.ax_1_1` (`_native.decide`, `_native.bv_decide`).
  It is not allowlisted, so both the axiom and every declaration depending
  on it are reported.
- **Trusts the `.olean` files.** The audit reads declarations as the build
  stored them. It does not re-check them independently in the kernel, as a
  tool such as `lean4checker` would.
- **Allows `Classical.choice`.** Any `noncomputable def` passes. A claim in
  this library that a function is computable, in the complexity-theoretic
  sense, rests on the machine semantics (a machine computing it within a
  stated bound), not on Lean's notion of computability.
- **Does not see `example`s or `#guard`s.** Neither adds a constant to the
  environment. The executable validation modules close some `example`s with
  `native_decide` and run `#guard`s, as regression tests that trust the
  compiler; an `example` keeps no auxiliary axiom, and no declaration can
  depend on it. `scripts/lint_style.py` rejects native evaluation in every
  other `.lean` file.
-/

open Lean

/-- The axioms a Complexitylib declaration is allowed to depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The module-name prefix identifying declarations compiled from this library. -/
def complexitylibModulePrefix : Name := `Complexitylib

/-- A readable index of the library's headline theorems. -/
def headlineTheorems : List Name := [
  -- Cobham's characterization of polynomial-time functions
  `Complexity.Cobham.cobham_iff_FPn,
  `Complexity.CobhamFP_eq_FP,
  -- Cook–Levin / NP-completeness
  `Complexity.SAT.NPComplete_language,
  `Complexity.SAT.language_mem_NP,
  `Complexity.SAT.pairLang_witness_mem_P,
  -- Cook–Levin corollaries and coNP duality
  `Complexity.SAT.coNPComplete_compl_language,
  `Complexity.SAT.language_mem_P_iff_P_eq_NP,
  `Complexity.SAT.language_mem_coNP_iff_NP_eq_coNP,
  `Complexity.P_ne_NP_of_NP_ne_coNP,
  -- Closure under polynomial-time reductions
  `Complexity.MapReducesPoly.mem_NP,
  `Complexity.MapReducesPoly.mem_coNP,
  -- Public verifier API and exact-machine compatibility
  `Complexity.mem_NP_of_linear_witness,
  `Complexity.mem_NP_of_poly_witness,
  `Complexity.NP.mem_NP_of_linear_witness,
  `Complexity.guessVerify_decidesInTime,
  `Complexity.SAT.linearGuessVerify_decidesInTime,
  -- FNP witness characterization (guess and verify)
  `Complexity.NP.witnessNTMConstruction,
  `Complexity.NP.mem_NP_of_FNP,
  `Complexity.NTM.compositionNTM_decidesInTime,
  -- Universal machine
  `Complexity.TM.UTMBody.utmTM_universal,
  `Complexity.TM.UTMBody.utmTM_universal_padded,
  `Complexity.TM.utmTM_simulates_pair,
  `Complexity.TM.utmTM_isEfficientlyUniversal,
  `Complexity.TM.utmTM_isUniversal,
  -- Time hierarchy
  `Complexity.time_hierarchy_weak,
  `Complexity.time_hierarchy_weak_ssubset,
  `Complexity.DTIME_pow_ssubset,
  -- Structural containments
  `Complexity.P_subset_NP,
  `Complexity.P_subset_NP_inter_coNP,
  `Complexity.P_subset_PSPACE,
  `Complexity.P_subset_UniformPPoly,
  `Complexity.UniformPPoly_eq_P,
  `Complexity.RP_subset_NP,
  `Complexity.BPP_subset_PP,
  `Complexity.NL_subset_P,
  `Complexity.PSPACE_subset_EXP,
  `Complexity.PP_subset_PSPACE,
  `Complexity.PH_subset_PSPACE,
  -- Savitch's theorem
  `Complexity.NPSPACE_subset_PSPACE,
  `Complexity.PSPACE_eq_NPSPACE,
  -- the easy half of Shamir's theorem
  `Complexity.IP_subset_PSPACE,
  -- the PCP theorem
  `Complexity.PCP_theorem,
  `Complexity.exists_pcp_of_mem_NP,
  `Complexity.PCP_subset_NP,
  -- Circuit lower and upper bounds
  `Complexity.shannon_lower_bound_circuit,
  `Complexity.shannon_sizeComplexity,
  `Complexity.shannon_upper_bound,
  `Complexity.Circuit.card_essentialInputs_le_mul_size,
  `Complexity.sizeComplexity_xorBool_ge,
  -- The concrete uniform polynomial-time coefficient-four hard family
  `Algebraic.Cutwidth.Extractor.sourceReductionHardLanguage_mem_P,
  `Algebraic.Cutwidth.Extractor.sourceReductionHardEval_mem_FP,
  `Algebraic.Cutwidth.sourceReductionHardFamily_eventually_lt_size,
  -- The same family and the cutwidth bound for a general graph-ordering coefficient
  `Algebraic.Cutwidth.sourceReductionHardFamily_eventually_lt_size_of_orderingBound,
  `Algebraic.Cutwidth.eventually_lt_size_of_orderingBound,
  `Algebraic.Cutwidth.eventually_lt_size_of_cutwidthBound,
  `Algebraic.Cutwidth.Multigraph.orderingBound_of_cutwidthBound,
  -- Gaussian layouts: ordering coefficient (6/π)(3 - 2√2) < 1/3 and the explicit family
  `Algebraic.Cutwidth.Gaussian.exists_cutwidthBound,
  `Algebraic.Cutwidth.Multigraph.exists_orderingBound_gaussian,
  `Algebraic.Cutwidth.Multigraph.exists_orderingBound_twenty_div_sixtyOne,
  `Algebraic.Cutwidth.eventually_lt_size_of_rectangleFree_gaussian,
  `Algebraic.Cutwidth.sourceReductionHardFamily_eventually_lt_size_gaussian,
  `Algebraic.Cutwidth.sourceReductionHardFamily_eventually_lt_size_fortyOne_div_nine,
  `Algebraic.Cutwidth.Gaussian.exists_frontier_pathwidthBound,
  `Algebraic.Cutwidth.Multigraph.exists_orderingBound_frontier,
  `Algebraic.Cutwidth.Multigraph.exists_orderingBound_nine_div_thirtyTwo,
  -- Band-jump bounds, conditional on the open premise `Gaussian.BandSubcritical` (not an axiom)
  `Algebraic.Cutwidth.Gaussian.exists_band_pathwidthBound,
  `Algebraic.Cutwidth.Gaussian.two_mul_exp_mul_frontierCoefficient_le,
  `Algebraic.Cutwidth.Multigraph.exists_orderingBound_band,
  `Algebraic.Cutwidth.Multigraph.exists_orderingBound_five_div_eighteen_of_bandSubcritical,
  `Algebraic.Cutwidth.sourceReductionHardFamily_eventually_lt_size_of_bandSubcritical,
  (`Algebraic.Cutwidth).str
    "sourceReductionHardFamily_eventually_lt_size_twentyThree_div_five_of_bandSubcritical",
  -- Superconcentrators: the cut lemma and the (5.5625 - o(1)) N edge bound
  `Algebraic.Cutwidth.Multigraph.Superconcentrator.exists_le_card_cut,
  `Algebraic.Cutwidth.Multigraph.Superconcentrator.eventually_le_card_edges_of_orderingBound,
  `Algebraic.Cutwidth.Multigraph.Superconcentrator.eventually_le_card_edges,
  `Algebraic.Cutwidth.Multigraph.Superconcentrator.eventually_fifty_div_nine_sub_mul_le_card_edges,
  `Algebraic.Cutwidth.Multigraph.Superconcentrator.eventually_le_card_vertices,
  -- Multi-output circuits: ordering transfer, rank-cut bound, totally regular linear maps
  `Algebraic.Cutwidth.MultiOutput.exists_rank,
  `Algebraic.Cutwidth.MultiOutput.blockRank_add_blockRank_le,
  `Algebraic.Cutwidth.MultiOutput.totallyRegular_cauchyZMod,
  `Algebraic.Cutwidth.MultiOutput.eventually_lt_size_of_totallyRegular,
  `Algebraic.Cutwidth.MultiOutput.eventually_lt_size_of_totallyRegular_fortyOne_div_nine,
  `Algebraic.Cutwidth.MultiOutput.eventually_lt_size_cauchyZMod,
  -- Quadratic forms: the rank-cut bound and the (25/9 - ε) N gate bound
  `Algebraic.Cutwidth.MultiOutput.blockRank_add_transpose_le,
  `Algebraic.Cutwidth.MultiOutput.totallyRegular_hankelCauchyZMod_add_transpose,
  `Algebraic.Cutwidth.MultiOutput.half_le_of_quadForm,
  `Algebraic.Cutwidth.MultiOutput.eventually_lt_size_of_quadForm,
  `Algebraic.Cutwidth.MultiOutput.eventually_lt_size_of_quadForm_twentyFive_div_nine,
  `Algebraic.Cutwidth.MultiOutput.eventually_lt_size_hankelCauchyZMod,
  -- Border rank: lower semicontinuity of matrix rank and the Koszul-flattening bound
  `Matrix.isClosed_setOf_rank_le,
  `Algebraic.Tensor3.rank_wedgeMatrix,
  `Algebraic.Tensor3.rank_koszulFlattening_le_borderRank_mul,
  `Algebraic.Tensor3.not_borderRankLE_of_lt_rank_koszulFlattening,
  -- Multiplication in finite fields: restricted rank-cut bound and the (5.5625 - o(1)) n bound
  `Algebraic.Cutwidth.MultiOutput.card_piFinset_le_of_fibres,
  `Algebraic.Cutwidth.MultiOutput.card_pow_le_supportedKernel,
  `Algebraic.Cutwidth.MultiOutput.le_add_two_of_fieldMul,
  `Algebraic.Cutwidth.MultiOutput.sub_two_le_of_fieldMul,
  `Algebraic.Cutwidth.MultiOutput.eventually_lt_size_of_fieldMul,
  `Algebraic.Cutwidth.MultiOutput.eventually_lt_size_of_fieldMul_fifty_div_nine,
  `Algebraic.Cutwidth.MultiOutput.eventually_lt_size_galoisField,
  -- Korten's top-down parity lower bounds and the majority extension
  `Complexity.KarchmerWigderson.parity_communication_lower_bound,
  `Complexity.Circuit.parity_wire_lower_bound,
  `Complexity.KarchmerWigderson.majority_communication_lower_bound,
  `Complexity.Circuit.majority_wire_lower_bound,
  `Complexity.Valiant.depth_reduction
]

/-- One declaration with nonstandard axiom dependencies. -/
structure AuditFailure where
  moduleName : Name
  declarationName : Name
  disallowedAxioms : Array Name

/-- Render one audit failure as an indented diagnostic line. -/
def AuditFailure.format (failure : AuditFailure) : String :=
  let axioms := failure.disallowedAxioms.toList.map fun ax => s!"`{ax}`"
  s!"\n  `{failure.declarationName}` (module `{failure.moduleName}`): " ++
    String.intercalate ", " axioms

/-- Return all nonstandard axioms on which a declaration depends. -/
def disallowedAxiomsOf (declarationName : Name) : CoreM (Array Name) := do
  let axioms ← collectAxioms declarationName
  return (axioms.filter fun ax => !allowedAxioms.contains ax).qsort Name.lt

open Elab Command in
run_cmd do
  let env ← getEnv
  for headline in headlineTheorems do
    unless env.contains headline do
      throwError "axiom guard: unknown headline `{headline}` — was it renamed?"

  let mut moduleCount : Nat := 0
  let mut declarationCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut axiomCount : Nat := 0
  let mut failures : Array AuditFailure := #[]
  for h : moduleIdx in *...env.header.moduleData.size do
    let moduleName := env.header.moduleNames[moduleIdx]!
    if complexitylibModulePrefix.isPrefixOf moduleName then
      moduleCount := moduleCount + 1
      let moduleData := env.header.moduleData[moduleIdx]
      unless moduleData.constNames.size == moduleData.constants.size do
        throwError "axiom guard: malformed declaration table for module `{moduleName}`"
      for h : declarationIdx in *...moduleData.constants.size do
        declarationCount := declarationCount + 1
        let declarationName := moduleData.constNames[declarationIdx]!
        match moduleData.constants[declarationIdx] with
        | .thmInfo _ => theoremCount := theoremCount + 1
        | .axiomInfo _ => axiomCount := axiomCount + 1
        | _ => pure ()
        let disallowed ← liftCoreM (disallowedAxiomsOf declarationName)
        unless disallowed.isEmpty do
          failures := failures.push { moduleName, declarationName, disallowedAxioms := disallowed }

  unless failures.isEmpty do
    failures := failures.qsort fun left right =>
      Name.lt left.declarationName right.declarationName
    let details := String.join (failures.toList.map AuditFailure.format)
    let failureMessage : MessageData :=
      m!"axiom guard: {failures.size} Complexitylib declarations depend on " ++
        m!"disallowed axioms:{details}"
    throwError failureMessage

  let summary : MessageData :=
    m!"axiom guard: {declarationCount} declarations ({theoremCount} theorems, " ++
      m!"{axiomCount} axioms) from {moduleCount} Complexitylib modules use only standard axioms"
  logInfo summary
