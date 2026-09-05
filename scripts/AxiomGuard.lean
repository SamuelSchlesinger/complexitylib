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

The audit selects declarations by their module of origin, not by declaration
name. It therefore covers private and generated declarations as well as the
library's extensions in foreign namespaces such as `Digraph` and `Nat`. The
executable validation modules are imported explicitly because they are
intentionally absent from the public `Complexitylib` import graph.

CI runs this on every push. `headlineTheorems` remains a readable index and a
rename smoke test; it does not determine the scope of the axiom audit.
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
  `Complexity.NTM.compositionNTM_decidesInTime,
  -- Universal machine
  `Complexity.TM.UTMBody.utmTM_universal,
  `Complexity.TM.UTMBody.utmTM_universal_padded,
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
