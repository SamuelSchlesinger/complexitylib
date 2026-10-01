/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.Semantics
public import Complexitylib.SAT.Rename
public import Complexitylib.SAT.ThreeCNF
public import Complexitylib.SAT.ThreeSAT
public import Complexitylib.SAT.ThreeSAT.Completeness
public import Complexitylib.SAT.ThreeSAT.Syntax
public import Complexitylib.SAT.Tseitin
public import Complexitylib.SAT.Tseitin.Machine
public import Complexitylib.SAT.QBF
public import Complexitylib.SAT.Resolution
public import Complexitylib.SAT.Encoding
public import Complexitylib.SAT.Language
public import Complexitylib.SAT.Verifier
public import Complexitylib.SAT.Headline
public import Complexitylib.SAT.GuessVerify
public import Complexitylib.SAT.CircuitOracle
public import Complexitylib.SAT.CircuitSatisfiability
public import Complexitylib.SAT.ThreeSAT.Headline
public import Complexitylib.SAT.CookLevin
public import Complexitylib.SAT.CookLevin.Assembly
public import Complexitylib.SAT.CookLevin.Corollaries

/-!
# SAT: Boolean satisfiability

This module formalizes the language **SAT** and the semantic/encoding
infrastructure used by the polynomial-time verifier.

## Submodules

- `Semantics` — `Lit`, `Clause`, `CNF`, `Assignment`, and the pure-recursive
  `CNF.eval`. This is the audit surface: whatever the verifier actually
  computes is proved equal to `CNF.eval α φ`.
- `Encoding`  — `CNF.encode : CNF → List Bool`, the bit-level format the
  verifier parses.
- `ThreeSAT` / `Tseitin` — the exact-3 language, its linear-time syntax
  checker, total encoded reduction, equisatisfiability, and quadratic
  encoding-size bound; `Tseitin.Machine` proves the concrete reduction is in
  `FP`, and `ThreeSAT.Completeness` proves 3SAT is NP-complete.
- `Language`  — `language`, the witness relation `Witness`, and the proofs
  `mem_language_iff_witness` / `polyBalanced_witness`.
- `Verifier` — executable decoding and checking for `pair(z, α)`.
- `VerifierTM` — deterministic TM components for the machine-level verifier.
- `GuessVerify` — compatibility API for the SAT-specialized NTM, preserving
  its concrete machine and exact bounds separately from the generic NP route.
- `Headline` / `CookLevin.Assembly` — `SAT ∈ NP` and the final
  NP-completeness theorem.
- `CircuitOracle` — extraction of a polynomial-size SAT circuit oracle from
  the hypothesis `NP ⊆ PPoly`.
- `CircuitSatisfiability` — exact-width circuit-SAT and fixed-prefix extension
  languages in `NP`, backed by the verified serialized circuit evaluator.
-/
