/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models
public import Complexitylib.Asymptotics
public import Complexitylib.TimeConstructible
public import Complexitylib.Classes
public import Complexitylib.Languages
public import Complexitylib.SAT
public import Complexitylib.Circuits
public import Complexitylib.BooleanAnalysis
public import Complexitylib.DescriptiveComplexity

/-!
# Complexitylib

The root module: importing it brings in the library's complete public
surface. Import an area module (`Complexitylib.Models`,
`Complexitylib.Classes`, …) instead to keep dependencies smaller.

## Headline theorems

Machine-checked with no `sorry` and no custom axioms — CI audits every
Complexitylib declaration for dependencies beyond `propext`,
`Classical.choice`, and `Quot.sound` (`scripts/AxiomGuard.lean`).

**Cook–Levin: SAT is NP-complete.**
- `Complexity.SAT.NPComplete_language` — `NPComplete SAT.language`
- `Complexity.SAT.language_mem_NP` — `SAT.language ∈ NP`
- `Complexity.SAT.pairLang_witness_mem_P` — the SAT verifier runs in
  polynomial time

**Universal simulation.**
- `Complexity.TM.UTMBody.utmTM_universal` — a fixed machine simulates any
  encoded machine with explicit time overhead (Arora–Barak Theorem 1.9)
- `Complexity.TM.UTMBody.utmTM_universal_padded` — the padded-encoding
  variant

**Deterministic time hierarchy.**
- `Complexity.time_hierarchy_weak` — more time decides strictly more
  languages, in a concrete clock-constructible formulation
- `Complexity.time_hierarchy_weak_ssubset`, `Complexity.DTIME_pow_ssubset`
  — strict polynomial separations such as
  `DTIME((n+1)^a) ⊂ DTIME((n+1)^(2a+5))`

**Structural containments.** `Complexity.P_subset_NP`,
`Complexity.P_subset_PSPACE`, `Complexity.P_subset_PPoly`,
`Complexity.UniformPPoly_subset_P`,
`Complexity.PAdvice_subset_PPoly`, `Complexity.PPoly_subset_PAdvice`,
`Complexity.RP_subset_NP`, `Complexity.BPP_subset_PPoly`,
`Complexity.BPP_subset_PAdvice`, and `Complexity.BPP_subset_PP`. The nonuniform
equivalence lives in `Complexitylib.Classes.PPoly.Advice`, while randomized
hardwiring and its advice corollary live in
`Complexitylib.Classes.Randomized.PPoly`; the broader time/space index is
`Complexitylib.Classes.Containments`.

**Circuit lower bounds.** Shannon's counting bound, gate-elimination
(`Circuit.card_essentialInputs_le_mul_size`), Schnorr's XOR bound
(`Complexity.sizeComplexity_xorBool_ge`), and Valiant's depth reduction
(`Complexity.Valiant.depth_reduction`).

**Barrington's theorem.** `Complexity.barrington_equivalence` identifies
logarithmic-depth Boolean formula families with polynomial-length width-`5`
permutation branching-program families.
-/

@[expose] public section
