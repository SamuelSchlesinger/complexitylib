/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Headline
public import Complexitylib.SAT.Internal.LinearGuessVerify
public import Complexitylib.SAT.ThreeSAT.Verifier
public import Complexitylib.Classes.Containments

/-!
# 3SAT is in NP

This file combines the ordinary SAT witness with the regular exact-3 syntax
condition. On paired inputs the resulting verifier language is the intersection
of the existing SAT verifier language and `ThreeSAT.PairSyntax.language`, so it
is in P. The generic linear-witness guess-and-verify construction then gives
the headline theorem `ThreeSAT.language_mem_NP`.
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

/-- A 3SAT witness is an ordinary SAT witness whose encoded formula also has
exact-3 syntax. -/
def Witness (z witness : List Bool) : Prop :=
  SAT.Witness z witness ∧ z ∈ Syntax.language

/-- Every 3SAT witness has the same linear length bound as its SAT witness. -/
theorem witness_length_le (z witness : List Bool) (h : Witness z witness) :
    witness.length ≤ z.length + 1 := by
  rcases h.1 with ⟨formula, hz, hlength, heval⟩
  exact hlength

/-- Exact-3 satisfiability is characterized by the combined witness relation. -/
theorem mem_language_iff_witness (z : List Bool) :
    z ∈ language ↔ ∃ witness, Witness z witness := by
  rw [language_eq_cnfsat_inter_syntax]
  constructor
  · rintro ⟨hsat, hsyntax⟩
    obtain ⟨witness, hwitness⟩ := (SAT.mem_language_iff_witness z).1 hsat
    exact ⟨witness, hwitness, hsyntax⟩
  · rintro ⟨witness, hwitness, hsyntax⟩
    exact ⟨(SAT.mem_language_iff_witness z).2 ⟨witness, hwitness⟩, hsyntax⟩

/-- The paired 3SAT witness language is the intersection of the SAT verifier
language and the paired exact-3 syntax language. -/
theorem pairLang_witness_eq :
    pairLang Witness = pairLang SAT.Witness ∩ PairSyntax.language := by
  ext input
  constructor
  · rintro ⟨z, witness, rfl, hwitness, hsyntax⟩
    exact ⟨⟨z, witness, rfl, hwitness⟩,
      (PairSyntax.pair_mem_language_iff z witness).2 hsyntax⟩
  · rintro ⟨⟨z, witness, hinput, hwitness⟩, hsyntax⟩
    have hzsyntax : z ∈ Syntax.language := by
      rw [hinput] at hsyntax
      exact (PairSyntax.pair_mem_language_iff z witness).1 hsyntax
    exact ⟨z, witness, hinput, hwitness, hzsyntax⟩

/-- The combined paired verifier language is in P. -/
theorem pairLang_witness_mem_P : pairLang Witness ∈ P := by
  rw [pairLang_witness_eq]
  exact P_inter SAT.pairLang_witness_mem_P PairSyntax.language_mem_P

/-- **3SAT ∈ NP.** Exact-3 satisfiability has linearly bounded witnesses and
a deterministic polynomial-time verifier. -/
theorem language_mem_NP : language ∈ NP :=
  SAT.language_mem_NP_of_linear_witness_verifierP_direct
    witness_length_le mem_language_iff_witness pairLang_witness_mem_P

end ThreeSAT

end SAT

end Complexity
