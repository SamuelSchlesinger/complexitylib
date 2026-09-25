/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Succinct.NP.Defs
import Complexitylib.Classes.NP.WitnessConstruction
import Complexitylib.Metacomplexity.MCSP.Succinct.Normalization.Internal
import Complexitylib.Metacomplexity.MCSP.Succinct.Witness.Internal

/-!
# SuccinctMCSP witness-class packaging -- proof internals
-/


public section

namespace Complexity

namespace SuccinctMCSP

theorem verifyRawWitness_eq_true_iff_internal (bits witness : List Bool) :
    verifyRawWitness bits witness = true ↔ RawWitnessRelation bits witness := by
  cases hdecode : Instance.decode? bits with
  | none => simp [verifyRawWitness, RawWitnessRelation, hdecode]
  | some inst =>
      simp [verifyRawWitness, RawWitnessRelation, hdecode,
        Instance.verifyRawCircuit_eq_true_iff_internal]

theorem rawWitnessRelation_mem_FNP_of_pairLang_mem_P_internal
    (hverifier : pairLang RawWitnessRelation ∈ P) :
    RawWitnessRelation ∈ FNP :=
  ⟨rawWitnessRelation_polyBalanced_internal, hverifier⟩

theorem mem_NP_of_pairLang_mem_P_internal
    (hverifier : pairLang RawWitnessRelation ∈ P) :
    Complexity.SuccinctMCSP ∈ NP := by
  apply NP.mem_NP_of_FNP
    (rawWitnessRelation_mem_FNP_of_pairLang_mem_P_internal hverifier)
  intro bits
  exact mem_iff_exists_rawWitnessRelation_internal bits

end SuccinctMCSP

end Complexity
