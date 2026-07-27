/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.L.PolynomialTime
public import Complexitylib.Classes.P.Preimage
public import Complexitylib.Classes.PPoly.Uniform.Preprocessing
public import Complexitylib.Circuits.Encoding.Machine

/-!
# Uniform polynomial-size circuits are in P — proof internals
-/

@[expose] public section

namespace Complexity

/-- Internal packaging of the verified serialized evaluator as a language in
`P`. -/
theorem circuitEvalLanguage_mem_P_internal :
    CircuitCode.circuitEvalLanguage ∈ P := by
  apply Set.mem_iUnion.mpr
  exact ⟨2, CircuitCode.Machine.workTapeCount,
    CircuitCode.Machine.evalFamilyTM, CircuitCode.Machine.evalFamilyTime,
    CircuitCode.Machine.evalFamilyTM_decidesInTime,
    CircuitCode.Machine.evalFamilyTime_bigO_quadratic⟩

/-- Internal circuits-to-machines direction of logspace-uniform P/poly. -/
theorem UniformPPoly_subset_P_internal : UniformPPoly ⊆ P := by
  -- The size witness is not needed in this direction: total `FL` generation
  -- already bounds the complete serialized output polynomially via `FL ⊆ FP`.
  rintro L ⟨F, _p, hdec, _hsize, gen, hgenFL, hgenCorrect⟩
  have hgenFP : gen ∈ FP := FL_subset_FP hgenFL
  have hpreprocess : generatorEvalInput gen ∈ FP :=
    generatorEvalInput_mem_FP hgenFP
  have hpreimage :
      generatorEvalInput gen ⁻¹' CircuitCode.circuitEvalLanguage ∈ P :=
    mem_P_preimage hpreprocess circuitEvalLanguage_mem_P_internal
  have hlanguage :
      L = generatorEvalInput gen ⁻¹' CircuitCode.circuitEvalLanguage := by
    ext x
    change x ∈ L ↔ generatorEvalInput gen x ∈ CircuitCode.circuitEvalLanguage
    have hcode : gen (List.replicate x.length true) = F.encodeAt x.length := by
      simpa only [unaryList] using hgenCorrect x.length
    rw [generatorEvalInput, hcode,
      CircuitCode.encodeAt_pair_mem_circuitEvalLanguage_iff]
    exact (hdec.evalList x).symm
  rwa [hlanguage]

end Complexity
