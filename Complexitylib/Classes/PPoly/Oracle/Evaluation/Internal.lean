/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Oracle.Evaluation.Defs
import Complexitylib.Classes.PPoly.Oracle
import Complexitylib.Circuits.Composition
import Complexitylib.Circuits.Encoding.Machine
import Complexitylib.Circuits.InputPairing

/-!
# Serialized evaluation circuits from polynomial circuit oracles -- internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace EvaluationOracleCircuit

theorem eval_queryCircuit_internal
    {codeWidth inputWidth : ℕ} [NeZero codeWidth]
    (code : BitString codeWidth) (input : BitString inputWidth) :
    BitString.toList
        ((queryCircuit codeWidth inputWidth).eval (packedInput code input)) =
      pair code.toList input.toList := by
  unfold queryCircuit queryWidth
  rw [Circuit.eval_pairInputSources]
  congr 1
  · apply List.ext_get
    · simp
    · intro index hleft hright
      simp [codeSource, packedInput, Circuit.InputSource.eval]
  · apply List.ext_get
    · simp
    · intro index hleft hright
      simp [inputSource, packedInput, Circuit.InputSource.eval]

theorem eval_compile_internal
    (oracle : PolynomialCircuitOracle circuitEvalLanguage)
    {codeWidth inputWidth : ℕ} [NeZero codeWidth]
    (code : BitString codeWidth) (input : BitString inputWidth) :
    (compile oracle codeWidth inputWidth).2.eval (packedInput code input) 0 =
      decide (evalFamilyCode code.toList input.toList = some true) := by
  unfold compile
  rw [Circuit.eval_compose, oracle.circuit_eval_eq_oracle]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, oracle.oracle_decides]
  rw [eval_queryCircuit_internal, pair_mem_circuitEvalLanguage_iff]

theorem size_compile_internal
    (oracle : PolynomialCircuitOracle circuitEvalLanguage)
    (codeWidth inputWidth : ℕ) [NeZero codeWidth] :
    (compile oracle codeWidth inputWidth).2.size =
      queryWidth codeWidth inputWidth +
        oracle.family.size (queryWidth codeWidth inputWidth) := by
  unfold compile
  rw [Circuit.size_compose]
  unfold queryCircuit queryWidth
  erw [Circuit.size_pairInputSources, oracle.circuit_size_eq_family_size]

end EvaluationOracleCircuit

end CircuitCode

end Complexity
