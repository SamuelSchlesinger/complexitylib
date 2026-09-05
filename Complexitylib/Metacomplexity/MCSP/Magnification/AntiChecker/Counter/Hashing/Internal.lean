/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Hashing.Defs
public import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.OracleProgram
import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.Circuit
import Complexitylib.Classes.Randomized.ApproximateCounting.Relative
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.FixedWidth
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Domain

/-!
# Hashing circuits for anti-checker counters -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem hashingEstimate_lt_counterRange_internal
    {arity prefixLength : ℕ}
    (beta : PositiveRationalScale) (harity : arity ≠ 0)
    (input : BitString (counterInputWidth arity prefixLength))
    (seed : BitString (hashingCounterSeedWidth beta arity prefixLength)) :
    ApproximateCounting.Relative.hashingEstimate
        (roundPrecision arity) (counterInputWidth arity prefixLength + 1)
        (encodedSurvivorSet arity (smallThreshold beta arity) input) seed <
      2 ^ counterOutputWidth beta arity := by
  have hprecision : 0 < roundPrecision arity := by
    simp only [roundPrecision]
    omega
  have hbound :=
    ApproximateCounting.Relative.hashingEstimate_lt_two_pow_succ
      (encodedSurvivorSet arity (smallThreshold beta arity) input)
      seed hprecision
  have hwidth :
      candidateCodeWidth arity (smallThreshold beta arity) + 1 ≤
        counterOutputWidth beta arity := by
    have hcode := AntiChecker.fixedWidth_codeWidth_le_codeLengthBound
      arity (smallThreshold beta arity)
    simp only [candidateCodeWidth, counterOutputWidth, roundBlockCount]
    omega
  exact hbound.trans_le (Nat.pow_le_pow_right (by omega) hwidth)

theorem exists_correct_counter_of_hashingCircuit_internal
    {overhead arity prefixLength internalGates : ℕ}
    (beta : PositiveRationalScale) (harity : arity ≠ 0)
    {circuit : Circuit Basis.andOr2
      (hashingCounterSeedWidth beta arity prefixLength +
        counterInputWidth arity prefixLength)
      (counterOutputWidth beta arity) internalGates}
    (himplements : HashingCircuitImplements beta circuit)
    (hsize : circuit.size ≤ counterSizeBound overhead beta arity) :
    ∃ counter : ApproximateCounterCircuit overhead beta arity prefixLength,
      counter.IsCorrect ∧ counter.circuit.size = circuit.size := by
  have hprecision : 0 < roundPrecision arity := by
    simp only [roundPrecision]
    omega
  obtain ⟨fixed, hfixed, hfixedSize⟩ :=
    ApproximateCounting.Relative.exists_hardwired_accurate_circuit
      hprecision himplements
  let counter : ApproximateCounterCircuit overhead beta arity prefixLength :=
    { internalGates := internalGates
      circuit := fixed
      size_le := by
        rw [hfixedSize]
        exact hsize }
  refine ⟨counter, ?_, ?_⟩
  · intro input
    have haccurate := hfixed input
    unfold ApproximateCounting.Relative.OutputIsAccurate at haccurate
    rw [card_encodedSurvivorSet] at haccurate
    simp only [ApproximateCounterCircuit.estimate, counterValue, counter]
    exact haccurate
  · simp only [counter]
    exact hfixedSize

theorem exists_correct_counter_of_oracleProgram_internal
    {language : Language}
    {overhead arity prefixLength rounds : ℕ}
    (beta : PositiveRationalScale) (harity : arity ≠ 0)
    (program : AdaptiveOracleProgram
      (hashingCounterSeedWidth beta arity prefixLength +
        counterInputWidth arity prefixLength)
      (counterOutputWidth beta arity) rounds)
    (circuitOracle : PolynomialCircuitOracle language)
    (hprogram : ApproximateCounting.Relative.OracleProgramImplements
      (roundPrecision arity) (counterInputWidth arity prefixLength + 1)
      (encodedSurvivorSet arity (smallThreshold beta arity))
      program circuitOracle.oracle)
    (hsize : (program.inlineCircuitOracle circuitOracle).2.size ≤
      counterSizeBound overhead beta arity) :
    ∃ counter : ApproximateCounterCircuit overhead beta arity prefixLength,
      counter.IsCorrect ∧
        counter.circuit.size =
          (program.inlineCircuitOracle circuitOracle).2.size := by
  apply exists_correct_counter_of_hashingCircuit_internal beta harity
  · unfold HashingCircuitImplements
    exact ApproximateCounting.Relative.inlineCircuitImplements
      (circuitOracle.implementation program)
      (circuitOracle.implementation_implements program) hprogram
  · exact hsize

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
