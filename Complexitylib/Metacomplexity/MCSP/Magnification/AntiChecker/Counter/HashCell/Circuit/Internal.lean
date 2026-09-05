/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.HashCell.Circuit.Defs
import Complexitylib.SAT.CircuitSatisfiability

/-!
# Circuit predicates for anti-checker hash cells -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

namespace HashCellPredicateCircuit

theorem ruler_length_internal (beta : PositiveRationalScale) (arity : ℕ) :
    (ruler beta arity).length = counterSurvivorPowerWidth beta arity := by
  simp [ruler]

theorem evalFamilyCode_code_internal
    {beta : PositiveRationalScale} {arity prefixLength rangeWidth : ℕ}
    (predicate : HashCellPredicateCircuit beta arity prefixLength rangeWidth)
    (input : BitString (counterInputWidth arity prefixLength))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (counterSurvivorPowerWidth beta arity) rangeWidth))
    (witness : BitString (counterSurvivorPowerWidth beta arity)) :
    CircuitCode.evalFamilyCode predicate.code
        ((hashCellPublicInput beta input seed).toList ++ witness.toList) =
      some (decide (HashCellWitness arity (smallThreshold beta arity)
        (roundPrecision arity) rangeWidth input seed witness)) := by
  let packed := Fin.append (hashCellPublicInput beta input seed) witness
  have hlength :
      ((hashCellPublicInput beta input seed).toList ++ witness.toList).length =
        hashCellPredicateInputWidth beta arity prefixLength rangeWidth := by
    simp [hashCellPredicateInputWidth]
  have heval := CircuitCode.evalCode_encodeCircuit_of_length
    predicate.circuit
    ((hashCellPublicInput beta input seed).toList ++ witness.toList) hlength
  have hpacked :
      BitString.ofList
          ((hashCellPublicInput beta input seed).toList ++ witness.toList)
          hlength = packed := by
    apply BitString.toList_inj.mp
    rw [BitString.toList_ofList]
    exact (BitString.toList_append (hashCellPublicInput beta input seed)
      witness).symm
  rw [hpacked, predicate.implements input seed witness] at heval
  have hnonempty :
      (hashCellPublicInput beta input seed).toList ++ witness.toList ≠ [] := by
    intro hempty
    have hzero := congrArg List.length hempty
    simp [hashCellPublicWidth, counterInputWidth, hashCellPublicInput] at hzero
  simpa [code, CircuitCode.evalFamilyCode, hnonempty, hlength] using heval

theorem query_mem_extensionLanguage_iff_internal
    {beta : PositiveRationalScale} {arity prefixLength rangeWidth : ℕ}
    (predicate : HashCellPredicateCircuit beta arity prefixLength rangeWidth)
    (input : BitString (counterInputWidth arity prefixLength))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (counterSurvivorPowerWidth beta arity) rangeWidth)) :
    predicate.query input seed ∈ CircuitSAT.extensionLanguage ↔
      HashCellNonempty arity (smallThreshold beta arity)
        (roundPrecision arity) rangeWidth input seed := by
  rw [query, CircuitSAT.pair_mem_extensionLanguage_iff]
  constructor
  · rintro ⟨witnessBits, hwitnessLength, heval⟩
    have hwitnessLength' :
        witnessBits.length = counterSurvivorPowerWidth beta arity := by
      simpa [ruler] using hwitnessLength
    let witness := BitString.ofList witnessBits hwitnessLength'
    have hsemantic := evalFamilyCode_code_internal predicate input seed witness
    have hwitnessList : witness.toList = witnessBits := by
      exact BitString.toList_ofList witnessBits hwitnessLength'
    rw [hwitnessList] at hsemantic
    rw [hsemantic] at heval
    have hdecide : decide (HashCellWitness arity (smallThreshold beta arity)
        (roundPrecision arity) rangeWidth input seed witness) = true := by
      exact Option.some.inj heval
    exact ⟨witness, of_decide_eq_true hdecide⟩
  · rintro ⟨witness, hwitness⟩
    refine ⟨witness.toList, ?_, ?_⟩
    · simp [ruler, counterSurvivorPowerWidth]
    · have heval := evalFamilyCode_code_internal predicate input seed witness
      simpa only [counterSurvivorPowerWidth] using heval.trans (by simp [hwitness])

end HashCellPredicateCircuit

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
