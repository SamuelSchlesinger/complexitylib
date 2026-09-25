/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.LayerIterationBounds
public import Complexitylib.Algebraic.LowerBound.AC0.ParityTopGate

/-!
# Variable-parameter depth reduction for parity circuits

This module composes the variable-parameter layer iterator with the parity
top-gate obstruction. A circuit of logical depth at most `rounds + 1` needs
only `rounds` restriction steps: the final unreduced AND or OR is handled as a
bounded-width normal form.

Under the explicit per-round switching and survivor inequalities, any parity
circuit forces `retained rounds <= treeBound rounds`. If the chosen schedule
ends above that tree bound, the circuit cannot compute parity. This is the
complete structural contradiction with the source-faithful `d - 1` round
count; selecting closed-form parameters remains a separate arithmetic task.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace Circuit

open scoped ENNReal

/-- A depth-`rounds + 1` parity circuit satisfying an explicit reduction
schedule forces the final survivor count below the final tree bound, with no
restriction on the placement of NOT gates. -/
theorem retained_le_treeBound_of_iterated_parity_raw
    (circuit : Algebraic.Circuit signature n 1)
    (computes : circuit.ComputesWith interpretation (Parity.target n))
    (rounds : Nat)
    (circuitDepth : logicalDepth circuit ≤ rounds + 1)
    (treeBound : Nat → Nat)
    (oneLeInitialBound : 1 ≤ treeBound 0)
    (p : Nat → NNReal)
    (atMostOne : ∀ level, level < rounds → p level ≤ 1)
    (boundMonotone : ∀ level, level < rounds →
      treeBound level ≤ treeBound (level + 1))
    (retained : Nat → Nat)
    (initial : retained 0 ≤ n)
    (failureLe : ∀ level, level < rounds →
      Program.layerFailureBoundOfBounds circuit.program (p level)
          (treeBound level) (treeBound (level + 1)) ≤
        (p level : ENNReal))
    (room : ∀ level, level < rounds →
      Program.layerFailureBoundOfBounds circuit.program (p level)
              (treeBound level) (treeBound (level + 1)) *
            (retained level : ENNReal) +
          (retained (level + 1) : ENNReal) <
        (p level : ENNReal) * (retained level : ENNReal)) :
    retained rounds ≤ treeBound rounds := by
  obtain ⟨rho, shallow, survivors⟩ :=
    Program.exists_shallowUpTo_with_liveCount_bounds_raw
      circuit.program rounds treeBound oneLeInitialBound p
      atMostOne boundMonotone retained initial failureLe room
  exact survivors.trans
    (liveCount_le_of_shallowBelowTop_computes_parity_raw
      computes circuitDepth shallow)

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem retained_le_treeBound_of_iterated_parity
    (circuit : Algebraic.Circuit signature n 1)
    (_normal : Program.NegationsAtInputs circuit.program)
    (computes : circuit.ComputesWith interpretation (Parity.target n))
    (rounds : Nat)
    (circuitDepth : logicalDepth circuit ≤ rounds + 1)
    (treeBound : Nat → Nat)
    (oneLeInitialBound : 1 ≤ treeBound 0)
    (p : Nat → NNReal)
    (atMostOne : ∀ level, level < rounds → p level ≤ 1)
    (boundMonotone : ∀ level, level < rounds →
      treeBound level ≤ treeBound (level + 1))
    (retained : Nat → Nat)
    (initial : retained 0 ≤ n)
    (failureLe : ∀ level, level < rounds →
      Program.layerFailureBoundOfBounds circuit.program (p level)
          (treeBound level) (treeBound (level + 1)) ≤
        (p level : ENNReal))
    (room : ∀ level, level < rounds →
      Program.layerFailureBoundOfBounds circuit.program (p level)
              (treeBound level) (treeBound (level + 1)) *
            (retained level : ENNReal) +
          (retained (level + 1) : ENNReal) <
        (p level : ENNReal) * (retained level : ENNReal)) :
    retained rounds ≤ treeBound rounds :=
  retained_le_treeBound_of_iterated_parity_raw circuit computes rounds
    circuitDepth treeBound oneLeInitialBound p atMostOne boundMonotone
    retained initial failureLe room

/-- Parameterized `rounds`-step parity lower bound with one unreduced top
layer: a schedule ending above its final tree allowance rules out the circuit,
with arbitrary internal NOT gates. -/
theorem not_computes_parity_of_iterated_switching_below_top_raw
    (circuit : Algebraic.Circuit signature n 1)
    (rounds : Nat)
    (circuitDepth : logicalDepth circuit ≤ rounds + 1)
    (treeBound : Nat → Nat)
    (oneLeInitialBound : 1 ≤ treeBound 0)
    (p : Nat → NNReal)
    (atMostOne : ∀ level, level < rounds → p level ≤ 1)
    (boundMonotone : ∀ level, level < rounds →
      treeBound level ≤ treeBound (level + 1))
    (retained : Nat → Nat)
    (initial : retained 0 ≤ n)
    (failureLe : ∀ level, level < rounds →
      Program.layerFailureBoundOfBounds circuit.program (p level)
          (treeBound level) (treeBound (level + 1)) ≤
        (p level : ENNReal))
    (room : ∀ level, level < rounds →
      Program.layerFailureBoundOfBounds circuit.program (p level)
              (treeBound level) (treeBound (level + 1)) *
            (retained level : ENNReal) +
          (retained (level + 1) : ENNReal) <
        (p level : ENNReal) * (retained level : ENNReal))
    (tooMany : treeBound rounds < retained rounds) :
    ¬circuit.ComputesWith interpretation (Parity.target n) := by
  intro computes
  exact (Nat.not_lt_of_ge
    (retained_le_treeBound_of_iterated_parity_raw
      circuit computes rounds circuitDepth treeBound
      oneLeInitialBound p atMostOne boundMonotone retained initial
      failureLe room)) tooMany

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem not_computes_parity_of_iterated_switching_below_top
    (circuit : Algebraic.Circuit signature n 1)
    (_normal : Program.NegationsAtInputs circuit.program)
    (rounds : Nat)
    (circuitDepth : logicalDepth circuit ≤ rounds + 1)
    (treeBound : Nat → Nat)
    (oneLeInitialBound : 1 ≤ treeBound 0)
    (p : Nat → NNReal)
    (atMostOne : ∀ level, level < rounds → p level ≤ 1)
    (boundMonotone : ∀ level, level < rounds →
      treeBound level ≤ treeBound (level + 1))
    (retained : Nat → Nat)
    (initial : retained 0 ≤ n)
    (failureLe : ∀ level, level < rounds →
      Program.layerFailureBoundOfBounds circuit.program (p level)
          (treeBound level) (treeBound (level + 1)) ≤
        (p level : ENNReal))
    (room : ∀ level, level < rounds →
      Program.layerFailureBoundOfBounds circuit.program (p level)
              (treeBound level) (treeBound (level + 1)) *
            (retained level : ENNReal) +
          (retained (level + 1) : ENNReal) <
        (p level : ENNReal) * (retained level : ENNReal))
    (tooMany : treeBound rounds < retained rounds) :
    ¬circuit.ComputesWith interpretation (Parity.target n) :=
  not_computes_parity_of_iterated_switching_below_top_raw circuit rounds
    circuitDepth treeBound oneLeInitialBound p atMostOne boundMonotone
    retained initial failureLe room tooMany

end Circuit
end AC0
end Algebraic
