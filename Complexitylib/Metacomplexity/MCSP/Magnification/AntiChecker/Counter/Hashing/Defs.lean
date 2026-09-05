/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.Circuit.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Circuit.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Domain.Defs

/-!
# Hashing circuits for anti-checker counters -- definitions

This layer specializes the generic relative-counting circuit contract to the
fixed-width encoded survivor set used by the Anti-Checker Lemma.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Width of the packed labeled-sample input for the counter extending a
prefix of length `prefixLength`. -/
@[reducible] def counterInputWidth (arity prefixLength : ℕ) : ℕ :=
  (prefixLength + 1) * (arity + 1)

instance (arity prefixLength : ℕ) :
    NeZero (counterInputWidth arity prefixLength) :=
  ⟨by simp [counterInputWidth]⟩

/-- Randomness needed by the relative hashing estimator on the encoded
survivor domain, with enough failure exponent to fix one seed for every
labeled-sample input. -/
def hashingCounterSeedWidth (beta : PositiveRationalScale)
    (arity prefixLength : ℕ) : ℕ :=
  ApproximateCounting.Relative.seedWidth
    (candidateCodeWidth arity (smallThreshold beta arity))
    (roundPrecision arity) (counterInputWidth arity prefixLength + 1)

/-- A seed-prefix circuit exactly implements the amplified hashing estimator
for the encoded labeled-survivor set. -/
def HashingCircuitImplements
    {arity prefixLength internalGates : ℕ}
    (beta : PositiveRationalScale)
    (circuit : Circuit Basis.andOr2
      (hashingCounterSeedWidth beta arity prefixLength +
        counterInputWidth arity prefixLength)
      (counterOutputWidth beta arity) internalGates) : Prop :=
  ApproximateCounting.Relative.CircuitImplements
    (roundPrecision arity) (counterInputWidth arity prefixLength + 1)
    (encodedSurvivorSet arity (smallThreshold beta arity)) circuit

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
