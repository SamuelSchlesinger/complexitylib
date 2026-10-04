/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Defs

/-!
# The source reserve for deterministic seed leakage

Reveal one seed-width observation for the honest call and for every
tampered call. The additional entropy reserve is exactly the bit width of
this joint observation, as in Chattopadhyay--Liao, Lemma 5.3.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The complete affine source reserve plus all `t + 1` seed-width observations. -/
def affineLeakageSourceEntropy (n t a target : Nat) : Nat :=
  affineIterationSourceEntropy n t a target +
    (t + 1) * affinePhaseOneRightBits n t a (affineIterationTarget t target)

end Algebraic.Cutwidth.Extractor
