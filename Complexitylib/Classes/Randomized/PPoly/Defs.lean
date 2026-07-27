/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.Randomized.CircuitAmplification
public import Complexitylib.Classes.Randomized.GoodSeed
public import Complexitylib.Circuits.Family.Defs

/-!
# Nonuniform derandomization — definitions

This module defines the explicit nonuniform circuit-family witness used in
`BPP ⊆ P/poly`. For each input length it chooses a uniformly correct amplified
seed and fixes that seed in the canonical choices-first acceptance circuit.

Correctness, size bounds, and the containment theorem are proved in the
internal and surface modules.
-/

@[expose] public section

namespace Complexity

namespace NTM

/-- Choose one amplified seed that is correct simultaneously on every input of
length `n`. Its specification is `uniformCorrectSeed_correct`. -/
noncomputable def uniformCorrectSeed (tm : NTM k) (L : Language)
    (f : ℕ → ℕ) (haccept : tm.AcceptsWithProb L f (2 / 3))
    (hreject : tm.RejectsWithProb L f (1 / 3)) (n : ℕ) :
    BitString (uniformSeedRuns n * f n) :=
  Classical.choose (tm.exists_uniform_correct_seed L f haccept hreject n)

/-- The circuit family obtained by choosing and fixing one uniformly correct
amplified seed at each positive input length. The answer on the unique empty
input is stored directly, following the `CircuitFamily` convention. -/
noncomputable def hardwiredAmplificationFamily (tm : NTM k) (L : Language)
    (f : ℕ → ℕ) (haccept : tm.AcceptsWithProb L f (2 / 3))
    (hreject : tm.RejectsWithProb L f (1 / 3)) :
    CircuitFamily Basis.andOr2 := by
  classical
  exact
    { emptyOutput := decide ([] ∈ L)
      circuits := fun n _ =>
        ⟨_, CircuitUnrolling.fixedSeedAmplifiedAcceptanceCircuit tm
          (uniformSeedRuns n) (f n) n
          (tm.uniformCorrectSeed L f haccept hreject n)⟩ }

end NTM

end Complexity
