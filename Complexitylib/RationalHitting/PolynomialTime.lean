/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.RationalHitting.PolynomialTime.Defs
public import Complexitylib.Classes.P.Defs
import Complexitylib.RationalHitting.PolynomialTime.Internal

/-!
# The rational hitting-list generator is in canonical FP

This transfers OpenAI's finite-machine runtime theorem to complexitylib's
canonical string-function class. Input `true^n ++ [false] ++ true^s` produces
the exact encoded `hittingList n s` for positive `n,s`; every malformed input
produces the empty string. A five-state format check supplies totality.

The source result and encoding are credited in `Complexitylib.RationalHitting`.
This theorem concerns list generation. Polynomial bit complexity for evaluating
rational formulas on the list remains a separate obligation.
-/

public section

namespace Complexity.RationalHitting

/-- The accepted inputs are exactly two positive unary parameters and a separator. -/
theorem inputDFA_accepts_iff {w : List Bool} :
    w ∈ inputDFA.accepts ↔ ∃ n s, 1 ≤ n ∧ 1 ≤ s ∧ w = binaryInput n s := by
  constructor
  · intro hw
    obtain ⟨n, s, rfl⟩ := Internal.input_shape hw
    exact ⟨n + 1, s + 1, by lia, by lia, rfl⟩
  · rintro ⟨n, s, hn, hs, rfl⟩
    cases n <;> cases s <;> try lia
    exact Internal.binaryInput_mem _ _

/-- The generator returns the source's complete encoding on literal positive unary input. -/
theorem hittingGenerator_binaryInput (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) :
    hittingGenerator (binaryInput n s) = encodeOutput (hittingList n s) := by
  cases n <;> cases s <;> try lia
  exact Internal.hittingGenerator_binaryInput _ _

/-- Every malformed binary string produces empty output. -/
theorem hittingGenerator_eq_nil {w : List Bool}
    (hw : ¬ ∃ n s, 1 ≤ n ∧ 1 ≤ s ∧ w = binaryInput n s) : hittingGenerator w = [] := by
  rw [hittingGenerator, ite_eq_right (mt inputDFA_accepts_iff.mp hw)]

/-- The total hitting-list generator has polynomial time in the canonical machine model. -/
theorem hittingGenerator_mem_FP : hittingGenerator ∈ FP :=
  Internal.hittingGenerator_mem_FP

end Complexity.RationalHitting
