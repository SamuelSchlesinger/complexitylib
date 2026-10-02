/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.SAT.GuessVerify

/-!
# Exact-machine compatibility regression examples

Run with `lake build --wfail SATGuessVerifyApiCheck`.
The old theorem names still describe the old concrete machine, tape count, and
clock. Importing the compatibility surface also retains the language-level API
previously available from `Classes.NP.Internal.GuessVerify`.
-/

namespace Complexity

example (M : TM k) {L L₀ : Language} {f : ℕ → ℕ}
    (hM : M.DecidesInTime L₀ f)
    (hchar : ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length ≤ x.length + 1 ∧ pair x y ∈ L₀) :
    (SAT.satGuessVerifyNTM M).DecidesInTime L (SAT.satGuessVerifyTime f) :=
  guessVerify_decidesInTime M hM hchar

example {R : List Bool → List Bool → Prop} {L : Language}
    (hbound : ∀ x y, R x y → y.length ≤ x.length + 1)
    (hchar : ∀ x, x ∈ L ↔ ∃ y, R x y)
    (M : TM k) {f : ℕ → ℕ} (hM : M.DecidesInTime (pairLang R) f) :
    (SAT.satGuessVerifyNTM M).DecidesInTime L (SAT.satGuessVerifyTime f) :=
  SAT.linearGuessVerify_decidesInTime hbound hchar M hM

example (M : TM k) : NTM (k + 3) := SAT.satGuessVerifyNTM M

example {L L₀ : Language} (hL₀ : L₀ ∈ P)
    (hchar : ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length ≤ x.length + 1 ∧ pair x y ∈ L₀) :
    L ∈ NP := mem_NP_of_linear_witness hL₀ hchar

-- The legacy import also retains its original padding-helper exports in modules.
example (p : Polynomial ℕ) (x : List Bool) :
    padWith p x = pair x (polyRuler p x) := rfl

example (p : Polynomial ℕ) : padWith p ∈ FP := padWith_mem_FP p

example {p : Polynomial ℕ} {L₀ : Language} (hL₀ : L₀ ∈ P) :
    padVerifier p L₀ ∈ P := padVerifier_mem_P hL₀

example {p : Polynomial ℕ} {L₀ : Language} (hL₀ : L₀ ∈ P) :
    padLang p L₀ ∈ NP := padLang_mem_NP hL₀

-- Earlier public imports also exposed the generic compiler and its linear bound.
#check WitnessTM.Verifier.compile_decidesInTimeSpace
#check WitnessTM.Verifier.time_linear_bigO_of_bigO

end Complexity
