/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Internal.GuessVerify

/-!
# Generic linear-witness interface for the SAT guess-and-verify machine

The concrete machine in `SAT.Internal.GuessVerify` only assumes that guessed
witnesses have length at most `|x| + 1`; most of its machine proof is already
parametric in the verifier language. This module packages those generic
theorems for any relation with that same linear bound.

## Main result

- `SAT.language_mem_NP_of_linear_witness_verifierP_direct` -- a linearly
  balanced relation with a polynomial-time paired verifier defines an NP
  language
-/

@[expose] public section

namespace Complexity

namespace SAT

/-- A member with a linearly bounded witness has an accepting run of the
generic guess-and-verify machine. -/
theorem linearGuessVerify_acceptsInTime_of_mem
    {R : List Bool → List Bool → Prop} {L : Language}
    (hbound : ∀ x y, R x y → y.length ≤ x.length + 1)
    (hchar : ∀ x, x ∈ L ↔ ∃ y, R x y)
    (M : TM k) {f : ℕ → ℕ} (hM : M.DecidesInTime (pairLang R) f)
    (x : List Bool) (hx : x ∈ L) :
    (satGuessVerifyNTM M).AcceptsInTime x (satGuessVerifyTime f x.length) := by
  obtain ⟨y, hR⟩ := (hchar x).1 hx
  apply satGuessVerify_acceptsInTime_of_witness_bound_of_decidesInTime
    M hM x y (hbound x y hR)
  exact ⟨x, y, rfl, hR⟩

/-- A nonmember has no accepting run of the generic guess-and-verify machine
within its uniform time bound. -/
theorem linearGuessVerify_not_acceptsInTime_of_not_mem
    {R : List Bool → List Bool → Prop} {L : Language}
    (hchar : ∀ x, x ∈ L ↔ ∃ y, R x y)
    (M : TM k) {f : ℕ → ℕ} (hM : M.DecidesInTime (pairLang R) f)
    (x : List Bool) (hx : x ∉ L) :
    ¬ (satGuessVerifyNTM M).AcceptsInTime x (satGuessVerifyTime f x.length) := by
  rintro ⟨choices, _hhalt, hout⟩
  obtain ⟨y, _hy, htrace⟩ :=
    satGuessVerify_trace_decides_for_some_setup_witness_of_decidesInTime
      M hM x choices
  have hnotpair : pair x y ∉ pairLang R := by
    rintro ⟨x', y', hpair, hR⟩
    obtain ⟨hx', hy'⟩ := pair_inj hpair
    subst x'
    subst y'
    exact hx ((hchar x).2 ⟨y, hR⟩)
  have hzero :
      ((satGuessVerifyNTM M).trace (satGuessVerifyTime f x.length) choices
        ((satGuessVerifyNTM M).initCfg x)).output.cells 1 = Γ.zero :=
    htrace.2.2 hnotpair
  rw [hzero] at hout
  have hzero_ne_one : Γ.zero ≠ Γ.one := by decide
  exact hzero_ne_one hout

/-- The generic SAT guess-and-verify machine decides any language described
by a linearly bounded relation whose paired language is decided by `M`. -/
theorem linearGuessVerify_decidesInTime
    {R : List Bool → List Bool → Prop} {L : Language}
    (hbound : ∀ x y, R x y → y.length ≤ x.length + 1)
    (hchar : ∀ x, x ∈ L ↔ ∃ y, R x y)
    (M : TM k) {f : ℕ → ℕ} (hM : M.DecidesInTime (pairLang R) f) :
    (satGuessVerifyNTM M).DecidesInTime L (satGuessVerifyTime f) := by
  refine ⟨satGuessVerify_allPathsHaltIn_of_decidesInTime M hM, ?_⟩
  intro x
  constructor
  · exact linearGuessVerify_acceptsInTime_of_mem hbound hchar M hM x
  · intro hacc
    by_contra hx
    exact linearGuessVerify_not_acceptsInTime_of_not_mem hchar M hM x hx hacc

/-- A relation with witnesses bounded by `|x| + 1` and a verifier in `P`
places its existential language in `NP`. -/
theorem language_mem_NP_of_linear_witness_verifierP_direct
    {R : List Bool → List Bool → Prop} {L : Language}
    (hbound : ∀ x y, R x y → y.length ≤ x.length + 1)
    (hchar : ∀ x, x ∈ L ↔ ∃ y, R x y)
    (hverify : pairLang R ∈ P) : L ∈ NP := by
  obtain ⟨c, k, M, f, hM, hfO⟩ := Set.mem_iUnion.mp hverify
  obtain ⟨d, hgO⟩ := satGuessVerifyTime_bigO_of_bigO hfO
  refine Set.mem_iUnion.mpr
    ⟨d, k + 3, satGuessVerifyNTM M, satGuessVerifyTime f, ?_, hgO⟩
  exact linearGuessVerify_decidesInTime hbound hchar M hM

end SAT

end Complexity
