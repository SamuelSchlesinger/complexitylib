/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Classes.NP.Verifier
public import Complexitylib.Classes.P.Bridge
public import Complexitylib.Classes.P.Cobham
public import Complexitylib.Classes.P.DecisionFn
public import Complexitylib.Classes.P.Pairing

/-!
# Public-only verifier API regression examples

Run with `lake build --wfail VerifierApiCheck`.
These examples exercise linear and zero polynomial witness bounds, including
empty inputs/certificates, a rejecting verifier, and malformed pair encodings.
No client imports an `Internal` module or a SAT theorem.
-/

namespace Complexity

private def emptyCertificateLanguage : Language := {w | pairSnd w = []}

private theorem emptyCertificateLanguage_mem_P : emptyCertificateLanguage ∈ P := by
  apply mem_P_of_decisionFn (emptyFlagFn_mem_FP pairSnd_mem_FP)
  intro w
  change pairSnd w = [] ↔ ∃ b ∈ emptyFlag (pairSnd w), b = true
  cases pairSnd w with
  | nil => simp
  | cons b bs => simp [emptyFlag_cons]

-- An empty certificate accepts even the empty input; a nonempty one is rejected.
example : pair [] [] ∈ emptyCertificateLanguage := by
  simp [emptyCertificateLanguage]

example : pair [] [true] ∉ emptyCertificateLanguage := by
  simp [emptyCertificateLanguage]

-- Linear witnesses include length zero: no positivity assumption is needed.
example : (Set.univ : Language) ∈ NP := by
  apply mem_NP_of_linear_witness emptyCertificateLanguage_mem_P
  intro x
  simp only [Set.mem_univ, true_iff]
  exact ⟨[], by simp, by simp [emptyCertificateLanguage]⟩

-- A zero polynomial bound permits exactly empty certificates, uniformly in x.
example : (Set.univ : Language) ∈ NP := by
  apply mem_NP_of_poly_witness 0 emptyCertificateLanguage_mem_P
  · intro x y hy
    have hy' : y = [] := by simpa [emptyCertificateLanguage] using hy
    simp [hy']
  · intro x
    simp only [Set.mem_univ, true_iff]
    exact ⟨[], by simp [emptyCertificateLanguage]⟩

-- A verifier that rejects everything yields the empty NP language.
example : (∅ : Language) ∈ NP := by
  have hreject : (∅ : Language) ∈ P := by
    apply mem_P_of_decisionFn (constFn_mem_FP [false])
    simp
  apply mem_NP_of_linear_witness hreject
  simp

-- Relation clients need only a bound, a characterization, and their P verifier.
example {R : List Bool → List Bool → Prop} {L : Language}
    (hbound : ∀ x y, R x y → y.length ≤ x.length + 1)
    (hchar : ∀ x, x ∈ L ↔ ∃ y, R x y)
    (hverify : pairLang R ∈ P) : L ∈ NP :=
  NP.mem_NP_of_linear_witness hbound hchar hverify

-- Empty input and certificate remain distinct from a malformed empty encoding.
example (R : List Bool → List Bool → Prop) :
    pair [] [] ∈ pairLang R ↔ R [] [] := mem_pairLang_pair R [] []

example (R : List Bool → List Bool → Prop) : [] ∉ pairLang R := by
  rintro ⟨x, y, hpair, _⟩
  have hlength := congrArg List.length hpair
  simp only [List.length_nil, pair_length] at hlength
  omega

end Complexity
