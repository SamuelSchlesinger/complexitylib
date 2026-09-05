/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.SAT.Internal.GuessVerify
public import Complexitylib.Classes.NP.Closure
public import Complexitylib.Classes.P.DecisionFn
public import Complexitylib.Classes.Containments
public import Complexitylib.Classes.Containments.Internal.NLSearchAssemble
public import Complexitylib.Classes.Containments.Internal.SavitchFrame
public import Complexitylib.Classes.P.Cobham.Internal

/-!
# Guess and verify, for any language

The guess-and-verify machine built for SAT is not in fact specific to SAT: it
takes an arbitrary deterministic verifier `M`, guesses a string of length at
most `|x| + 1`, pairs it with the input and runs `M` on the result. Every
structural theorem about it in `SAT/Internal/GuessVerify` is already stated for
an arbitrary language `L`; only the final assembly mentions SAT.

This module performs that assembly generically. The result is the
guess-and-verify bridge `NP.WitnessNTMConstruction` was meant to provide,
restricted to witnesses of linear length — which costs nothing, since padding
the input makes any polynomial witness bound linear.

## Main results

- `Complexity.mem_NP_of_linear_witness` — a language with a polynomial-time
  verifier and witnesses of length at most `|x| + 1` is in `NP`
- `Complexity.mem_NP_of_poly_witness` — the same for any polynomial witness
  bound, by padding the input until the bound is linear
-/

@[expose] public section

namespace Complexity

variable {k : ℕ}

/-- The guess-and-verify machine decides any language whose members are exactly
the inputs with a short certificate accepted by `M`. -/
theorem guessVerify_decidesInTime (M : TM k) {L L₀ : Language} {f : ℕ → ℕ}
    (hM : M.DecidesInTime L₀ f)
    (hchar : ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length ≤ x.length + 1 ∧ pair x y ∈ L₀) :
    (SAT.satGuessVerifyNTM M).DecidesInTime L (SAT.satGuessVerifyTime f) := by
  refine ⟨SAT.satGuessVerify_allPathsHaltIn_of_decidesInTime M hM, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨y, hlen, hmem⟩ := (hchar x).1 hx
    exact SAT.satGuessVerify_acceptsInTime_of_witness_bound_of_decidesInTime M hM x y
      hlen hmem
  · intro hacc
    by_contra hx
    obtain ⟨choices, hhalt, hout⟩ := hacc
    obtain ⟨y, hy, htrace⟩ :=
      SAT.satGuessVerify_trace_decides_for_some_setup_witness_of_decidesInTime M hM x choices
    have hnot : pair x y ∉ L₀ := fun hmem => hx ((hchar x).2 ⟨y, hy, hmem⟩)
    have hzero : ((SAT.satGuessVerifyNTM M).trace (SAT.satGuessVerifyTime f x.length) choices
        ((SAT.satGuessVerifyNTM M).initCfg x)).output.cells 1 = Γ.zero :=
      htrace.2.2 hnot
    rw [hzero] at hout
    exact (by decide : Γ.zero ≠ Γ.one) hout

/-- **Guess and verify.** A language whose members are exactly the inputs
carrying a certificate of length at most `|x| + 1` that a polynomial-time
verifier accepts is in `NP`. -/
theorem mem_NP_of_linear_witness {L L₀ : Language} (hL₀ : L₀ ∈ P)
    (hchar : ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length ≤ x.length + 1 ∧ pair x y ∈ L₀) :
    L ∈ NP := by
  obtain ⟨c, k, M, f, hM, hfO⟩ := Set.mem_iUnion.mp hL₀
  obtain ⟨d, hgO⟩ := SAT.satGuessVerifyTime_bigO_of_bigO hfO
  exact Set.mem_iUnion.mpr ⟨d, k + 3, SAT.satGuessVerifyNTM M, SAT.satGuessVerifyTime f,
    guessVerify_decidesInTime M hM hchar, hgO⟩

/-! ### Any polynomial witness bound -/

/-- The input padded with a ruler long enough to make the witness bound linear. -/
noncomputable def padWith (p : Polynomial ℕ) (x : List Bool) : List Bool :=
  pair x (polyRuler p x)

theorem padWith_mem_FP (p : Polynomial ℕ) : padWith p ∈ FP := by
  have h : (fun z : List Bool => polyRuler p (id z)) ∈ FP := polyRulerFn_mem_FP p id_mem_FP
  exact Cobham.pairFn_mem_FP id_mem_FP h

/-- The verifier for the padded language: run the original verifier on the
unpadded input, and check that the padding really is long enough. -/
noncomputable def padVerifier (p : Polynomial ℕ) (L₀ : Language) : Language :=
  {w | pair (pairFst (pairFst w)) (pairSnd w) ∈ L₀ ∧
    (polyRuler p (pairFst (pairFst w))).length
      ≤ (pairSnd (pairFst w)).length}

theorem padVerifier_mem_P {p : Polynomial ℕ} {L₀ : Language} (hL₀ : L₀ ∈ P) :
    padVerifier p L₀ ∈ P := by
  have hff : (fun w : List Bool => pairFst (pairFst w)) ∈ FP :=
    fstBlockOf_mem_FP Cobham.fstBlock_mem_FP
  have hsf : (fun w : List Bool => pairSnd (pairFst w)) ∈ FP :=
    sndBlockOf_mem_FP Cobham.fstBlock_mem_FP
  have hA : (fun w : List Bool =>
      pair (pairFst (pairFst w)) (pairSnd w)) ⁻¹' L₀ ∈ P :=
    mem_P_preimage (Cobham.pairFn_mem_FP hff Cobham.sndBlock_mem_FP) hL₀
  have hruler : (fun w : List Bool =>
      polyRuler p (pairFst (pairFst w))) ∈ FP :=
    polyRulerFn_mem_FP p hff
  have hB : {w : List Bool |
      (polyRuler p (pairFst (pairFst w))).length
        ≤ (pairSnd (pairFst w)).length} ∈ P := by
    refine mem_P_of_decisionFn (lenLeFlagFn_mem_FP hsf hruler) fun w => ?_
    simp only [Set.mem_ofPred_eq]
    set a := pairSnd (pairFst w) with ha
    set b := polyRuler p (pairFst (pairFst w)) with hb
    constructor
    · intro hle
      rw [(Cobham.lenLeFlag_eq_true_iff a b).mpr hle]
      exact ⟨true, by simp, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      rcases Cobham.lenLeFlag_flag a b with h | h
      · exact (Cobham.lenLeFlag_eq_true_iff a b).mp h
      · rw [h] at hc
        simp at hc
  exact P_inter hA hB

/-- The padded language, whose witnesses are short enough for the linear
guess-and-verify machine. -/
noncomputable def padLang (p : Polynomial ℕ) (L₀ : Language) : Language :=
  {z | ∃ y : List Bool, y.length ≤ z.length + 1 ∧ pair z y ∈ padVerifier p L₀}

theorem padLang_mem_NP {p : Polynomial ℕ} {L₀ : Language} (hL₀ : L₀ ∈ P) :
    padLang p L₀ ∈ NP :=
  mem_NP_of_linear_witness (padVerifier_mem_P hL₀) fun _ => Iff.rfl

/-- **Guess and verify, with any polynomial witness bound.** A language whose
members are exactly the inputs carrying a certificate a polynomial-time verifier
accepts is in `NP`, provided the verifier only accepts certificates of
polynomial length. -/
theorem mem_NP_of_poly_witness {L L₀ : Language} (p : Polynomial ℕ) (hL₀ : L₀ ∈ P)
    (hbal : ∀ x y : List Bool, pair x y ∈ L₀ → y.length ≤ p.eval x.length)
    (hchar : ∀ x, x ∈ L ↔ ∃ y : List Bool, pair x y ∈ L₀) :
    L ∈ NP := by
  have hpre : L = padWith p ⁻¹' padLang p L₀ := by
    ext x
    rw [Set.mem_preimage, hchar x]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_, ?_, ?_⟩
      · have := hbal x y hy
        rw [padWith, pair_length, polyRuler_length]
        omega
      · rw [padWith, pairSnd_pair, pairFst_pair, pairFst_pair]
        exact hy
      · rw [padWith, pairFst_pair, pairFst_pair, pairSnd_pair]
    · rintro ⟨y, _, hmem, _⟩
      refine ⟨y, ?_⟩
      rw [padWith, pairSnd_pair, pairFst_pair, pairFst_pair] at hmem
      exact hmem
  rw [hpre]
  exact mem_NP_preimage (padWith_mem_FP p) (padLang_mem_NP hL₀)

end Complexity
