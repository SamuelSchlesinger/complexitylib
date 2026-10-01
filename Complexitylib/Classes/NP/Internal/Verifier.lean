/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel’s dot
-/
module
public import Complexitylib.Classes.NP.Verifier.Linear
public import Complexitylib.Classes.NP.Closure
public import Complexitylib.Classes.P.Bridge
public import Complexitylib.Classes.P.DecisionFn
public import Complexitylib.Classes.Containments
public import Complexitylib.Classes.P.Cobham.Internal

/-!
# Polynomial witness bounds by padding

The linear-witness theorem is provided by the generic finite-verifier compiler
through `Complexitylib.Classes.NP.Verifier.Linear`. Polynomial witness bounds
reduce to that case by padding until the witness bound is linear in input size.
This implementation has no SAT dependency. The public membership theorem is in
`Complexitylib.Classes.NP.Verifier`, and `Classes.NP.WitnessConstruction` uses it
to prove the FNP-to-NP corollaries.
-/

@[expose] public section

namespace Complexity

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
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hsf : (fun w : List Bool => pairSnd (pairFst w)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
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
theorem mem_NP_of_poly_witness_internal {L L₀ : Language} (p : Polynomial ℕ) (hL₀ : L₀ ∈ P)
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
