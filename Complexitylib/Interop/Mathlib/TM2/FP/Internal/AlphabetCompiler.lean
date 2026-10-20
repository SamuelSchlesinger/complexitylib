/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM2.FP.Internal.Compiler
public import Complexitylib.Interop.Mathlib.TM0.Alphabet
import Complexitylib.Interop.Mathlib.TM0.Alphabet.Internal.Copy
import Complexitylib.Classes.P.Composition
import Complexitylib.Classes.P.Cobham.Internal.Reverse
import Mathlib.Computability.NFA

/-!
# Canonical FP transfer with finite input and output alphabets

The compiler's stack tracks are unchanged. Explicit symbol codes add linear
parsing and emission cost. Palindromic codewords let ordinary binary reversal
restore the stack order, even when input and output alphabets differ.
-/

@[expose] public section

namespace Complexity.MathlibTM2

open Turing

lemma alphabetAdapter_input {α β : Type} (tm : FinTM2) [∀ k, Fintype (tm.Γ k)]
    (input : tm.Γ tm.k₀ ≃ α) (output : tm.Γ tm.k₁ ≃ β)
    {Q : Type} [Fintype Q] [Inhabited Q]
    (G : TM0.Machine (TM2to1.Γ' tm.K tm.Γ) Q) (w : List α) :
    (alphabetAdapter tm input output G).inputCells true w =
      TM2to1.trInit tm.k₀ (w.reverse.map input.symm) := by
  cases w with
  | nil => rfl
  | cons a xs =>
      simp only [TM2to1.trInit, List.map_reverse, List.reverse_reverse]
      change (alphabetAdapter tm input output G).inputSymbol true a ::
        (alphabetAdapter tm input output G).inputCells false xs = _
      rw [MathlibTM0.AlphabetMachine.inputCells_false]
      change (true, Function.update (fun _ => none) tm.k₀ (some (input.symm a))) ::
          xs.map (fun x => (false, Function.update (fun _ => none) tm.k₀ (some (input.symm x)))) =
        (true, Function.update (fun _ => none) tm.k₀ (some (input.symm a))) ::
          (xs.map input.symm).map (fun b => (false, Function.update (fun _ => none) tm.k₀ (some b)))
      rw [List.map_map]
      rfl

lemma coded_reversal {α β : Type} (ci : FiniteAlphabetCode α) (co : FiniteAlphabetCode β)
    (f : List α → List β) :
    (List.reverse ∘ ci.map co (fun xs => (f xs.reverse).reverse) ∘ List.reverse) =
      ci.map co f := by
  funext w
  simp only [Function.comp_def, FiniteAlphabetCode.map, FiniteAlphabetCode.decode_reverse_eq]
  cases ci.decode w <;> simp [FiniteAlphabetCode.encode_reverse_eq]

lemma mem_FP_encoded_proof {α β : Type} {f : List α → List β}
    (ci : FiniteAlphabetCode α) (co : FiniteAlphabetCode β)
    (computer : TM2ComputableInPolyTime id id f) [∀ k, Fintype (computer.tm.Γ k)] :
    ci.map co f ∈ FP := by
  obtain ⟨m, G, C, _, hG⟩ := exists_tm0_computer computer.tm
  obtain ⟨D, _, hD⟩ := exists_output_length_bound computer.tm
  let M := alphabetAdapter computer.tm computer.inputAlphabet computer.outputAlphabet G
  have hg : ci.map co (fun xs => (f xs.reverse).reverse) ∈ FP := by
    apply MathlibTM0.AlphabetMachine.mem_FP (M := M) ci co
      (p := Polynomial.C C * (Polynomial.X + computer.time + 1) ^ 2)
      (q := Polynomial.X + Polynomial.C D * computer.time)
    · intro xs
      obtain ⟨u, hu, c, hc, hh, ho⟩ := hG _ _ _ (computer.outputsFun xs.reverse)
      refine ⟨u, ?_, c, ?_, hh, ?_⟩
      · simpa using hu
      · rw [marked_run_eq_exec]
        change exec (TM0.step G) u (TM0.init (M.inputCells true xs)) = some c
        dsimp only [M]
        rw [alphabetAdapter_input]
        exact hc
      · intro j
        change ((c.Tape.nth j).2 computer.tm.k₁).map computer.outputAlphabet = _
        rw [ho, decode_trInit]
        simp [List.map_reverse]
    · intro xs
      have hd := hD _ _ _ (computer.outputsFun xs.reverse)
      simpa using hd
  have h := mem_FP_comp (mem_FP_comp reverse_mem_FP hg) reverse_mem_FP
  rw [coded_reversal] at h
  exact h

lemma mem_FP_encoded_on_dfa_proof {α β : Type} {f : List α → List β}
    (ci : FiniteAlphabetCode α) (co : FiniteAlphabetCode β)
    (computer : TM2ComputableAux α β) [∀ k, Fintype (computer.tm.Γ k)]
    {σ : Type} [Fintype σ] (D : DFA Bool σ) [DecidablePred (· ∈ D.accepts)]
    {p : Polynomial ℕ}
    (h : ∀ xs, ci.encode xs ∈ D.accepts →
      TM2OutputsInTime computer.tm (xs.map computer.inputAlphabet.symm)
        (some ((f xs).map computer.outputAlphabet.symm)) (p.eval xs.length)) :
    (fun bits => if bits ∈ D.accepts then ci.map co f bits else []) ∈ FP := by
  classical
  obtain ⟨m, G, C, _, hG⟩ := exists_tm0_computer computer.tm
  obtain ⟨L, _, hL⟩ := exists_output_length_bound computer.tm
  let M := alphabetAdapter computer.tm computer.inputAlphabet computer.outputAlphabet G
  let D' := D.toNFA.reverse.toDFA
  have accepts (w : List Bool) : w ∈ D'.accepts ↔ w.reverse ∈ D.accepts := by simp [D']
  have valid (xs : List α) (hx : ci.encode xs ∈ D'.accepts) :
      ci.encode xs.reverse ∈ D.accepts := by
    rw [FiniteAlphabetCode.encode_reverse_eq]
    exact (accepts _).mp hx
  let g (xs : List α) := (f xs.reverse).reverse
  have hg : (fun bits => if bits ∈ D'.accepts then ci.map co g bits else []) ∈ FP := by
    apply MathlibTM0.AlphabetMachine.mem_FP_on_dfa (M := M) ci co D'
      (p := Polynomial.C C * (Polynomial.X + p + 1) ^ 2)
      (q := Polynomial.X + Polynomial.C L * p)
    · intro xs hx
      obtain ⟨u, hu, c, hc, hh, ho⟩ := hG _ _ _ (h xs.reverse (valid xs hx))
      refine ⟨u, ?_, c, ?_, hh, ?_⟩
      · simpa using hu
      · rw [marked_run_eq_exec]
        change exec (TM0.step G) u (TM0.init (M.inputCells true xs)) = some c
        dsimp only [M]
        rw [alphabetAdapter_input]
        exact hc
      · intro j
        change ((c.Tape.nth j).2 computer.tm.k₁).map computer.outputAlphabet = _
        rw [ho, decode_trInit]
        simp [g, List.map_reverse]
    · intro xs hx
      have hl := hL _ _ _ (h xs.reverse (valid xs hx))
      simpa [g] using hl
  have hr := mem_FP_comp (mem_FP_comp reverse_mem_FP hg) reverse_mem_FP
  have heq :
      (List.reverse ∘ (fun bits => if bits ∈ D'.accepts then ci.map co g bits else []) ∘
        List.reverse) = (fun bits => if bits ∈ D.accepts then ci.map co f bits else []) := by
    funext bits
    by_cases hw : bits ∈ D.accepts
    · simpa only [Function.comp_def, accepts, List.reverse_reverse, hw, ite_true] using
        congrFun (coded_reversal ci co f) bits
    · simp [Function.comp_def, accepts, hw]
  rw [heq] at hr
  exact hr

end Complexity.MathlibTM2
