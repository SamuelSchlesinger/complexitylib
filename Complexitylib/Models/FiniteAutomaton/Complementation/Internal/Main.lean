/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Recognition
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Representation

/-!
# Two-way complementation: main

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Main.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

/-- An n-state source language requires exponentially many states for any 2NFA complement. -/
theorem complementation_lower_bound (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      ∀ s : ℕ, ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin s),
        B.language = A.languageᶜ → 2 ^ ((n - 4) / 127) ≤ 2 * (s + 1) := by
  obtain ⟨A, hA⟩ := sourceLanguage_state_bound (Fin (n - 2))
  have hsize : Fintype.card (Fin (n - 2)) + 2 = n := by simp; omega
  let A' := A.reindex (finCongr hsize)
  refine ⟨A', ?_⟩
  intro s B hB
  have hAlang : A'.language = sourceLanguage (Fin (n - 2)) := by
    rw [TwoNFA.reindex_language, hA]
  obtain ⟨τ, l, r, a, b, hzero, hmul, hrecognition⟩ := B.diagram_representation
  have hbound := diagram_recognition_lower_bound (n - 2) (s + 1) (by omega) (by omega)
    τ hzero hmul l r a b (by
      intro w
      rw [← hrecognition w, hB, hAlang]
      rfl)
  simpa only [lossBound, Nat.sub_sub, Nat.reduceAdd] using hbound

/-- The real-valued lower bound for arbitrary finite target state sets. -/
theorem complementation_lower_bound_finite (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      ∀ (Q : Type*) [Fintype Q], ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        B.language = A.languageᶜ →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q : ℝ) := by
  obtain ⟨A, hA⟩ := complementation_lower_bound n hn
  refine ⟨A, ?_⟩
  intro Q _ B hB
  have hbound := hA (Fintype.card Q) (B.reindex (Fintype.equivFin Q)) (by
    rw [TwoNFA.reindex_language, hB])
  have hreal : (2 : ℝ) ^ ((n - 4) / 127) ≤ 2 * ((Fintype.card Q : ℝ) + 1) := by
    exact_mod_cast hbound
  linarith

/-- Letter maps commute with tape lookup and preserve the two endmarkers. -/
theorem tapeSymbol_map {Sigma Gamma : Type*} (f : Sigma → Gamma) (w : List Sigma)
    (p : Fin (w.length + 2)) :
    tapeSymbol (w.map f) ⟨p.val, by simp⟩ =
      Sum.map id f (tapeSymbol w p) := by
  simp only [tapeSymbol, List.length_map, List.getElem_map]
  split_ifs <;> rfl

/-- Pull an automaton back along a letter map, preserving its state set. -/
def TwoNFA.pullAlphabet {Sigma Gamma Q : Type*} (A : TwoNFA Gamma Q) (f : Sigma → Gamma) :
    TwoNFA Sigma Q where
  initial := A.initial
  accepting := A.accepting
  transition q symbol := A.transition q (Sum.map id f symbol)

/-- Letter pullback accepts exactly the words whose images the original machine accepts. -/
theorem TwoNFA.pullAlphabet_language {Sigma Gamma Q : Type*} (A : TwoNFA Gamma Q)
    (f : Sigma → Gamma) (w : List Sigma) :
    w ∈ (A.pullAlphabet f).language ↔ w.map f ∈ A.language := by
  let e : (Q × Fin (w.length + 2)) ≃ (Q × Fin ((w.map f).length + 2)) :=
    Equiv.prodCongr (Equiv.refl Q) (finCongr (by simp))
  have hstep (c d : Q × Fin (w.length + 2)) :
      (e c, e d) ∈ A.step (w.map f) ↔ (c, d) ∈ (A.pullAlphabet f).step w := by
    change (∃ move : Fin 3,
      (d.1, move) ∈ A.transition c.1
        (tapeSymbol (w.map f) ⟨c.2.val, by simp⟩) ∧
      (d.2.val : ℤ) = (c.2.val : ℤ) + (move.val : ℤ) - 1) ↔ _
    rw [tapeSymbol_map]
    rfl
  constructor
  · rintro ⟨c, hc, hrun⟩
    refine ⟨e c, hc, ?_⟩
    exact (relStar_equiv_iff e _ _ hstep (A.initial, ⟨0, by omega⟩) c).mpr hrun
  · rintro ⟨d, hd, hrun⟩
    refine ⟨e.symm d, hd, ?_⟩
    apply (relStar_equiv_iff e _ _ hstep (A.initial, ⟨0, by omega⟩) (e.symm d)).mp
    rw [Equiv.apply_symm_apply]
    exact hrun

/-- No real polynomial bounds the powers of two at all natural inputs. -/
theorem polynomial_not_bound_two_pow (p : Polynomial ℝ) :
    ¬ ∀ n : ℕ, (2 : ℝ) ^ n ≤ p.eval (n : ℝ) := by
  have hlittle (q : Polynomial ℝ) :
      Asymptotics.IsLittleO Filter.atTop (fun n : ℕ => q.eval (n : ℝ))
        (fun n : ℕ => (2 : ℝ) ^ n) := by
    induction q using Polynomial.induction_on' with
    | add q r hq hr => simpa only [Polynomial.eval_add] using hq.add hr
    | monomial k a =>
      simpa only [Polynomial.eval_monomial] using
        (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k
          (by norm_num : (1 : ℝ) < 2)).const_mul_left a
  intro hbound
  obtain ⟨n, hn⟩ := (hlittle p |>.bound (by norm_num : (0 : ℝ) < 1 / 2)).exists
  have hpos : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have habs := le_abs_self (p.eval (n : ℝ))
  have hle := hbound n
  simp only [Real.norm_eq_abs, abs_of_pos hpos] at hn
  linarith

/-- There is no polynomial state bound for complementation over all finite alphabets. -/
theorem no_polynomial_complementation :
    ¬ ∃ p : Polynomial ℝ, ∀ n k : ℕ, ∀ A : TwoNFA (Fin k) (Fin n),
      ∃ s : ℕ, ∃ B : TwoNFA (Fin k) (Fin s),
        B.language = A.languageᶜ ∧ (s : ℝ) ≤ p.eval (n : ℝ) := by
  classical
  rintro ⟨p, hp⟩
  let q : Polynomial ℝ := Polynomial.C 2 *
    (p.comp (Polynomial.C 127 * Polynomial.X + Polynomial.C 4) + Polynomial.C 1)
  apply polynomial_not_bound_two_pow q
  intro t
  let n := 127 * t + 4
  obtain ⟨A, hA⟩ := complementation_lower_bound n (by dsimp [n]; omega)
  let Sigma := SetRel (Fin (n - 2)) (Fin (n - 2))
  let e : Sigma ≃ Fin (Fintype.card Sigma) := Fintype.equivFin Sigma
  obtain ⟨s, B, hB, hs⟩ := hp n (Fintype.card Sigma) (A.pullAlphabet e.symm)
  have hcomplement : (B.pullAlphabet e).language = A.languageᶜ := by
    ext w
    rw [B.pullAlphabet_language, hB]
    change ¬ w.map e ∈ (A.pullAlphabet e.symm).language ↔ ¬ w ∈ A.language
    rw [A.pullAlphabet_language]
    simp only [List.map_map, Equiv.symm_comp_self, List.map_id]
  have hbound := hA s (B.pullAlphabet e) hcomplement
  have hexponent : (n - 4) / 127 = t := by dsimp [n]; omega
  rw [hexponent] at hbound
  have hreal : (2 : ℝ) ^ t ≤ 2 * ((s : ℝ) + 1) := by exact_mod_cast hbound
  change (2 : ℝ) ^ t ≤ q.eval (t : ℝ)
  simp only [q, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_C, Polynomial.eval_X]
  have hn : (n : ℝ) = 127 * (t : ℝ) + 4 := by simp [n]
  rw [hn] at hs
  linarith

end Complementation.Internal

end Complexity.FiniteAutomaton
