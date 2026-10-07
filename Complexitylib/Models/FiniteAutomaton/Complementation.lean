/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Encoding

/-!
# Exponential state complexity of nondeterministic complementation

The source is OpenAI's two-way complementation formalization:
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Main.lean

The public statements use the existing `NMachine` and ordinary Mathlib `NFA`.
Acceptance here permits a zero-step run (`positive = false`). The bridge
preserves the state count. The source's diagram argument also yields a lower
bound through every letter-to-word encoding, independent of codeword lengths.

Combining that bound with the existing binary liveness scanner proves an
exponential lower bound for the full complement of a small binary NFA's language.
The encoded-word agreement is only the proof method; the binary result concerns
a language of all finite binary words. These are checked consequences without
any assertion that the source authors were unaware of them.
-/

public section

namespace Complexity.FiniteAutomaton

/-- Any encoded-word recognizer for the complement of liveness needs exponentially
many states, even with two-way nondeterminism and arbitrary codeword lengths. -/
theorem encoded_oneWayLiveness_complement_lower_bound {Alpha : Type}
    (h : ℕ) (hh : 2 ≤ h) (code : Alphabet h → List Alpha)
    (s : ℕ) (M : NMachine Alpha s)
    (hM : ∀ w, M.Accepts false (w.flatMap code) ↔ w ∉ oneWayLiveness h) :
    2 ^ ((h - 2) / 127) ≤ 2 * (s + 1) :=
  Complementation.Internal.encoded_complement_lower_bound h hh code s M hM

/-- The complement of the ordinary `h`-state liveness NFA requires exponentially
many states in every two-way nondeterministic recognizer. -/
theorem livenessNFA_complement_lower_bound (h : ℕ) (hh : 2 ≤ h)
    (s : ℕ) (M : NMachine (Alphabet h) s)
    (hM : M.Recognizes false ((livenessNFA h).accepts)ᶜ) :
    2 ^ ((h - 2) / 127) ≤ 2 * (s + 1) :=
  Complementation.Internal.liveness_complement_lower_bound h hh s M hM

/-- Already a one-way endmarker automaton has an exponentially expensive
complement when the complementing machine may use two-way nondeterminism. -/
theorem exists_oneWay_nfa_complementation_lower_bound (h : ℕ) (hh : 2 ≤ h) :
    ∃ N : NMachine (Alphabet h) (h + 3), N.NoLeft ∧
      ∀ (s : ℕ) (M : NMachine (Alphabet h) s),
        (∀ w, M.Accepts false w ↔ ¬ N.Accepts false w) →
          2 ^ ((h - 2) / 127) ≤ 2 * (s + 1) := by
  obtain ⟨N, hleft, hN⟩ := oneWayLiveness_small_nfa h
  refine ⟨N, hleft, ?_⟩
  intro s M hM
  apply livenessNFA_complement_lower_bound h hh s M
  intro w
  simpa only [livenessNFA_accepts, Set.mem_compl_iff] using
    (hM w).trans (not_congr (hN false w))

/-- The complement of the `9 * (n + 2)`-state binary scanner requires an
exponential number of states even in a two-way nondeterministic automaton. -/
theorem binaryLivenessNFA_complement_lower_bound (n s : ℕ) (M : NMachine Bool s)
    (hM : M.Recognizes false ((binaryLivenessNFA n).accepts)ᶜ) :
    2 ^ (n / 127) ≤ 2 * (s + 1) :=
  Complementation.Internal.binary_complement_lower_bound n s M hM

/-- No polynomial in the source state count bounds complementation of ordinary
binary NFAs by two-way NFAs, under zero-step finite-run acceptance. -/
theorem no_binary_nfa_polynomial_complementation :
    ¬ ∃ p : Polynomial ℝ, ∀ (Q : Type) [Fintype Q] (A : NFA Bool Q),
      ∃ s : ℕ, ∃ M : NMachine Bool s,
        M.Recognizes false A.acceptsᶜ ∧ (s : ℝ) ≤ p.eval (Fintype.card Q : ℝ) :=
  Complementation.Internal.no_binary_polynomial_complementation

end Complexity.FiniteAutomaton
