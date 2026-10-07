/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Main
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.NFABridge
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Encoding
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Binary

/-!
# Exponential state complexity of one-way liveness

OpenAI, *An Exponential Two-Way Deterministic State Lower Bound for One-Way
Liveness* (25 September 2026):
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-exponential-two-way-deterministic-state-lower-bound-for-one-way-liveness-September-25-2026

The language consists of words of binary relations whose product is nonempty.
It has an `h + 3`-state one-way nondeterministic endmarker automaton, while every
equivalent two-way deterministic automaton has exponentially many states.
Both the zero-length-run and positive-run acceptance conventions are covered.
The source proof also rules out polynomial simulation even when its input
machines are required to be one-way.

The NFA bridge identifies the same language with a standard `h`-state Mathlib
NFA. This alphabet consists of relations on `Fin h`; it is finite but grows
with `h`. The imported `Binary` module gives a new fixed-binary-alphabet
consequence using a linear-size truth-table scanner.
-/

public section

namespace Complexity.FiniteAutomaton

/-- One-way liveness is recognized by the ordinary `h`-state Mathlib NFA. -/
theorem livenessNFA_accepts (h : ℕ) :
    (livenessNFA h).accepts = oneWayLiveness h :=
  livenessNFA_accepts_proof h

/-- The one-way upper bound in the endmarker model, under both acceptance conventions. -/
theorem oneWayLiveness_small_nfa (h : ℕ) :
    ∃ N : NMachine (Alphabet h) (h + 3), N.NoLeft ∧
      ∀ positive : Bool, N.Recognizes positive (oneWayLiveness h) :=
  small_nfa h

/-- Every two-way deterministic recognizer for one-way liveness has exponential state cost. -/
theorem oneWayLiveness_deterministic_lower_bound (h : ℕ) (hh : 2 ≤ h)
    (positive : Bool) (s : ℕ) (D : DMachine (Alphabet h) s)
    (hD : D.Recognizes positive (oneWayLiveness h)) :
    2 ^ ((h - 2) / 31) ≤ 4 * (s + if positive then 2 else 1) ^ 2 :=
  deterministic_lower_bound h hh positive s D hD

/-- The lower bound applies to a language represented by an ordinary Mathlib NFA. -/
theorem livenessNFA_deterministic_lower_bound (h : ℕ) (hh : 2 ≤ h)
    (positive : Bool) (s : ℕ) (D : DMachine (Alphabet h) s)
    (hD : D.Recognizes positive (livenessNFA h).accepts) :
    2 ^ ((h - 2) / 31) ≤ 4 * (s + if positive then 2 else 1) ^ 2 :=
  oneWayLiveness_deterministic_lower_bound h hh positive s D
    (by simpa only [livenessNFA_accepts] using hD)

/-- No alphabet-independent polynomial simulation of one-way NFAs by two-way DFAs exists. -/
theorem no_oneWay_polynomial_simulation (positive : Bool) :
    ¬ OneWayPolynomialSimulation positive :=
  no_oneWay_polynomial_simulation_proof positive

/-- Consequently, unrestricted two-way NFAs admit no such polynomial deterministic simulation. -/
theorem no_polynomial_simulation (positive : Bool) : ¬ PolynomialSimulation positive := by
  rintro ⟨C, c, hC, hc, hsim⟩
  exact no_oneWay_polynomial_simulation positive
    ⟨C, c, hC, hc, fun Alpha inst n N _ => hsim Alpha inst n N⟩

end Complexity.FiniteAutomaton
