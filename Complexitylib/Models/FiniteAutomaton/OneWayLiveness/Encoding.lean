/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Encoding

/-!
# The state lower bound survives arbitrary word encodings

A consequence of OpenAI's crossing-diagram and relation-divisor argument:
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Syntactic.lean

Replace each relation letter by a word over any target alphabet. Any two-way
deterministic machine agreeing with one-way liveness on all encoded words
still satisfies the original state lower bound, with exactly the same constants.
The theorem imposes no bound on code lengths. Its behavior on other inputs
does not enter the hypothesis. In particular, the theorem applies to every
language extending the prescribed answers on encoded words.

The proof feeds the product of the encoded word's crossing diagrams into the
source's representation theorem. This avoids the extra states of a simulation
that explicitly stores the position within a codeword.
-/

public section

namespace Complexity.FiniteAutomaton

/-- The exact liveness state lower bound transfers through every letter-to-word
encoding, independently of the alphabet and of the encoded word lengths. -/
theorem encoded_oneWayLiveness_lower_bound {Alpha : Type}
    (h : ℕ) (hh : 2 ≤ h) (code : Alphabet h → List Alpha)
    (positive : Bool) (s : ℕ) (D : DMachine Alpha s)
    (hD : ∀ w, D.Accepts positive (w.flatMap code) ↔ w ∈ oneWayLiveness h) :
    2 ^ ((h - 2) / 31) ≤ 4 * (s + if positive then 2 else 1) ^ 2 :=
  encoded_oneWayLiveness_lower_bound_proof h hh code positive s D hD

end Complexity.FiniteAutomaton
