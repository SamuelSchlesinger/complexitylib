/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Binary

/-!
# A fixed binary alphabet still requires exponentially many deterministic states

A consequence of OpenAI's one-way-liveness lower bound and its crossing-diagram
proof, combined with the binary scanner constructed here. The full language
of the NFA has a two-way deterministic lower bound; this is not a promise problem.

Source: https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata
-/

public section

namespace Complexity.FiniteAutomaton

/-- The binary scanner uses nine states per original liveness vertex. -/
theorem card_binaryLivenessState (n : ℕ) :
    Fintype.card (BinaryLivenessState n) = 9 * (n + 2) :=
  BinaryLiveness.card_binary_state (n + 1)

/-- On encoded relation words the binary NFA accepts exactly one-way liveness. -/
theorem binaryLivenessNFA_accepts_code (n : ℕ) (w : List (Alphabet (n + 2))) :
    w.flatMap binaryLivenessCode ∈ (binaryLivenessNFA n).accepts ↔
      w ∈ oneWayLiveness (n + 2) :=
  BinaryLiveness.binary_liveness_accepts_code w

/-- Every equivalent two-way deterministic recognizer has exponential state cost,
even though the alphabet is the fixed two-element type `Bool`. -/
theorem binaryLivenessNFA_deterministic_lower_bound (n : ℕ)
    (positive : Bool) (s : ℕ) (D : DMachine Bool s)
    (hD : D.Recognizes positive (binaryLivenessNFA n).accepts) :
    2 ^ (n / 31) ≤ 4 * (s + if positive then 2 else 1) ^ 2 :=
  BinaryLiveness.binary_state_lower_bound n positive s D hD

end Complexity.FiniteAutomaton
