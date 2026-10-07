/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Main
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Bridge
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness

/-!
# Word encodings preserve the complementation lower bound

Feed the diagram of each encoded word into OpenAI's order-reversing relation
image theorem. Code lengths do not enter the state bound. The existing binary
liveness NFA then gives a fixed-alphabet lower bound for the full complement
language, and exponential growth rules out a polynomial complementation bound.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton.Complementation.Internal

/-- Curried form of a binary relation. -/
def fromSetRel {H : Type} (R : SetRel H H) : BRel H := ⟨fun x y => (x, y) ∈ R⟩

theorem fromSetRel_product {H : Type} (w : List (SetRel H H)) :
    (w.map fromSetRel).prod = fromSetRel (relationProduct w) := by
  induction w with
  | nil => rfl
  | cons R w ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      rfl

theorem live_map_fromSetRel {H : Type} (w : List (SetRel H H)) :
    BRel.Live (w.map fromSetRel) ↔ (relationProduct w).Nonempty := by
  rw [BRel.Live, fromSetRel_product]
  exact ⟨fun ⟨x, y, h⟩ => ⟨(x, y), h⟩, fun ⟨(x, y), h⟩ => ⟨x, y, h⟩⟩

theorem encoded_complement_lower_bound {Alpha : Type}
    (h : ℕ) (hh : 2 ≤ h) (code : Alphabet h → List Alpha)
    (s : ℕ) (M : NMachine Alpha s)
    (hM : ∀ w, M.Accepts false (w.flatMap code) ↔ w ∉ oneWayLiveness h) :
    2 ^ ((h - 2) / 127) ≤ 2 * (s + 1) := by
  obtain ⟨τ, l, r, a, b, hzero, hmul, hrecognition⟩ := (asSource M).diagram_representation
  let encode (w : List (SetRel (Fin h) (Fin h))) := (w.map fromSetRel).flatMap code
  have hencode (w) : M.Accepts false (encode w) ↔ ¬ (relationProduct w).Nonempty :=
    (hM _).trans (not_congr (live_map_fromSetRel w))
  apply diagram_recognition_lower_bound h (s + 1) hh (by lia)
    (fun w => τ (encode w)) (by simpa [encode] using hzero)
    (fun u v => by
      simpa only [encode, List.map_append, List.flatMap_append] using
        hmul (encode u) (encode v)) l r a b
  intro w
  exact (hrecognition (encode w)).symm.trans
    ((asSource_language M _).trans (hencode w))

theorem binary_complement_lower_bound (n s : ℕ) (M : NMachine Bool s)
    (hM : M.Recognizes false ((binaryLivenessNFA n).accepts)ᶜ) :
    2 ^ (n / 127) ≤ 2 * (s + 1) := by
  have h := encoded_complement_lower_bound (n + 2) (by lia)
    binaryLivenessCode s M (fun w => (hM _).trans
      (not_congr (binaryLivenessNFA_accepts_code n w)))
  simpa only [Nat.add_sub_cancel] using h

theorem liveness_complement_lower_bound (h : ℕ) (hh : 2 ≤ h)
    (s : ℕ) (M : NMachine (Alphabet h) s)
    (hM : M.Recognizes false ((livenessNFA h).accepts)ᶜ) :
    2 ^ ((h - 2) / 127) ≤ 2 * (s + 1) := by
  apply encoded_complement_lower_bound h hh (fun R => [R]) s M
  intro w
  simpa only [List.flatMap_singleton', livenessNFA_accepts, Set.mem_compl_iff] using hM w

theorem no_binary_polynomial_complementation :
    ¬ ∃ p : Polynomial ℝ, ∀ (Q : Type) [Fintype Q] (A : NFA Bool Q),
      ∃ s : ℕ, ∃ M : NMachine Bool s,
        M.Recognizes false A.acceptsᶜ ∧ (s : ℝ) ≤ p.eval (Fintype.card Q : ℝ) := by
  rintro ⟨p, hp⟩
  let q : Polynomial ℝ := Polynomial.C 2 *
    (p.comp (Polynomial.C 9 * (Polynomial.C 127 * Polynomial.X + Polynomial.C 2)) +
      Polynomial.C 1)
  apply polynomial_not_bound_two_pow q
  intro t
  obtain ⟨s, M, hM, hs⟩ := hp (BinaryLivenessState (127 * t)) (binaryLivenessNFA (127 * t))
  have hnat := binary_complement_lower_bound (127 * t) s M hM
  have hpow : (2 : ℝ) ^ t ≤ 2 * ((s : ℝ) + 1) := by
    have he : 127 * t / 127 = t := by lia
    rw [he] at hnat
    exact_mod_cast hnat
  rw [card_binaryLivenessState] at hs
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hs
  dsimp [q]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_C, Polynomial.eval_X]
  linarith

end Complexity.FiniteAutomaton.Complementation.Internal
