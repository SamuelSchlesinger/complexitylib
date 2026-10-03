/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Output.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Output
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Positivity

/-!
# Exact successor certificates for an actual advice bit

Compose the old deterministic observation with the actual common or observed
output transcript. Both constructions retain the original latent states,
preserve the original tag pointwise, and recover both executed next states.
The observed construction stores the tampered next state on every row.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

variable {n m L : Nat} {Z A B : Type u} [Fintype Z] [Fintype A] [Fintype B]
  {p : (Z × B) × A → ℝ} {x : Z → A → Fin n → Bool} {y : Z → B → Fin m → Bool}
  {honest tampered : (Z × B) × A → Fin (matchedBlockOutputBits 64 L) → Bool}
  {separated : Prop} {ρ α β : ℝ}

theorem AdviceInvariant.advance_weak
    (I : AdviceInvariant n m L p x y honest tampered separated ρ α β)
    (e : Nat) (x' : Z → A → Fin n → Bool) (y' : Z → B → Fin m → Bool)
    (b b' : Bool) (phase : Prop) (notSeparated : ¬ phase) {error : ℝ}
    (near : weightDist
      (flipFlopOutputWeight n m L e I.w I.l I.r
        (fun t => x (I.origin t)) (fun t => x' (I.origin t))
        (fun t => y (I.origin t)) (fun t => y' (I.origin t)) I.q I.q' b b')
      (uniformSecondWeight (flipFlopOutputWeight n m L e I.w I.l I.r
        (fun t => x (I.origin t)) (fun t => x' (I.origin t))
        (fun t => y (I.origin t)) (fun t => y' (I.origin t)) I.q I.q' b b')) ≤ error) :
    Nonempty (AdviceInvariant n m L p x y
      (fun a => flipFlopStep n m L e (x a.1.1 a.2) (y a.1.1 a.1.2) (honest a) b)
      (fun a => flipFlopStep n m L e (x' a.1.1 a.2) (y' a.1.1 a.1.2) (tampered a) b')
      phase error ((Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ 8 * α)
      ((Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) ^ 5 * β)) := by
  let xl := fun t => x (I.origin t)
  let xt := fun t => x' (I.origin t)
  let yr := fun t => y (I.origin t)
  let yt := fun t => y' (I.origin t)
  let observe := fun a : (Z × B) × A =>
    flipFlopTranscript n m L e xl xt yr yt I.q I.q' b b' ((I.observe a, a.1.2), a.2)
  obtain ⟨hw, hl, hr⟩ := flipFlopTranscript_probability n m L e I.w I.l I.r
    xl xt yr yt I.q I.q' b b' I.probability I.left_probability I.right_probability
  have factor := flipFlopTranscript_factored n m L e I.w I.l I.r
    xl xt yr yt I.q I.q' b b' I.left_probability I.right_probability
  rw [← I.factored, mapWeight_comp] at factor
  have projected := weightDist_uniformSecond_map_first_le
    (flipFlopOutputWeight n m L e I.w I.l I.r xl xt yr yt I.q I.q' b b') Prod.fst
  rw [flipFlopOutputWeight_retainedSeed n m L e I.w I.l I.r xl xt yr yt I.q I.q' b b'
    I.probability I.left_probability I.right_probability] at projected
  refine ⟨{
    Tag := FlipFlopTranscript I.Tag L
    tagFinite := inferInstance
    origin := fun t => I.origin t.1.1.1.1
    observe := observe
    origin_observe := ?_
    w := flipFlopTranscriptWeight n m L e I.w I.l I.r xl xt yr yt I.q I.q' b b'
    l := flipFlopTranscriptLeft n L e I.l xl xt
    r := flipFlopTranscriptRight m L e I.r yr yt I.q I.q' b b'
    probability := hw
    left_probability := hl
    right_probability := hr
    factored := factor
    q := flipFlopHonestOutput m L e yr b
    q' := flipFlopTamperedOutput m L e yt b'
    honest_eq := ?_
    tampered_eq := ?_
    fixedTampered := fun _ _ => false
    fixed := fun h => False.elim (notSeparated h)
    μ := flipFlopTranscriptLeftEnvelope m L e I.μ I.r yr yt I.q I.q' b b'
    ξ := flipFlopTranscriptRightEnvelope n L e I.ξ I.l xl xt
    left_nonnegative := flipFlopTranscriptLeftEnvelope_nonnegative
      m L e I.μ I.r yr yt I.q I.q' b b' I.left_nonnegative I.right_probability
    right_nonnegative := flipFlopTranscriptRightEnvelope_nonnegative
      n L e I.ξ I.l xl xt I.right_nonnegative I.left_probability
    left_cap := flipFlopTranscript_left_envelope n m L e I.w I.l I.r
      xl xt yr yt I.q I.q' b b' I.μ I.probability I.left_probability I.right_probability
      I.left_cap
    right_cap := flipFlopTranscript_right_envelope n m L e I.w I.l I.r
      xl xt yr yt I.q I.q' b b' I.ξ I.probability I.left_probability I.right_probability
      I.right_cap
    left_sum := ?_
    right_sum := ?_
    state := projected.trans near }⟩
  · intro a
    exact I.origin_observe a
  · intro a
    change flipFlopHonestOutput m L e yr b
      (flipFlopTranscript n m L e xl xt yr yt I.q I.q' b b'
        ((I.observe a, a.1.2), a.2)) a.1.2 = _
    rw [flipFlopHonestOutput_eq_step]
    simp only [xl, yr, I.origin_observe, I.honest_eq]
  · intro a
    change flipFlopTamperedOutput m L e yt b'
      (flipFlopTranscript n m L e xl xt yr yt I.q I.q' b b'
        ((I.observe a, a.1.2), a.2)) a.1.2 = _
    rw [flipFlopTamperedOutput_eq_step]
    simp only [xt, yt, I.origin_observe, I.tampered_eq]
  · rw [flipFlopTranscriptLeftEnvelope_sum m L e I.μ I.r yr yt I.q I.q' b b'
      I.right_probability]
    exact mul_le_mul_of_nonneg_left I.left_sum (by positivity)
  · rw [flipFlopTranscriptRightEnvelope_sum n L e I.ξ I.l xl xt I.left_probability]
    have hβ : 0 ≤ β := (Finset.sum_nonneg (fun t _ => I.right_nonnegative t)).trans I.right_sum
    have hC : 1 ≤ (Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) := by
      exact_mod_cast (show 1 ≤ Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
        from Fintype.card_pos)
    exact (mul_le_mul_of_nonneg_left I.right_sum (by positivity)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC (by decide : 4 ≤ 5)) hβ)

theorem AdviceInvariant.advance_observed
    (I : AdviceInvariant n m L p x y honest tampered separated ρ α β)
    (e : Nat) (x' : Z → A → Fin n → Bool) (y' : Z → B → Fin m → Bool)
    (b b' : Bool) (phase : Prop) {error : ℝ}
    (near : weightDist
      (flipFlopObservedOutputWeight n m L e I.w I.l I.r
        (fun t => x (I.origin t)) (fun t => x' (I.origin t))
        (fun t => y (I.origin t)) (fun t => y' (I.origin t)) I.q I.q' b b')
      (uniformSecondWeight (flipFlopObservedOutputWeight n m L e I.w I.l I.r
        (fun t => x (I.origin t)) (fun t => x' (I.origin t))
        (fun t => y (I.origin t)) (fun t => y' (I.origin t)) I.q I.q' b b')) ≤ error) :
    Nonempty (AdviceInvariant n m L p x y
      (fun a => flipFlopStep n m L e (x a.1.1 a.2) (y a.1.1 a.1.2) (honest a) b)
      (fun a => flipFlopStep n m L e (x' a.1.1 a.2) (y' a.1.1 a.1.2) (tampered a) b')
      phase error ((Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ 8 * α)
      ((Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) ^ 5 * β)) := by
  let xl := fun t => x (I.origin t)
  let xt := fun t => x' (I.origin t)
  let yr := fun t => y (I.origin t)
  let yt := fun t => y' (I.origin t)
  let observe := fun a : (Z × B) × A =>
    flipFlopObservedTranscript n m L e xl xt yr yt I.q I.q' b b'
      ((I.observe a, a.1.2), a.2)
  obtain ⟨hw, hl, hr⟩ := flipFlopObserved_probability n m L e I.w I.l I.r
    xl xt yr yt I.q I.q' b b' I.probability I.left_probability I.right_probability
  have factor := flipFlopObserved_factored n m L e I.w I.l I.r
    xl xt yr yt I.q I.q' b b' I.left_probability I.right_probability
  rw [← I.factored, mapWeight_comp] at factor
  have projected := weightDist_uniformSecond_map_first_le
    (flipFlopObservedOutputWeight n m L e I.w I.l I.r xl xt yr yt I.q I.q' b b') Prod.fst
  rw [flipFlopObservedOutputWeight_retainedSeed n m L e I.w I.l I.r xl xt yr yt I.q I.q' b b'
    I.probability I.left_probability I.right_probability] at projected
  refine ⟨{
    Tag := FlipFlopObservedTranscript I.Tag L
    tagFinite := inferInstance
    origin := fun t => I.origin t.1.1.1.1.1
    observe := observe
    origin_observe := ?_
    w := flipFlopObservedWeight n m L e I.w I.l I.r xl xt yr yt I.q I.q' b b'
    l := flipFlopObservedLeft n L e I.l xl xt
    r := flipFlopObservedRight m L e I.r yr yt I.q I.q' b b'
    probability := hw
    left_probability := hl
    right_probability := hr
    factored := factor
    q := fun t => flipFlopHonestOutput m L e yr b t.1
    q' := fun t _ => t.2
    honest_eq := ?_
    tampered_eq := ?_
    fixedTampered := Prod.snd
    fixed := fun _ _ _ => rfl
    μ := flipFlopObservedLeftEnvelope m L e I.μ I.r yr yt I.q I.q' b b'
    ξ := flipFlopObservedRightEnvelope n L e I.ξ I.l xl xt
    left_nonnegative := flipFlopObservedLeftEnvelope_nonnegative
      m L e I.μ I.r yr yt I.q I.q' b b' I.left_nonnegative I.right_probability
    right_nonnegative := flipFlopObservedRightEnvelope_nonnegative
      n L e I.ξ I.l xl xt I.right_nonnegative I.left_probability
    left_cap := flipFlopObserved_left_envelope n m L e I.w I.l I.r
      xl xt yr yt I.q I.q' b b' I.μ I.probability I.left_probability I.right_probability
      I.left_cap
    right_cap := flipFlopObserved_right_envelope n m L e I.w I.l I.r
      xl xt yr yt I.q I.q' b b' I.ξ I.probability I.left_probability I.right_probability
      I.right_cap
    left_sum := ?_
    right_sum := ?_
    state := projected.trans near }⟩
  · intro a
    exact I.origin_observe a
  · intro a
    change flipFlopHonestOutput m L e yr b
      (flipFlopTranscript n m L e xl xt yr yt I.q I.q' b b'
        ((I.observe a, a.1.2), a.2)) a.1.2 = _
    rw [flipFlopHonestOutput_eq_step]
    simp only [xl, yr, I.origin_observe, I.honest_eq]
  · intro a
    dsimp only [observe, flipFlopObservedTranscript]
    simp only [xt, yt, I.origin_observe, I.tampered_eq]
  · rw [flipFlopObservedLeftEnvelope_sum m L e I.μ I.r yr yt I.q I.q' b b'
      I.right_probability]
    exact mul_le_mul_of_nonneg_left I.left_sum (by positivity)
  · rw [flipFlopObservedRightEnvelope_sum n L e I.ξ I.l xl xt I.left_probability]
    exact mul_le_mul_of_nonneg_left I.right_sum (by positivity)

end Algebraic.Cutwidth.Extractor.Internal
