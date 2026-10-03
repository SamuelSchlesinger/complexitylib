/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs

/-!
# An exact proof witness for a prefix of the actual advice chain

The witness records a finite deterministic transcript of the original
sources, its exact normalized factors, original-source envelopes, and
agreement of both current states with the executed programs. Once advice
has differed, the tampered current state is fixed by the transcript.

This is internal proof data for constructing the induction in
Chattopadhyay--Goyal--Li Lemma 6.9. The public extraction theorem must build
this witness from the original sources; it cannot assume its existence.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

/-- One conservative error update shared by all three actual bit-step estimates. -/
noncomputable def adviceStepError (L e : Nat) (ρ α β : ℝ) : ℝ :=
  let K : ℝ := (2 : ℝ) ^ (2 ^ 62 * L)
  let J : ℝ := (2 : ℝ) ^ (2 ^ 142 * L)
  let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
  let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
  4 * ρ + 12 * ((2 : ℝ) ^ e)⁻¹ + K * D * (1 + D ^ 2) * (2 + D ^ 4) * α +
    3 * K * D ^ 2 / C + J * (2 * C ^ 3 + C ^ 5) * β

/-- Exact source factors and state uniformity after a concrete pair of program prefixes. -/
structure AdviceInvariant (n m L : Nat) {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    (p : (Z × B) × A → ℝ)
    (x : Z → A → Fin n → Bool) (y : Z → B → Fin m → Bool)
    (honest tampered : (Z × B) × A → Fin (matchedBlockOutputBits 64 L) → Bool)
    (separated : Prop) (ρ α β : ℝ) : Type (u + 1) where
  /-- The finite transcript alphabet after the processed prefix. -/
  Tag : Type u
  [tagFinite : Fintype Tag]
  /-- Recover the original shared tag from the current transcript. -/
  origin : Tag → Z
  /-- The deterministic current transcript of the original source sample. -/
  observe : (Z × B) × A → Tag
  origin_observe : ∀ a, origin (observe a) = a.1.1
  /-- The actual current transcript distribution. -/
  w : Tag → ℝ
  /-- The original left source conditioned on the current transcript. -/
  l : Tag → A → ℝ
  /-- The original right source conditioned on the current transcript. -/
  r : Tag → B → ℝ
  probability : IsProbabilityWeight w
  left_probability : ∀ t, IsProbabilityWeight (l t)
  right_probability : ∀ t, IsProbabilityWeight (r t)
  factored : mapWeight (fun a : (Z × B) × A => ((observe a, a.1.2), a.2)) p =
    factoredWeight w l r
  /-- The current honest program state, as a function of the retained right source. -/
  q : Tag → B → Fin (matchedBlockOutputBits 64 L) → Bool
  /-- The current tampered program state over the same right source. -/
  q' : Tag → B → Fin (matchedBlockOutputBits 64 L) → Bool
  honest_eq : ∀ a, q (observe a) a.1.2 = honest a
  tampered_eq : ∀ a, q' (observe a) a.1.2 = tampered a
  /-- The transcript's tampered state once advice has differed. -/
  fixedTampered : Tag → Fin (matchedBlockOutputBits 64 L) → Bool
  fixed : separated → ∀ t b, q' t b = fixedTampered t
  /-- An envelope for the original honest left-source joint masses. -/
  μ : Tag → ℝ
  /-- An envelope for the original honest right-source joint masses. -/
  ξ : Tag → ℝ
  left_nonnegative : ∀ t, 0 ≤ μ t
  right_nonnegative : ∀ t, 0 ≤ ξ t
  left_cap : ∀ t x₀, w t * mapWeight (x (origin t)) (l t) x₀ ≤ μ t
  right_cap : ∀ t y₀, w t * mapWeight (y (origin t)) (r t) y₀ ≤ ξ t
  left_sum : ∑ t, μ t ≤ α
  right_sum : ∑ t, ξ t ≤ β
  state : weightDist (retainedSeedWeight w r q)
    (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ

attribute [instance] AdviceInvariant.tagFinite

end Algebraic.Cutwidth.Extractor.Internal
