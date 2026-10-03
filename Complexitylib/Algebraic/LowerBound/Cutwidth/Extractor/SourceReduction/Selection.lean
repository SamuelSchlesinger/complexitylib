/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Amplification.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.BadSeeds.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Selection.Internal

/-!
# Selecting parity-good source fixings and coordinates

One small common seed test gives good fixings for every low-order parity at
once. At each retained fixing, keep the coordinates with a candidate outside
that test. This is the selection step after equation (5) in Chattopadhyay and
Liao, *Extractors for Sum of Two Sources* (2021), Lemma 5.4.

The parity estimate is an explicit premise: an affine correlation breaker and
linearity of the sampler must still establish it for the actual XOR reduction.
The conclusion retains a `1 - δ` fraction of second-source fixings and
discards at most a `2ε` fraction of coordinates at each one. A subsequent
majority application must check positivity and the moment and margin budgets.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A somewhere sampler leaves many good fixings in each sufficiently large
uniform source, with the same failure bound as for arbitrary source weights. -/
theorem SomewhereSampler.exists_good_fibers {α Outer Candidate Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Ω]
    {S : α → Outer → Candidate → Ω} {L ε δ : ℝ}
    (sampler : SomewhereSampler S L ε δ) (Q : Finset α)
    (positive : 0 < Q.card) (source : L ≤ Q.card)
    (T : Finset Ω) (small : (T.card : ℝ) ≤ ε * Fintype.card Ω) :
    ∃ G ⊆ Q, (1 - δ) * Q.card ≤ G.card ∧
      ∀ y ∈ G, ((allHitSeeds S T y).card : ℝ) ≤ 2 * ε * Fintype.card Outer :=
  Internal.somewhereSampler_exists_good_fibers sampler Q positive source T small

/-- Union the bad-seed tests, apply the somewhere sampler, and retain all
coordinates with an escaping candidate. The distinguished coordinate for
each parity may be any member of that parity. The weights and coordinate
values are arbitrary here; the majority consumer additionally needs a
probability distribution, signs, and its quantitative budgets. -/
theorem SomewhereSampler.parity_fibers {α Source Choice Seed : Type*}
    [Fintype Source] [Fintype Choice] [Fintype Seed] {N : Nat}
    {s : Finset α} {w : α → ℝ} (σ : α → Source → Fin N → ℝ)
    {S : Source → Fin N → Choice → Seed} {L ε δ β η : ℝ}
    (sampler : SomewhereSampler S L ε δ) (Q : Finset Source)
    (positive : 0 < Q.card) (source : L ≤ Q.card)
    (bad : Finset (Fin N) → Choice → Finset Seed) (nonneg : 0 ≤ η)
    (seedBound : ∀ U ∈ parityTests (Fin N) 4, ∀ z,
      ((bad U z).card : ℝ) ≤ η * Fintype.card Seed)
    (budget : (N : ℝ) ^ 4 * Fintype.card Choice * η ≤ ε)
    (estimate : ∀ U ∈ parityTests (Fin N) 4, ∃ j ∈ U, ∀ z, ∀ y ∈ Q,
      S y j z ∉ bad U z →
        |weightedMean s w (fun x => ∏ i ∈ U, σ x y i)| ≤ β) :
    ∃ G ⊆ Q, (1 - δ) * Q.card ≤ G.card ∧
      ∀ y ∈ G, ∃ (m : Nat) (good : Fin m ↪ Fin N),
        ((N - m : Nat) : ℝ) ≤ 2 * ε * N ∧
        ParityBiasBound s w (fun x i => σ x y (good i)) β :=
  Internal.somewhereSampler_parity_fibers σ sampler Q positive source bad
    nonneg seedBound budget estimate

end Algebraic.Cutwidth.Extractor
