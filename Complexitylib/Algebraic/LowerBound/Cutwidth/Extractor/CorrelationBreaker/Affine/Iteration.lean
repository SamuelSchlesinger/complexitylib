/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Internal.Execution
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Internal.Envelope

/-!
# Exact semantics and source accounting for repeated affine rounds

Every finite iterate records the actual round transcripts and preserves
both original latent states. Its factored law is exactly a deterministic
image of the original law, and the XOR of its side contributions is the
actual repeated four-call algorithm. Conditional kernels remain normalized
at impossible messages as well as messages of positive mass.

Original source envelopes remain valid throughout. Their total masses
are multiplied by the short-message alphabet to powers twice and four
times the number of rounds. These exact laws support the iteration in
Chattopadhyay--Liao, *Extractors for Sum of Two Sources*, Theorem 6.1,
printed pp.23--25: <https://arxiv.org/abs/2110.12652>. The statistical
subset invariants and parameter choices are proved in `Iteration.Extraction`
and `Iteration.Parameters` (`affineCorrelationBreaker_parameters_dist_le`),
and the uniform runtime in `Affine.Program`
(`affineCorrelationBreakerSelectedEval_mem_FP`).
-/

public section

namespace Algebraic.Cutwidth.Extractor

variable {n d h t L : Nat} {Z A B : Type*}

/-- Zero rounds return the supplied old row without reading new randomness. -/
theorem affineRoundsOutput_zero (n d h L e : Nat) (x : Fin n → Bool) (y : Fin d → Bool)
    (row : Fin (matchedBlockOutputBits h L) → Bool) :
    affineRoundsOutput n d h L e 0 x y row = row := rfl

/-- Each additional round rereads the same original inputs and the preceding actual row. -/
theorem affineRoundsOutput_succ (n d h L e i : Nat)
    (x : Fin n → Bool) (y : Fin d → Bool)
    (row : Fin (matchedBlockOutputBits h L) → Bool) :
    affineRoundsOutput n d h L e (i + 1) x y row =
      affineRoundOutput n d h L e x y (affineRoundsOutput n d h L e i x y row) := rfl

/-- Zero transitions preserve the entire supplied state. -/
theorem AffineIterationState.iterate_zero [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e : Nat) : s.iterate e 0 = s := rfl

/-- The next actual state is obtained by the existing one-round observation construction. -/
theorem AffineIterationState.iterate_succ [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) :
    s.iterate e (i + 1) = (s.iterate e i).next e := rfl

/-- One actual transition preserves all normalized factors. -/
theorem AffineIterationState.next_probability [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e : Nat)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    IsProbabilityWeight (s.next e).weight ∧
      (∀ z, IsProbabilityWeight ((s.next e).left z)) ∧
      ∀ z, IsProbabilityWeight ((s.next e).right z) :=
  Internal.affineIterationState_next_probability s e hw hl hr

/-- Every finite actual iterate has normalized transcript and conditional kernels. -/
theorem AffineIterationState.iterate_probability [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    IsProbabilityWeight (s.iterate e i).weight ∧
      (∀ z, IsProbabilityWeight ((s.iterate e i).left z)) ∧
      ∀ z, IsProbabilityWeight ((s.iterate e i).right z) :=
  Internal.affineIterationState_iterate_probability s e i hw hl hr

/-- The left source map always reads its unchanged original coordinate. -/
theorem AffineIterationState.iterate_source [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat)
    (z : AffineIterationTranscript Z t L i) :
    (s.iterate e i).source z = s.source (AffineIterationTranscript.origin i z) :=
  Internal.affineIterationState_iterate_source s e i z

/-- The right mask always reads its unchanged original coordinate. -/
theorem AffineIterationState.iterate_mask [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat)
    (z : AffineIterationTranscript Z t L i) :
    (s.iterate e i).mask z = s.mask (AffineIterationTranscript.origin i z) :=
  Internal.affineIterationState_iterate_mask s e i z

/-- All right source words remain the original words, including tampered copies. -/
theorem AffineIterationState.iterate_rightWords [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat)
    (z : AffineIterationTranscript Z t L i) :
    (s.iterate e i).rightWords z = s.rightWords (AffineIterationTranscript.origin i z) :=
  Internal.affineIterationState_iterate_rightWords s e i z

/-- The actual accumulated transcript retains its original tag pointwise. -/
theorem AffineIterationState.transcript_origin [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (p : (Z × B) × A) :
    AffineIterationTranscript.origin i (s.transcript e i p) = p.1.1 :=
  Internal.affineIterationState_transcript_origin s e i p

/-- The whole iterated factored law is exactly the original law with its actual transcript. -/
theorem AffineIterationState.iterate_factored [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    mapWeight (s.lift e i) (factoredWeight s.weight s.left s.right) =
      factoredWeight (s.iterate e i).weight (s.iterate e i).left (s.iterate e i).right :=
  Internal.affineIterationState_iterate_factored s e i hw hl hr

/-- Every honest or tampered masked row is the actual repeated semantic output. -/
theorem AffineIterationState.iterate_rows_eq [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat)
    (p : (Z × B) × A) (j : Option (Fin t)) :
    (fun k => Bool.xor
      ((s.iterate e i).leftRows (s.transcript e i p) p.2 j k)
      ((s.iterate e i).rightRows (s.transcript e i p) p.1.2 j k)) =
      affineRoundsOutput n d h L e i
        (fun k => Bool.xor (s.source p.1.1 p.2 k) (s.mask p.1.1 p.1.2 k))
        (s.rightWords p.1.1 p.1.2 j)
        (fun k => Bool.xor (s.leftRows p.1.1 p.2 j k) (s.rightRows p.1.1 p.1.2 j k)) :=
  Internal.affineIterationState_iterate_rows_eq s e i p j

/-- The evolving left envelope bounds the unchanged original-left source masses. -/
theorem AffineIterationState.leftEnvelope_cap [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (μ : Z → ℝ)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z))
    (cap : ∀ z x₀, s.weight z * mapWeight (s.source z) (s.left z) x₀ ≤ μ z)
    (z : AffineIterationTranscript Z t L i) (x₀ : Fin n → Bool) :
    (s.iterate e i).weight z *
        mapWeight ((s.iterate e i).source z) ((s.iterate e i).left z) x₀ ≤
      s.leftEnvelope e μ i z :=
  Internal.affineIterationState_leftEnvelope_cap s e i μ hw hl hr cap z x₀

/-- The evolving right envelope bounds the original honest right-word masses. -/
theorem AffineIterationState.rightEnvelope_cap [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (ν : Z → ℝ)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z))
    (cap : ∀ z y₀, s.weight z *
      mapWeight (fun b => s.rightWords z b none) (s.right z) y₀ ≤ ν z)
    (z : AffineIterationTranscript Z t L i) (y₀ : Fin d → Bool) :
    (s.iterate e i).weight z *
        mapWeight (fun b => (s.iterate e i).rightWords z b none)
          ((s.iterate e i).right z) y₀ ≤
      s.rightEnvelope e ν i z :=
  Internal.affineIterationState_rightEnvelope_cap s e i ν hw hl hr cap z y₀

/-- Nonnegative original-left envelopes remain nonnegative at every transcript. -/
theorem AffineIterationState.leftEnvelope_nonnegative [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (μ : Z → ℝ)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (z : AffineIterationTranscript Z t L i) : 0 ≤ s.leftEnvelope e μ i z :=
  Internal.affineIterationState_leftEnvelope_nonnegative s e i μ hw hl hr nonnegative z

/-- Nonnegative original-right envelopes remain nonnegative at every transcript. -/
theorem AffineIterationState.rightEnvelope_nonnegative [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (ν : Z → ℝ)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) (nonnegative : ∀ z, 0 ≤ ν z)
    (z : AffineIterationTranscript Z t L i) : 0 ≤ s.rightEnvelope e ν i z :=
  Internal.affineIterationState_rightEnvelope_nonnegative s e i ν hw hl hr nonnegative z

/-- Each actual round multiplies the left-envelope total by the squared message alphabet. -/
theorem AffineIterationState.leftEnvelope_sum [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (μ : Z → ℝ)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    (∑ z, s.leftEnvelope e μ i z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ (2 * i) * ∑ z, μ z :=
  Internal.affineIterationState_leftEnvelope_sum s e i μ hw hl hr

/-- Each actual round multiplies the right-envelope total by the fourth-power message alphabet. -/
theorem AffineIterationState.rightEnvelope_sum [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (ν : Z → ℝ)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    (∑ z, s.rightEnvelope e ν i z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ (4 * i) * ∑ z, ν z :=
  Internal.affineIterationState_rightEnvelope_sum s e i ν hw hl hr

end Algebraic.Cutwidth.Extractor
