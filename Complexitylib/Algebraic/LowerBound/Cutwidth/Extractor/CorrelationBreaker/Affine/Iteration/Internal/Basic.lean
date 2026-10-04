/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round

/-!
# Normalized iteration states and original coordinate maps

The actual transitions preserve normalized factors, including null
transcripts. Their source maps still read the original variables, and the
computed transcript projects to the original tag pointwise.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

variable {n d h t L : Nat} {Z A B : Type*}

theorem affineIterationState_next_probability [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e : Nat)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    IsProbabilityWeight (s.next e).weight ∧
      (∀ z, IsProbabilityWeight ((s.next e).left z)) ∧
      ∀ z, IsProbabilityWeight ((s.next e).right z) :=
  affineRoundTranscript_probability d h t L e s.weight s.left s.right
    s.leftRows s.rightRows s.rightWords hw hl hr

theorem affineIterationState_iterate_probability [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    IsProbabilityWeight (s.iterate e i).weight ∧
      (∀ z, IsProbabilityWeight ((s.iterate e i).left z)) ∧
      ∀ z, IsProbabilityWeight ((s.iterate e i).right z) := by
  induction i with
  | zero => exact ⟨hw, hl, hr⟩
  | succ i ih =>
      exact affineIterationState_next_probability (s.iterate e i) e ih.1 ih.2.1 ih.2.2

theorem affineIterationState_iterate_source [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat)
    (z : AffineIterationTranscript Z t L i) :
    (s.iterate e i).source z = s.source (AffineIterationTranscript.origin i z) := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih (affineRoundOrigin z)

theorem affineIterationState_iterate_mask [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat)
    (z : AffineIterationTranscript Z t L i) :
    (s.iterate e i).mask z = s.mask (AffineIterationTranscript.origin i z) := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih (affineRoundOrigin z)

theorem affineIterationState_iterate_rightWords [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat)
    (z : AffineIterationTranscript Z t L i) :
    (s.iterate e i).rightWords z = s.rightWords (AffineIterationTranscript.origin i z) := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih (affineRoundOrigin z)

theorem affineIterationState_transcript_origin [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (p : (Z × B) × A) :
    AffineIterationTranscript.origin i (s.transcript e i p) = p.1.1 := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih

theorem affineIterationState_iterate_source_transcript [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (p : (Z × B) × A) :
    (s.iterate e i).source (s.transcript e i p) = s.source p.1.1 := by
  rw [affineIterationState_iterate_source, affineIterationState_transcript_origin]

theorem affineIterationState_iterate_mask_transcript [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (p : (Z × B) × A) :
    (s.iterate e i).mask (s.transcript e i p) = s.mask p.1.1 := by
  rw [affineIterationState_iterate_mask, affineIterationState_transcript_origin]

theorem affineIterationState_iterate_rightWords_transcript [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (p : (Z × B) × A) :
    (s.iterate e i).rightWords (s.transcript e i p) = s.rightWords p.1.1 := by
  rw [affineIterationState_iterate_rightWords, affineIterationState_transcript_origin]

end Algebraic.Cutwidth.Extractor.Internal
