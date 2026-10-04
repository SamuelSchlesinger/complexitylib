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
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Exact execution through all accumulated affine transcripts

Deterministic pushforwards compose the one-round factorization without
resampling either original side. The two side contributions reconstruct
the actual repeated masked-row algorithm pointwise.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

variable {n d h t L : Nat} {Z A B : Type*}

theorem affineIterationState_next_factored [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e : Nat)
    (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    mapWeight (fun p : (Z × B) × A =>
      ((affineRoundTranscript d h t L e s.leftRows s.rightRows s.rightWords p, p.1.2), p.2))
      (factoredWeight s.weight s.left s.right) =
      factoredWeight (s.next e).weight (s.next e).left (s.next e).right :=
  affineRoundTranscript_factored d h t L e s.weight s.left s.right
    s.leftRows s.rightRows s.rightWords hl hr

theorem affineIterationState_iterate_factored [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    mapWeight (s.lift e i) (factoredWeight s.weight s.left s.right) =
      factoredWeight (s.iterate e i).weight (s.iterate e i).left (s.iterate e i).right := by
  induction i with
  | zero => exact mapWeight_id _
  | succ i ih =>
      let current := s.iterate e i
      let step := fun p : (AffineIterationTranscript Z t L i × B) × A =>
        ((affineRoundTranscript d h t L e current.leftRows current.rightRows
          current.rightWords p, p.1.2), p.2)
      change mapWeight (fun p => step (s.lift e i p))
        (factoredWeight s.weight s.left s.right) = _
      rw [← mapWeight_comp, ih]
      have probability := affineIterationState_iterate_probability s e i hw hl hr
      exact affineIterationState_next_factored current e probability.2.1 probability.2.2

theorem affineIterationState_next_rows_eq [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e : Nat)
    (p : (Z × B) × A) (j : Option (Fin t)) :
    (fun k => Bool.xor
      ((s.next e).leftRows
        (affineRoundTranscript d h t L e s.leftRows s.rightRows s.rightWords p) p.2 j k)
      ((s.next e).rightRows
        (affineRoundTranscript d h t L e s.leftRows s.rightRows s.rightWords p) p.1.2 j k)) =
      affineRoundOutput n d h L e
        (fun k => Bool.xor (s.source p.1.1 p.2 k) (s.mask p.1.1 p.1.2 k))
        (s.rightWords p.1.1 p.1.2 j)
        (fun k => Bool.xor (s.leftRows p.1.1 p.2 j k) (s.rightRows p.1.1 p.1.2 j k)) :=
  (affineRoundOutput_eq_xor n d h t L e s.source s.mask s.leftRows s.rightRows
    s.rightWords p j).symm

theorem affineIterationState_iterate_rows_eq [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat)
    (p : (Z × B) × A) (j : Option (Fin t)) :
    (fun k => Bool.xor
      ((s.iterate e i).leftRows (s.transcript e i p) p.2 j k)
      ((s.iterate e i).rightRows (s.transcript e i p) p.1.2 j k)) =
      affineRoundsOutput n d h L e i
        (fun k => Bool.xor (s.source p.1.1 p.2 k) (s.mask p.1.1 p.1.2 k))
        (s.rightWords p.1.1 p.1.2 j)
        (fun k => Bool.xor (s.leftRows p.1.1 p.2 j k) (s.rightRows p.1.1 p.1.2 j k)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      change (fun k => Bool.xor
        (((s.iterate e i).next e).leftRows
          (affineRoundTranscript d h t L e (s.iterate e i).leftRows (s.iterate e i).rightRows
            (s.iterate e i).rightWords ((s.transcript e i p, p.1.2), p.2)) p.2 j k)
        (((s.iterate e i).next e).rightRows
          (affineRoundTranscript d h t L e (s.iterate e i).leftRows (s.iterate e i).rightRows
            (s.iterate e i).rightWords ((s.transcript e i p, p.1.2), p.2)) p.1.2 j k)) = _
      rw [affineIterationState_next_rows_eq]
      dsimp only
      rw [affineIterationState_iterate_source_transcript,
        affineIterationState_iterate_mask_transcript,
        affineIterationState_iterate_rightWords_transcript, ih]
      rfl

end Algebraic.Cutwidth.Extractor.Internal
