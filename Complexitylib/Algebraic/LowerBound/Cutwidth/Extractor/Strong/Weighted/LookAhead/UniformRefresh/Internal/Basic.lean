/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Actual selected-refresh identities

The second-output law is the existing tampered-refresh law with its extra
right output discarded. Both choices have the same exact common transcript
factorization and refresh the original right source with a fixed seed.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem lookAheadSelectedRefreshWeight_false {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out) :
    lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R false =
      lookAheadFirstRefreshWeight w l r x x' q q' initialSeed W QExt y R := rfl

theorem lookAheadSelectedRefreshWeight_true_eq_map {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out) :
    lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R true =
      mapWeight (fun p : ((LookAheadBaseTranscript Z Q Mid × Out) × A) × Out =>
        ((p.1.1.1, p.1.2), p.2))
        (lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y R) := by
  rw [lookAheadTamperedRefreshWeight, mapWeight_comp]
  rfl

theorem lookAheadSelectedRefreshWeight_probability {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out) (second : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R second) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem lookAheadSelectedRefreshWeight_eq_factored {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out) (second : Bool)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b) :
    lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R second =
      mapWeight (fun p : (LookAheadBaseTranscript Z Q Mid × B) × A =>
        ((p.1.1, p.2), R (y p.1.1.1.1 p.1.2)
          (if second then p.1.1.2.1.2 else p.1.1.2.1.1)))
        (factoredWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
          (lookAheadBaseLeft l x x' initialSeed W QExt) (lookAheadBaseRight r q q')) := by
  rw [← lookAheadBase_factored w l r x x' q q' initialSeed W QExt hl hr, mapWeight_comp]
  rfl

theorem lookAheadSelectedRefreshWeight_retainedSeed {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out) (second : Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (LookAheadBaseTranscript Z Q Mid × A) × Out => (p.1.1, p.2))
        (lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R second) =
      retainedSeedWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
        (lookAheadBaseRight r q q')
        (fun t b => R (y t.1.1 b) (if second then t.2.1.2 else t.2.1.1)) := by
  rw [lookAheadSelectedRefreshWeight_eq_factored w l r x x' q q' initialSeed W QExt y R
    second (fun z => (hl z).1) hr, mapWeight_comp]
  exact (retainedSeedWeight_eq_factored
    (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
    (lookAheadBaseLeft l x x' initialSeed W QExt) (lookAheadBaseRight r q q')
    (fun t b => R (y t.1.1 b) (if second then t.2.1.2 else t.2.1.1))
    (observedTranscriptKernel_probability (fun zq : Z × (Q × Q) => l zq.1)
      (lookAheadBaseMessage x x' initialSeed W QExt) (fun zq => hl zq.1))).symm

end Algebraic.Cutwidth.Extractor.Internal
