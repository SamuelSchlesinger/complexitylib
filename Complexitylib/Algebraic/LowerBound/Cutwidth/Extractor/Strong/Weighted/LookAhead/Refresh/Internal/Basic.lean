/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Exact transcript identities for look-ahead refreshes

Right observations and subsequent left observations preserve the complete
latent joint law. The refresh output laws only project these deterministic
transcripts; no independent resampling is used in their identities.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem factoredWeight_observe_right_left {Z A B U V : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (g : Z → B → U) (f : Z × U → A → V)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (Z × B) × A =>
      ((((p.1.1, g p.1.1 p.1.2), f (p.1.1, g p.1.1 p.1.2) p.2), p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight
        (observedTranscriptWeight (observedTranscriptWeight w r g) (fun zu => l zu.1) f)
        (observedTranscriptKernel (fun zu => l zu.1) f)
        (fun zuv => observedTranscriptKernel r g zuv.1) := by
  have first := factoredWeight_observe_right w l r g hr
  have second := factoredWeight_observe_left (observedTranscriptWeight w r g)
    (fun zu => l zu.1) (observedTranscriptKernel r g) f (fun zu => hl zu.1)
  rw [← first, mapWeight_comp] at second
  exact second

theorem lookAheadBase_factored {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (Z × B) × A =>
      let zq := (p.1.1, (q p.1.1 p.1.2, q' p.1.1 p.1.2))
      (((zq, lookAheadBaseMessage x x' initialSeed W QExt zq p.2), p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
        (lookAheadBaseLeft l x x' initialSeed W QExt) (lookAheadBaseRight r q q') :=
  factoredWeight_observe_right_left w l r (fun z b => (q z b, q' z b))
    (lookAheadBaseMessage x x' initialSeed W QExt) hl hr

theorem lookAheadBase_probability {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt) ∧
      (∀ t, IsProbabilityWeight (lookAheadBaseLeft l x x' initialSeed W QExt t)) ∧
      (∀ t, IsProbabilityWeight (lookAheadBaseRight (Mid := Mid) r q q' t)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact observedTranscriptWeight_probability _ _ _
      (observedTranscriptWeight_probability w r _ hw hr) (fun zq => hl zq.1)
  · exact observedTranscriptKernel_probability _ _ (fun zq => hl zq.1)
  · exact fun t => observedTranscriptKernel_probability r _ hr t.1

theorem lookAheadFirstRefreshWeight_probability {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (lookAheadFirstRefreshWeight w l r x x' q q' initialSeed W QExt y R) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem lookAheadTamperedRefreshWeight_probability {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y y' : Z → B → Y) (R : Y → Mid → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y' R) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem firstRefresh_seed_eq_map {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) :
    alternatingSeedWeight w l r (fun z b => (q z b, q' z b))
        (fun zq a => W (x zq.1 a) (initialSeed zq.2.1)) =
      mapWeight (fun p : (Z × B) × Mid =>
        ((p.1.1, (q p.1.1 p.1.2, q' p.1.1 p.1.2)), p.2))
        (retainedExtractionWeight w l r x (fun z b => initialSeed (q z b)) W) := by
  unfold alternatingSeedWeight retainedExtractionWeight
  rw [mapWeight_comp]

theorem firstRefresh_output_eq_map {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out) :
    lookAheadFirstRefreshWeight w l r x x' q q' initialSeed W QExt y R =
      mapWeight (fun p : ((Z × (Q × Q)) × A) × Out =>
        (((p.1.1, lookAheadBaseMessage x x' initialSeed W QExt p.1.1 p.1.2), p.1.2), p.2))
        (alternatingExtractionWeight w l r (fun z b => (q z b, q' z b))
          (fun zq a => W (x zq.1 a) (initialSeed zq.2.1)) y R) := by
  unfold lookAheadFirstRefreshWeight alternatingExtractionWeight
  rw [mapWeight_comp]
  rfl

end Algebraic.Cutwidth.Extractor.Internal
