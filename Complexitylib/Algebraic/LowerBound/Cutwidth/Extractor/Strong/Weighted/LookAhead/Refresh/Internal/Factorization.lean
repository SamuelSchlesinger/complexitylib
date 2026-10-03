/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Factored forms of the actual refresh distributions

The common transcript fixes every refresh seed. These identities retain
both latent states during observation, then form the actual refresh by a
deterministic map. They make the refreshed source right-only without an
independence assumption about the refreshed source and retained right state.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem lookAheadFirstRefreshWeight_eq_factored {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b) :
    lookAheadFirstRefreshWeight w l r x x' q q' initialSeed W QExt y R =
      mapWeight (fun p : (LookAheadBaseTranscript Z Q Mid × B) × A =>
        ((p.1.1, p.2), R (y p.1.1.1.1 p.1.2) p.1.1.2.1.1))
        (factoredWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
          (lookAheadBaseLeft l x x' initialSeed W QExt) (lookAheadBaseRight r q q')) := by
  rw [← lookAheadBase_factored w l r x x' q q' initialSeed W QExt hl hr, mapWeight_comp]
  rfl

theorem lookAheadFirstRefreshWeight_retainedSeed {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (LookAheadBaseTranscript Z Q Mid × A) × Out => (p.1.1, p.2))
        (lookAheadFirstRefreshWeight w l r x x' q q' initialSeed W QExt y R) =
      retainedSeedWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
        (lookAheadBaseRight r q q') (fun t b => R (y t.1.1 b) t.2.1.1) := by
  rw [lookAheadFirstRefreshWeight_eq_factored w l r x x' q q' initialSeed W QExt y R
    (fun z => (hl z).1) hr, mapWeight_comp]
  exact (retainedSeedWeight_eq_factored
    (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
    (lookAheadBaseLeft l x x' initialSeed W QExt) (lookAheadBaseRight r q q')
    (fun t b => R (y t.1.1 b) t.2.1.1)
    (observedTranscriptKernel_probability (fun zq : Z × (Q × Q) => l zq.1)
      (lookAheadBaseMessage x x' initialSeed W QExt) (fun zq => hl zq.1))).symm

theorem lookAheadTamperedRefresh_factored {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y' : Z → B → Y) (R : Y → Mid → Out)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (Z × B) × A =>
      let zq := (p.1.1, (q p.1.1 p.1.2, q' p.1.1 p.1.2))
      let messages := lookAheadBaseMessage x x' initialSeed W QExt zq p.2
      ((((zq, messages), R (y' p.1.1 p.1.2) messages.2.1), p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight
        (observedTranscriptWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
          (lookAheadBaseRight r q q') (fun t b => R (y' t.1.1 b) t.2.2.1))
        (fun tu => lookAheadBaseLeft l x x' initialSeed W QExt tu.1)
        (observedTranscriptKernel (lookAheadBaseRight r q q')
          (fun t b => R (y' t.1.1 b) t.2.2.1)) := by
  have result := factoredWeight_observe_right
    (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
    (lookAheadBaseLeft l x x' initialSeed W QExt) (lookAheadBaseRight r q q')
    (fun t b => R (y' t.1.1 b) t.2.2.1)
    (fun t => (observedTranscriptKernel_probability r _ hr t.1).1)
  rw [← lookAheadBase_factored w l r x x' q q' initialSeed W QExt hl
    (fun z => (hr z).1), mapWeight_comp] at result
  exact result

theorem lookAheadTamperedRefreshWeight_eq_factored {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y y' : Z → B → Y) (R : Y → Mid → Out)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z, IsProbabilityWeight (r z)) :
    lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y' R =
      mapWeight (fun p : ((LookAheadBaseTranscript Z Q Mid × Out) × B) × A =>
        ((p.1.1, p.2), R (y p.1.1.1.1.1 p.1.2) p.1.1.1.2.1.2))
        (factoredWeight
          (observedTranscriptWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
            (lookAheadBaseRight r q q') (fun t b => R (y' t.1.1 b) t.2.2.1))
          (fun tu => lookAheadBaseLeft l x x' initialSeed W QExt tu.1)
          (observedTranscriptKernel (lookAheadBaseRight r q q')
            (fun t b => R (y' t.1.1 b) t.2.2.1))) := by
  rw [← lookAheadTamperedRefresh_factored w l r x x' q q' initialSeed W QExt y' R hl hr,
    mapWeight_comp]
  rfl

end Algebraic.Cutwidth.Extractor.Internal
