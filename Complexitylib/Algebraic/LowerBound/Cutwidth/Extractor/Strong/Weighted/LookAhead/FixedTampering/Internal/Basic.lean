/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Exact fixed-tampering transcript identities

Three deterministic observations identify the actual law with normalized
left and right kernels. The statistical proof can process the left leak
before the independent right input observation and then retain the honest
first output as a deterministic function of the already retained state.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

variable {Z A B X Q Seed Mid Y Out : Type*}

theorem fixedTampering_factored_eq_map
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (R : Y → Mid → Out)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    factoredWeight (fixedTamperingTranscriptWeight w l r x q y' leak initialSeed W R)
      (fixedTamperingLeft l x leak initialSeed W) (fixedTamperingRight r q y' R) =
      mapWeight (fun p : (Z × B) × A =>
        ((fixedTamperingTranscriptValue x q y' leak initialSeed W R p.1.1 p.2 p.1.2,
          p.1.2), p.2)) (factoredWeight w l r) := by
  have h := factoredWeight_observe_left_right w l r leak
    (fixedTamperingRightMessage q y' R) (fun z => (hl z).1) (fun z => (hr z).1)
  have hp (t : (Z × Mid) × (Q × Out)) :
      IsProbabilityWeight (observedTranscriptKernel l leak t.1) :=
    observedTranscriptKernel_probability l leak hl t.1
  unfold fixedTamperingTranscriptWeight fixedTamperingLeft fixedTamperingRight
  rw [← factoredWeight_observe_left _ _ _ _ (fun t => (hp t).1), ← h, mapWeight_comp]
  rfl

theorem fixedTampering_factors_probability
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (R : Y → Mid → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (fixedTamperingTranscriptWeight w l r x q y' leak initialSeed W R) ∧
      (∀ t : FixedTamperingTranscript Z Q Mid Out,
        IsProbabilityWeight (fixedTamperingLeft l x leak initialSeed W t)) ∧
      (∀ t, IsProbabilityWeight (fixedTamperingRight r q y' R t)) := by
  have h := observedTranscript_left_right_probability w l r leak
    (fixedTamperingRightMessage q y' R) hw hl hr
  exact ⟨observedTranscriptWeight_probability _ _ _ h.1 h.2.1,
    observedTranscriptKernel_probability _ _ h.2.1, fun t => h.2.2 t.1⟩

theorem fixedTamperingRefreshWeight_probability
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (R : Y → Mid → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem fixedTamperingRefreshWeight_eq_factored
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (R : Y → Mid → Out)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R =
      mapWeight (fun p : (FixedTamperingTranscript Z Q Mid Out × B) × A =>
        ((p.1.1, p.2), R (y p.1.1.1.1.1 p.1.2) p.1.1.2))
        (factoredWeight (fixedTamperingTranscriptWeight w l r x q y' leak initialSeed W R)
          (fixedTamperingLeft l x leak initialSeed W) (fixedTamperingRight r q y' R)) := by
  rw [fixedTampering_factored_eq_map w l r x q y' leak initialSeed W R hl hr, mapWeight_comp]
  rfl

theorem fixedTampering_seed_eq_map
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (R : Y → Mid → Out)
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    alternatingSeedWeight (observedTranscriptWeight w l leak)
        (observedTranscriptKernel l leak) (fun zm => r zm.1)
        (fixedTamperingRightMessage q y' R) (fixedTamperingHonestMessage x initialSeed W) =
      mapWeight (fun p : ((Z × B) × (Unit × Mid)) × Mid =>
        (((p.1.1.1, p.1.2.2),
          fixedTamperingRightMessage q y' R (p.1.1.1, p.1.2.2) p.1.1.2), p.2))
        (twoSidedExtractionWeight w l r x (fun z b => initialSeed (q z b))
          (fun _ _ => ()) (fun _ _ => ()) (fun z _ a => leak z a) W) := by
  rw [twoSidedExtractionWeight_eq_map]
  unfold alternatingSeedWeight
  rw [← factoredWeight_observe_left w l r leak (fun z => (hl z).1),
    mapWeight_comp, mapWeight_comp]
  rfl

theorem fixedTamperingRefreshWeight_eq_alternating_map
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (R : Y → Mid → Out)
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R =
      mapWeight (fun p : (((Z × Mid) × (Q × Out)) × A) × Out =>
        (((p.1.1, fixedTamperingHonestMessage x initialSeed W p.1.1 p.1.2), p.1.2), p.2))
        (alternatingExtractionWeight (observedTranscriptWeight w l leak)
          (observedTranscriptKernel l leak) (fun zm => r zm.1)
          (fixedTamperingRightMessage q y' R) (fixedTamperingHonestMessage x initialSeed W)
          (fun zm => y zm.1) R) := by
  unfold alternatingExtractionWeight
  rw [← factoredWeight_observe_left w l r leak (fun z => (hl z).1),
    mapWeight_comp, mapWeight_comp]
  rfl

end Algebraic.Cutwidth.Extractor.Internal
