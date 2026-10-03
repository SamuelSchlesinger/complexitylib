/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs
import Mathlib.Data.Finset.Union

/-!
# Actual laws for smooth independence merging

The original left state determines the honest source, every tampered
source, and the actual prefix. The original right state determines all
seeds after that prefix. The two sides are independent only conditional
on the original transcript; observing the prefix is an exact update of
that factored law. Source and seed hypotheses concern their actual joint
laws, and the output retains the original right state and prefix.

These definitions support the smooth-source independence-merging step
in Chattopadhyay--Liao, *Extractors for Sum of Two Sources* (2021),
Theorem 6.1, using Lemma 3.26: <https://arxiv.org/abs/2110.12652>.
No statistical claim is part of the definitions.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The honest original source together with the selected original tampered source copies. -/
noncomputable def smoothIndependenceSourceWeight {Z A X : Type*} {t : Nat}
    [Fintype Z] [Fintype A]
    (w : Z → ℝ) (l : Z → A → ℝ) (xs : Z → A → Option (Fin t) → X)
    (T : Finset (Fin t)) : (Z × (T → X)) × X → ℝ :=
  observedSeedWeight w l (fun z a (j : T) => xs z a (some j.1))
    (fun z a => xs z a none)

/-- Actual seed copies after the original left prefix, retaining the selected tampered seeds. -/
noncomputable def smoothIndependenceSeedWeight {Z A B Q Seed : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (q : Z → A → Q) (ys : (Z × Q) → B → Option (Fin t) → Seed)
    (S : Finset (Fin t)) : ((Z × Q) × (S → Seed)) × Seed → ℝ :=
  observedSeedWeight (observedTranscriptWeight w l q) (fun zq => r zq.1)
    (fun zq b (j : S) => ys zq b (some j.1)) (fun zq b => ys zq b none)

/-- Actual extraction retaining the original prefix, full right state, and union of tamperings. -/
noncomputable def smoothIndependenceMergingWeight {Z A B X Q Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (xs : Z → A → Option (Fin t) → X) (q : Z → A → Q)
    (ys : (Z × Q) → B → Option (Fin t) → Seed) (E : X → Seed → Out)
    (S T : Finset (Fin t)) : (((Z × Q) × B) × (↥(S ∪ T) → Out)) × Out → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let zq := (p.1.1, q p.1.1 p.2)
    (((zq, p.1.2), fun j : ↥(S ∪ T) =>
      E (xs p.1.1 p.2 (some j.1)) (ys zq p.1.2 (some j.1))),
      E (xs p.1.1 p.2 none) (ys zq p.1.2 none))) (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
