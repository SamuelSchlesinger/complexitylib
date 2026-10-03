/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs
import Mathlib.Data.Finset.Union

/-!
# Joint law for finite independence merging

The left variable contains a source and all its tampered copies. The right
variable contains a seed and all its tampered copies. Their conditional
laws are independent given a shared transcript. The output law retains the
entire right variable, the transcript, and every tampered extraction indexed
by the union of two supplied sets. The sets may overlap.

This is the finite law in Chattopadhyay--Liao, *Extractors for Sum of Two
Sources*, Lemma 3.26: <https://arxiv.org/pdf/2110.12652>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Extract while retaining the transcript, every seed, and the chosen tampered outputs. -/
noncomputable def independenceMergingWeight {Z X Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype X] [Fintype Seed]
    (w : Z → ℝ) (l : Z → (X × (Fin t → X)) → ℝ)
    (r : Z → (Seed × (Fin t → Seed)) → ℝ) (E : X → Seed → Out)
    (S T : Finset (Fin t)) :
    ((Z × (Seed × (Fin t → Seed))) × (↥(S ∪ T) → Out)) × Out → ℝ :=
  mapWeight (fun p : (Z × (Seed × (Fin t → Seed))) × (X × (Fin t → X)) =>
    ((p.1, fun j : ↥(S ∪ T) => E (p.2.2 j) (p.1.2.2 j)), E p.2.1 p.1.2.1))
    (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
