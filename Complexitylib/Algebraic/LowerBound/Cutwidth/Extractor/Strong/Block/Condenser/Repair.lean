/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Mathlib.Data.Fin.Tuple.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser.Repair.Internal

/-!
# Replacing a latent head while preserving a block-source tail

Each latent state may have a different conditional tail distribution. If
all those tails are block sources, replacing a deterministic head by any
capped probability law yields a full block source at exactly the distance
between the old and new head marginals. The construction retains the latent
state's correlation with its tail; it assumes no independence between them.

This is a finite repair step for the shared-seed block-condensation argument
of Chattopadhyay--Goodman--Liao, Lemma 5.5:
<https://eccc.weizmann.ac.il/report/2021/075/download/>.
Maximal coupling supplies the repair, and attaching the unchanged conditional
tail preserves total variation. The induction over all blocks and averaging
over the shared seed are separate from this theorem.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Replace a deterministic head by a capped target law while preserving
conditional tail caps, at exactly the distance of the head marginals. -/
theorem exists_block_tail_replacement {α Ω : Type*} [Fintype α] [Fintype Ω]
    (t K : Nat) (w : α → ℝ) (tail : α → (Fin t → Ω) → ℝ)
    (f : α → Ω) (target : Ω → ℝ) (hw : IsProbabilityWeight w)
    (htail : ∀ a, IsBlockSource (tail a) K) (htarget : IsProbabilityWeight target)
    (cap : CappedWeight target K) :
    ∃ r : (Fin (t + 1) → Ω) → ℝ,
      IsBlockSource r K ∧ mapWeight (fun z => z 0) r = target ∧
        weightDist
          (mapWeight (fun az : α × (Fin t → Ω) => Fin.cons (f az.1) az.2)
            (fun az => w az.1 * tail az.1 az.2)) r =
          weightDist (mapWeight f w) target :=
  Internal.exists_block_tail_replacement t K w tail f target hw htail htarget cap

end Algebraic.Cutwidth.Extractor
