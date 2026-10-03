/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Mathlib.Data.Fin.Tuple.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Conditioning
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser.Repair.Internal.Replacement

/-!
# Block-source caps after exact head repair

The repaired tuple is a nonnegative mixture of the original conditional
tail laws at each head. Its head marginal has the requested cap, so the
prepend criterion supplies every block-source inequality.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

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
          weightDist (mapWeight f w) target := by
  obtain ⟨c, r, hc, _, rows, head, factor, distance⟩ := exists_prepend_replacement
    t w tail f target hw (fun a => (htail a).1) htarget
  refine ⟨r, ?_, head, distance⟩
  exact isBlockSource_of_prepend_mixture r target tail (fun h a => c (h, a))
    htarget cap htail (fun h a => hc.1 (h, a)) rows factor

end Algebraic.Cutwidth.Extractor.Internal
