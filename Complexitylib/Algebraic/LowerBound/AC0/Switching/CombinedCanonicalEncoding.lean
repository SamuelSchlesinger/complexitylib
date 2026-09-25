/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedAdvice
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.CanonicalEncoding
public import Mathlib.Data.Finset.Sort

/-!
# Decoder-facing combined switching advice

This module gives the counted block advice a canonical sequential
interpretation. Each stored position subset is replayed in increasing source
order. A continuing block closes after its last query, while the last block
never needs a closing marker because replay ends with the advice list.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace Switching

/-- Expand one block into the elementary query format used by the canonical
replay decoder. -/
def BlockAdvice.toQueryList
    (block : BlockAdvice width length)
    (closesBlock : Bool) : List (QueryAdvice width) :=
  List.ofFn fun index : Fin length =>
    { position := block.positions.val.orderEmbOfFin block.positions.property index
      closesBlock := closesBlock && decide (index.val + 1 = length)
      difference := block.differences index }

/-- Expanding a block preserves its indexed length. -/
@[simp] theorem BlockAdvice.length_toQueryList
    (block : BlockAdvice width length)
    (closesBlock : Bool) :
    (block.toQueryList closesBlock).length = length := by
  simp [BlockAdvice.toQueryList]

/-- Combined advice for a nonempty path, split into its first block and, if that
block does not end the path, the advice for the rest. -/
def CombinedAdvice.SuccView (width pathLength : Nat) :=
  (blockLengthMinusOne : Fin (Nat.min width (pathLength + 1))) ×
    if blockLengthMinusOne.val = pathLength then
      BlockAdvice width (blockLengthMinusOne.val + 1)
    else
      ContinuingBlockAdvice width (blockLengthMinusOne.val + 1) ×
        CombinedAdvice width
          (pathLength - blockLengthMinusOne.val)

/-- Combined advice for a path of length `pathLength + 1` is its first-block view. -/
def CombinedAdvice.succEquiv (width pathLength : Nat) :
    CombinedAdvice width (Nat.succ pathLength) ≃
      CombinedAdvice.SuccView width pathLength := by
  simp only [CombinedAdvice, CombinedAdvice.SuccView]
  exact Equiv.refl _

/-- Flatten combined advice into sequential query advice. Source positions are
sorted within each block; exactly the nonfinal block boundaries are marked. -/
def CombinedAdvice.toQueryList :
    (pathLength : Nat) → CombinedAdvice width pathLength →
      List (QueryAdvice width)
  | 0, _ => []
  | Nat.succ pathLength, advice => by
      let unpacked := CombinedAdvice.succEquiv width pathLength advice
      rcases unpacked with ⟨index, payload⟩
      by_cases final : index.val = pathLength
      · have block : BlockAdvice width (index.val + 1) := by
          simpa [final] using payload
        exact block.toQueryList false
      · have payload : ContinuingBlockAdvice width (index.val + 1) ×
            CombinedAdvice width (pathLength - index.val) := by
          simpa [final] using payload
        exact payload.1.val.toQueryList true ++
          CombinedAdvice.toQueryList (pathLength - index.val) payload.2

/-- Flattening combined advice produces exactly the indexed number of query
symbols. -/
@[simp] theorem CombinedAdvice.length_toQueryList
    (advice : CombinedAdvice width pathLength) :
    advice.toQueryList.length = pathLength := by
  induction pathLength using Nat.strong_induction_on with
  | h pathLength inductionHypothesis =>
      cases pathLength with
      | zero => simp [CombinedAdvice.toQueryList]
      | succ remaining =>
          rw [CombinedAdvice.toQueryList]
          generalize unpackedEq :
            CombinedAdvice.succEquiv width remaining advice = unpacked
          rcases unpacked with ⟨index, payload⟩
          by_cases final : index.val = remaining
          · simp only [final, ↓reduceDIte, BlockAdvice.length_toQueryList]
          · simp only [final, ↓reduceDIte, List.length_append,
              BlockAdvice.length_toQueryList]
            have indexLe : index.val ≤ remaining := by
              have belowTotal : index.val < remaining + 1 :=
                index.isLt.trans_le
                  (Nat.min_le_right width (remaining + 1))
              omega
            rw [inductionHypothesis]
            · omega
            · omega

/-- The first-block view of advice consisting of one final block. -/
def CombinedAdvice.finalView
    (block : BlockAdvice width (remaining + 1))
    (lengthLeWidth : remaining + 1 ≤ width) :
    CombinedAdvice.SuccView width remaining :=
  ⟨⟨remaining, lt_min (by omega) (by omega)⟩, by
    simp
    exact block⟩

/-- Package one positive-length block as final combined advice. -/
def CombinedAdvice.ofFinalBlock
    (block : BlockAdvice width (remaining + 1))
    (lengthLeWidth : remaining + 1 ≤ width) :
    CombinedAdvice width (remaining + 1) :=
  (CombinedAdvice.succEquiv width remaining).symm
    (CombinedAdvice.finalView block lengthLeWidth)

/-- Flattening a packaged final block returns precisely that block, with no
operationally unnecessary closing marker. -/
@[simp] theorem CombinedAdvice.toQueryList_ofFinalBlock
    (block : BlockAdvice width (remaining + 1))
    (lengthLeWidth : remaining + 1 ≤ width) :
    (CombinedAdvice.ofFinalBlock block lengthLeWidth).toQueryList =
      block.toQueryList false := by
  change CombinedAdvice.toQueryList (remaining + 1)
      ((CombinedAdvice.succEquiv width remaining).symm
        (CombinedAdvice.finalView block lengthLeWidth)) = _
  rw [CombinedAdvice.toQueryList]
  rw [Equiv.apply_symm_apply]
  simp [CombinedAdvice.finalView]

private theorem CombinedAdvice.toQueryList_cast
    {left right : Nat}
    (equal : left = right)
    (advice : CombinedAdvice width left) :
    CombinedAdvice.toQueryList right (equal ▸ advice) =
      advice.toQueryList := by
  subst right
  rfl

private theorem cast_symm_cast
    {left right : Nat}
    (equal : left = right)
    (advice : CombinedAdvice width right) :
    equal ▸ (equal.symm ▸ advice) = advice := by
  subst right
  rfl

/-- The first-block view of advice obtained by prepending a continuing block to the
advice for a nonempty remainder. -/
def CombinedAdvice.prependView
    (block : ContinuingBlockAdvice width (blockRemaining + 1))
    (tail : CombinedAdvice width tailLength)
    (blockLeWidth : blockRemaining + 1 ≤ width)
    (tailPositive : 0 < tailLength) :
    CombinedAdvice.SuccView width (blockRemaining + tailLength) := by
  let index : Fin (Nat.min width (Nat.succ (blockRemaining + tailLength))) :=
    ⟨blockRemaining, lt_min (by omega) (by omega)⟩
  exact ⟨index, by
    have notFinal : blockRemaining ≠ blockRemaining + tailLength := by omega
    simp only [index, notFinal, ↓reduceIte]
    exact ⟨block, (Nat.add_sub_cancel_left blockRemaining tailLength).symm ▸
      tail⟩⟩

/-- Prepend a positive continuing block to nonempty combined advice. -/
def CombinedAdvice.prependBlock
    (block : ContinuingBlockAdvice width (blockRemaining + 1))
    (tail : CombinedAdvice width tailLength)
    (blockLeWidth : blockRemaining + 1 ≤ width)
    (tailPositive : 0 < tailLength) :
    CombinedAdvice width (Nat.succ (blockRemaining + tailLength)) :=
  (CombinedAdvice.succEquiv width
    (blockRemaining + tailLength)).symm
      (CombinedAdvice.prependView block tail blockLeWidth tailPositive)

/-- Flattening prepended advice concatenates the continuing block and the
nonempty tail. -/
@[simp] theorem CombinedAdvice.toQueryList_prependBlock
    (block : ContinuingBlockAdvice width (blockRemaining + 1))
    (tail : CombinedAdvice width tailLength)
    (blockLeWidth : blockRemaining + 1 ≤ width)
    (tailPositive : 0 < tailLength) :
    (CombinedAdvice.prependBlock block tail blockLeWidth
      tailPositive).toQueryList =
      block.val.toQueryList true ++ tail.toQueryList := by
  change CombinedAdvice.toQueryList _
      ((CombinedAdvice.succEquiv width
        (blockRemaining + tailLength)).symm
          (CombinedAdvice.prependView block tail blockLeWidth
            tailPositive)) = _
  rw [CombinedAdvice.toQueryList, Equiv.apply_symm_apply]
  simp [CombinedAdvice.prependView, ne_of_gt tailPositive]
  have remainderEq : blockRemaining + tailLength - blockRemaining =
      tailLength := Nat.add_sub_cancel_left blockRemaining tailLength
  have transported := (CombinedAdvice.toQueryList_cast remainderEq
    (remainderEq.symm ▸ tail)).symm
  rw [cast_symm_cast remainderEq tail] at transported
  convert transported using 1

/-- The same query advice with its block-closing marker cleared. -/
def QueryAdvice.withoutClose
    (advice : QueryAdvice width) : QueryAdvice width :=
  { advice with closesBlock := false }

/-- Erase the final query's block-closing marker. It is operationally
irrelevant because no advice remains after that query. -/
def clearLastClose : List (QueryAdvice width) → List (QueryAdvice width)
  | [] => []
  | [advice] => [advice.withoutClose]
  | advice :: next :: rest => advice :: clearLastClose (next :: rest)

/-- Erasing the last closing marker preserves list length. -/
@[simp] theorem length_clearLastClose
    (advice : List (QueryAdvice width)) :
    (clearLastClose advice).length = advice.length := by
  induction advice with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          simp only [clearLastClose, List.length_cons]
          simp only [List.length_cons] at inductionHypothesis
          omega

/-- Canonical replay is insensitive to the final query's closing marker. -/
theorem replayIndices_clearLastClose
    (formula : DNF n)
    (state : PartialAssignment n)
    (currentTerm : Option (Term n))
    (advice : List (QueryAdvice width)) :
    replayIndices formula state currentTerm (clearLastClose advice) =
      replayIndices formula state currentTerm advice := by
  induction advice generalizing state currentTerm with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil =>
          simp [clearLastClose, replayIndices, QueryAdvice.withoutClose]
      | cons next rest =>
          simp only [clearLastClose, replayIndices]
          split <;> rename_i selected
          · rfl
          · split <;> rename_i decoded
            · rfl
            · change _ :: replayIndices formula _ _
                  (clearLastClose (next :: rest)) =
                _ :: replayIndices formula _ _ (next :: rest)
              exact congrArg (List.cons _) (inductionHypothesis _ _)

/-- Decode a refined restriction carrying combined block advice. -/
def decodeCombined
    (formula : DNF n)
    (encoded : PartialAssignment n × CombinedAdvice width pathLength) :
    PartialAssignment n :=
  encoded.1.clear
    (replayIndices formula encoded.1 none encoded.2.toQueryList).toFinset

end Switching
end AC0
end Algebraic
