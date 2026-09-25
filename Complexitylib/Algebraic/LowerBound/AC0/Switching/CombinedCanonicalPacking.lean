/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedCanonicalTrace

/-!
# Packing canonical blocks into combined switching advice

This module turns the ordered raw blocks extracted from a canonical DNF trace
into the finite `CombinedAdvice` type used by the sharp counting argument. It
proves exact correspondence with the elementary replay transcript, including
synthesized block boundaries, and obtains a replay-and-clear left inverse for
every bounded canonical path.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace Switching

/-- Convert one ordered raw block into indexed counted advice. -/
def BlockAdvice.ofRelativeBlock
    (block : List (RelativeQuery width))
    (positionsSorted : (block.map Prod.fst).Pairwise (· < ·)) :
    BlockAdvice width block.length :=
  { positions := ⟨(block.map Prod.fst).toFinset, by
      rw [List.toFinset_card_of_nodup positionsSorted.nodup,
        List.length_map]⟩
    differences := fun index => (block.get index).2 }

/-- Restore an elementary query symbol from its relative position and bit. -/
def RelativeQuery.toQueryAdvice
    (query : RelativeQuery width)
    (closesBlock : Bool) : QueryAdvice width :=
  { position := query.1
    closesBlock := closesBlock
    difference := query.2 }

/-- Add the boundary convention expected by the elementary replay decoder to
one raw block. -/
def relativeBlockToQueryList
    (block : List (RelativeQuery width))
    (closesBlock : Bool) : List (QueryAdvice width) :=
  List.ofFn fun index : Fin block.length =>
    (block.get index).toQueryAdvice
      (closesBlock && decide (index.val + 1 = block.length))

private theorem relativeBlockToQueryList_cons_of_nonempty
    (query : RelativeQuery width)
    (block : List (RelativeQuery width))
    (blockNonempty : block ≠ [])
    (closesBlock : Bool) :
    relativeBlockToQueryList (query :: block) closesBlock =
      query.toQueryAdvice false ::
        relativeBlockToQueryList block closesBlock := by
  unfold relativeBlockToQueryList
  rw [List.ofFn_succ]
  congr 1
  cases closesBlock <;> simp [blockNonempty]

/-- A singleton raw block receives precisely the requested boundary bit. -/
@[simp] theorem relativeBlockToQueryList_singleton
    (query : RelativeQuery width)
    (closesBlock : Bool) :
    relativeBlockToQueryList [query] closesBlock =
      [query.toQueryAdvice closesBlock] := by
  simp [relativeBlockToQueryList, RelativeQuery.toQueryAdvice]

private theorem orderEmbOfFin_ofRelativeBlock
    (block : List (RelativeQuery width))
    (positionsSorted : (block.map Prod.fst).Pairwise (· < ·))
    (index : Fin block.length) :
    ((BlockAdvice.ofRelativeBlock block
          positionsSorted).positions.val.orderEmbOfFin
        (BlockAdvice.ofRelativeBlock block
          positionsSorted).positions.property) index =
      (block.get index).1 := by
  have parametrization :
      (fun index : Fin block.length => (block.get index).1) =
        fun index =>
          ((BlockAdvice.ofRelativeBlock block
              positionsSorted).positions.val.orderEmbOfFin
            (BlockAdvice.ofRelativeBlock block
              positionsSorted).positions.property) index := by
    apply Finset.orderEmbOfFin_unique
    · intro current
      change (block.get current).1 ∈ (block.map Prod.fst).toFinset
      exact List.mem_toFinset.mpr
        (List.mem_map_of_mem (block.get_mem current))
    · have strict :=
        (List.sortedLT_iff_strictMono_get).mp positionsSorted.sortedLT
      intro left right less
      let left' : Fin (block.map Prod.fst).length :=
        ⟨left.val, by simp only [List.length_map]; exact left.isLt⟩
      let right' : Fin (block.map Prod.fst).length :=
        ⟨right.val, by simp only [List.length_map]; exact right.isLt⟩
      simpa only [List.get_eq_getElem, List.getElem_map] using
        strict (by simpa [left', right'] using less : left' < right')
  exact (congrFun parametrization index).symm

/-- Expanding a counted block constructed from raw data recovers the exact
elementary query list, including the chosen final boundary marker. -/
theorem BlockAdvice.toQueryList_ofRelativeBlock
    (block : List (RelativeQuery width))
    (positionsSorted : (block.map Prod.fst).Pairwise (· < ·))
    (closesBlock : Bool) :
    (BlockAdvice.ofRelativeBlock block positionsSorted).toQueryList
        closesBlock =
      relativeBlockToQueryList block closesBlock := by
  unfold BlockAdvice.toQueryList relativeBlockToQueryList
  congr 1
  funext index
  congr 1
  exact orderEmbOfFin_ofRelativeBlock block positionsSorted index

/-- Re-expanding a raw block recovers its positions and differences; the
chosen closing bit is deliberately forgotten. -/
theorem BlockAdvice.map_toRelativeQuery_toQueryList_ofRelativeBlock
    (block : List (RelativeQuery width))
    (positionsSorted : (block.map Prod.fst).Pairwise (· < ·))
    (closesBlock : Bool) :
    ((BlockAdvice.ofRelativeBlock block positionsSorted).toQueryList
      closesBlock).map QueryAdvice.toRelativeQuery = block := by
  rw [BlockAdvice.toQueryList_ofRelativeBlock]
  rw [relativeBlockToQueryList, List.map_ofFn]
  simp only [Function.comp_def]
  rw [show (fun index : Fin block.length =>
      QueryAdvice.toRelativeQuery
        ((block.get index).toQueryAdvice
          (closesBlock && decide (index.val + 1 = block.length)))) =
        block.get by
    funext index
    rfl]
  exact List.ofFn_get block

/-- A raw mismatch becomes exactly the nonzero-difference condition required
by a continuing counted block. -/
theorem BlockAdvice.hasMismatch_ofRelativeBlock
    (block : List (RelativeQuery width))
    (positionsSorted : (block.map Prod.fst).Pairwise (· < ·))
    (mismatch : RelativeBlockHasMismatch block) :
    (BlockAdvice.ofRelativeBlock block positionsSorted).HasMismatch := by
  intro allZero
  obtain ⟨query, queryPresent, queryDiffers⟩ := mismatch
  obtain ⟨index, getEq⟩ := List.get_of_mem queryPresent
  have zeroAt := congrFun allZero index
  change (block.get index).2 = false at zeroAt
  rw [getEq, queryDiffers] at zeroAt
  contradiction

/-- Sequential elementary advice represented by a list of relative blocks.
Every nonfinal block receives a closing marker; the final block does not. -/
def relativeBlocksToQueryList :
    List (List (RelativeQuery width)) → List (QueryAdvice width)
  | [] => []
  | [block] => relativeBlockToQueryList block false
  | block :: next :: rest =>
      relativeBlockToQueryList block true ++
        relativeBlocksToQueryList (next :: rest)

private theorem relativeBlocksToQueryList_prependToFirstBlock
    (query : RelativeQuery width)
    (blocks : List (List (RelativeQuery width)))
    (nonempty : ∀ block ∈ blocks, block ≠ []) :
    relativeBlocksToQueryList
        (Switching.prependToFirstBlock query blocks) =
      query.toQueryAdvice false :: relativeBlocksToQueryList blocks := by
  cases blocks with
  | nil =>
      simp [Switching.prependToFirstBlock, relativeBlocksToQueryList]
  | cons block tail =>
      have blockNonempty : block ≠ [] := nonempty block (by simp)
      cases tail with
      | nil =>
          simp only [Switching.prependToFirstBlock,
            relativeBlocksToQueryList]
          exact relativeBlockToQueryList_cons_of_nonempty query block
            blockNonempty false
      | cons next remaining =>
          simp only [Switching.prependToFirstBlock,
            relativeBlocksToQueryList]
          rw [relativeBlockToQueryList_cons_of_nonempty query block
            blockNonempty true]
          rfl

/-- Counted combined advice together with its exact elementary replay list. -/
structure RelativeBlockPacking
    (width : Nat) (blocks : List (List (RelativeQuery width))) where
  /-- Counted advice occupying the sum of the raw block lengths. -/
  advice : CombinedAdvice width ((blocks.map List.length).sum)
  /-- Re-expansion produces exactly the boundary-annotated raw blocks. -/
  toQueryList : advice.toQueryList = relativeBlocksToQueryList blocks

private theorem CombinedAdvice.toQueryList_transport
    {left right : Nat}
    (equal : left = right)
    (advice : CombinedAdvice width left) :
    (equal ▸ advice).toQueryList = advice.toQueryList := by
  subst right
  rfl

/-- Recursively package structurally valid raw blocks, retaining the exact
replay-list equation as part of the construction. -/
def packRelativeBlocks
    (blocks : List (List (RelativeQuery width)))
    (nonempty : ∀ block ∈ blocks, block ≠ [])
    (positionsSorted : ∀ block ∈ blocks,
      (block.map Prod.fst).Pairwise (· < ·))
    (lengthLeWidth : ∀ block ∈ blocks, block.length ≤ width)
    (continuingMismatch :
      RelativeBlocksHaveContinuingMismatch blocks) :
    RelativeBlockPacking width blocks := by
  induction blocks with
  | nil =>
      let unitAdvice : CombinedAdvice width 0 := by
        simp only [CombinedAdvice]
        exact PUnit.unit
      exact ⟨unitAdvice, by
        change CombinedAdvice.toQueryList 0 unitAdvice = []
        simp [CombinedAdvice.toQueryList]⟩
  | cons block tail inductionHypothesis =>
      cases tail with
      | nil =>
          have blockNonempty : block ≠ [] := nonempty block (by simp)
          cases block with
          | nil => exact False.elim (blockNonempty rfl)
          | cons query rest =>
              have sorted := positionsSorted (query :: rest) (by simp)
              have bounded := lengthLeWidth (query :: rest) (by simp)
              let advice := CombinedAdvice.ofFinalBlock
                (BlockAdvice.ofRelativeBlock (query :: rest) sorted) bounded
              refine ⟨advice, ?_⟩
              change CombinedAdvice.toQueryList (rest.length + 1) advice =
                relativeBlockToQueryList (query :: rest) false
              rw [show advice.toQueryList =
                  (BlockAdvice.ofRelativeBlock
                    (query :: rest) sorted).toQueryList false by
                exact CombinedAdvice.toQueryList_ofFinalBlock _ _]
              exact BlockAdvice.toQueryList_ofRelativeBlock _ _ _
      | cons next remaining =>
          have blockNonempty : block ≠ [] := nonempty block (by simp)
          cases block with
          | nil => exact False.elim (blockNonempty rfl)
          | cons query rest =>
              have blockPresent : query :: rest ∈
                  (query :: rest) :: next :: remaining := by simp
              have sorted := positionsSorted (query :: rest) blockPresent
              have bounded := lengthLeWidth (query :: rest) blockPresent
              have tailNonempty : ∀ selected ∈ next :: remaining,
                  selected ≠ [] := by
                intro selected present
                exact nonempty selected (by simp [present])
              have tailSorted : ∀ selected ∈ next :: remaining,
                  (selected.map Prod.fst).Pairwise (· < ·) := by
                intro selected present
                exact positionsSorted selected (by simp [present])
              have tailBounded : ∀ selected ∈ next :: remaining,
                  selected.length ≤ width := by
                intro selected present
                exact lengthLeWidth selected (by simp [present])
              have headMismatch : RelativeBlockHasMismatch (query :: rest) :=
                continuingMismatch.1
              have tailMismatch :
                  RelativeBlocksHaveContinuingMismatch (next :: remaining) :=
                continuingMismatch.2
              let tailPacking := inductionHypothesis tailNonempty tailSorted
                tailBounded tailMismatch
              let blockAdvice :=
                BlockAdvice.ofRelativeBlock (query :: rest) sorted
              let continuing :
                  ContinuingBlockAdvice width (rest.length + 1) :=
                ⟨blockAdvice,
                  BlockAdvice.hasMismatch_ofRelativeBlock
                    (query :: rest) sorted headMismatch⟩
              have tailPositive :
                  0 < (((next :: remaining).map List.length).sum) := by
                have nextNonempty := tailNonempty next (by simp)
                have nextPositive := List.length_pos_iff.mpr nextNonempty
                simp only [List.map_cons, List.sum_cons]
                omega
              let rawAdvice := CombinedAdvice.prependBlock continuing
                tailPacking.advice bounded tailPositive
              have totalEq :
                  Nat.succ (rest.length +
                    (((next :: remaining).map List.length).sum)) =
                    ((((query :: rest) :: next :: remaining).map
                      List.length).sum) := by
                simp only [List.map_cons, List.sum_cons, List.length_cons]
                omega
              let advice := totalEq ▸ rawAdvice
              exact ⟨advice, by
                rw [show advice.toQueryList = rawAdvice.toQueryList by
                  exact CombinedAdvice.toQueryList_transport totalEq rawAdvice]
                rw [show rawAdvice.toQueryList =
                    continuing.val.toQueryList true ++
                      tailPacking.advice.toQueryList by
                  exact CombinedAdvice.toQueryList_prependBlock _ _ _ _]
                rw [show continuing.val.toQueryList true =
                    relativeBlockToQueryList (query :: rest) true by
                  simpa [continuing, blockAdvice] using
                    BlockAdvice.toQueryList_ofRelativeBlock
                      (query :: rest) sorted true]
                rw [tailPacking.toQueryList]
                rfl⟩

/-- Package a structurally valid list of raw blocks as counted combined
advice. -/
def CombinedAdvice.ofRelativeBlocks
    (blocks : List (List (RelativeQuery width)))
    (nonempty : ∀ block ∈ blocks, block ≠ [])
    (positionsSorted : ∀ block ∈ blocks,
      (block.map Prod.fst).Pairwise (· < ·))
    (lengthLeWidth : ∀ block ∈ blocks, block.length ≤ width)
    (continuingMismatch :
      RelativeBlocksHaveContinuingMismatch blocks) :
    CombinedAdvice width ((blocks.map List.length).sum) :=
  (packRelativeBlocks blocks nonempty positionsSorted lengthLeWidth
    continuingMismatch).advice

/-- Packaging raw blocks preserves their exact sequential replay advice. -/
theorem CombinedAdvice.toQueryList_ofRelativeBlocks
    (blocks : List (List (RelativeQuery width)))
    (nonempty : ∀ block ∈ blocks, block ≠ [])
    (positionsSorted : ∀ block ∈ blocks,
      (block.map Prod.fst).Pairwise (· < ·))
    (lengthLeWidth : ∀ block ∈ blocks, block.length ≤ width)
    (continuingMismatch :
      RelativeBlocksHaveContinuingMismatch blocks) :
    (CombinedAdvice.ofRelativeBlocks blocks nonempty positionsSorted
      lengthLeWidth continuingMismatch).toQueryList =
        relativeBlocksToQueryList blocks :=
  (packRelativeBlocks blocks nonempty positionsSorted lengthLeWidth
    continuingMismatch).toQueryList

private theorem clearLastClose_cons_toQueryAdvice_false
    (query : RelativeQuery width)
    (tail : List (QueryAdvice width)) :
    clearLastClose (query.toQueryAdvice false :: tail) =
      query.toQueryAdvice false :: clearLastClose tail := by
  cases tail with
  | nil => rfl
  | cons next rest => rfl

end Switching

namespace DNF

/-- A canonical raw-block sequence is empty exactly when its elementary
advice transcript is empty. -/
theorem CanonicalTrace.combinedBlocks_eq_nil_iff_adviceList_eq_nil
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) :
    trace.combinedBlocks (widthBound := widthBound) = [] ↔
      trace.adviceList (widthBound := widthBound) = [] := by
  constructor
  · intro blocksEmpty
    have flattened := trace.flatten_combinedBlocks
      (widthBound := widthBound)
    rw [blocksEmpty] at flattened
    simpa using flattened.symm
  · intro adviceEmpty
    have flattened := trace.flatten_combinedBlocks
      (widthBound := widthBound)
    rw [adviceEmpty] at flattened
    simp only [List.map_nil] at flattened
    cases blocksEq : trace.combinedBlocks (widthBound := widthBound) with
    | nil => rfl
    | cons block rest =>
        have blockNonempty := trace.combinedBlocks_nonempty block (by
          rw [blocksEq]
          simp)
        rw [blocksEq, List.flatten_cons] at flattened
        exact False.elim
          (blockNonempty (List.append_eq_nil_iff.mp flattened).1)

mutual

/-- Rebuilding elementary advice from canonical raw blocks gives the original
transcript with its operationally irrelevant final closing marker cleared. -/
theorem CanonicalTrace.relativeBlocksToQueryList_combinedBlocks
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) :
    Switching.relativeBlocksToQueryList
        (trace.combinedBlocks (widthBound := widthBound)) =
      Switching.clearLastClose
        (trace.adviceList (widthBound := widthBound)) :=
  match trace with
  | .nil _ => rfl
  | .start _ _ _ block =>
      block.relativeBlocksToQueryList_combinedBlocks

/-- The same exact reconstruction while traversing one source term. -/
theorem CanonicalBlockTrace.relativeBlocksToQueryList_combinedBlocks
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) :
    Switching.relativeBlocksToQueryList
        (trace.combinedBlocks (widthBound := widthBound)) =
      Switching.clearLastClose
        (trace.adviceList (widthBound := widthBound)) :=
  match trace with
  | .nil _ _ _ => rfl
  | .takeMore (index := index) (value := value) tail => by
      rw [CanonicalBlockTrace.combinedBlocks,
        Switching.relativeBlocksToQueryList_prependToFirstBlock]
      · rw [tail.relativeBlocksToQueryList_combinedBlocks]
        rw [CanonicalBlockTrace.adviceList_takeMore]
        simpa [Switching.RelativeQuery.toQueryAdvice] using
          (Switching.clearLastClose_cons_toQueryAdvice_false
            (term.sourcePosition index,
              Bool.xor (term.satisfyingValue index) value)
            (tail.adviceList (widthBound := widthBound))).symm
      · exact tail.combinedBlocks_nonempty
  | .takeLast (index := index) (value := value) tail => by
      let query : Switching.RelativeQuery widthBound :=
        (term.sourcePosition index,
          Bool.xor (term.satisfyingValue index) value)
      change Switching.relativeBlocksToQueryList
          ([query] :: tail.combinedBlocks) =
        Switching.clearLastClose
          (query.toQueryAdvice true :: tail.adviceList)
      by_cases tailEmpty :
          tail.combinedBlocks (widthBound := widthBound) = []
      · have adviceEmpty :=
          (tail.combinedBlocks_eq_nil_iff_adviceList_eq_nil).1 tailEmpty
        rw [tailEmpty, adviceEmpty]
        rfl
      · have adviceNonempty :
            tail.adviceList (widthBound := widthBound) ≠ [] :=
          fun adviceEmpty => tailEmpty
            ((tail.combinedBlocks_eq_nil_iff_adviceList_eq_nil).2 adviceEmpty)
        cases blocksEq : tail.combinedBlocks (widthBound := widthBound) with
        | nil => exact False.elim (tailEmpty blocksEq)
        | cons next rest =>
            cases adviceEq : tail.adviceList (widthBound := widthBound) with
            | nil => exact False.elim (adviceNonempty adviceEq)
            | cons nextAdvice remainingAdvice =>
                simp only [Switching.relativeBlocksToQueryList,
                  Switching.clearLastClose]
                rw [Switching.relativeBlockToQueryList_singleton]
                rw [← blocksEq,
                  tail.relativeBlocksToQueryList_combinedBlocks,
                  adviceEq]
                rfl

end

/-- Counted combined advice extracted from a bounded canonical trace. -/
def CanonicalTrace.combinedAdvice
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps)
    (bounded : formula.WidthAtMost widthBound) :
    Switching.CombinedAdvice widthBound steps.length :=
  trace.sum_length_combinedBlocks (widthBound := widthBound) ▸
    Switching.CombinedAdvice.ofRelativeBlocks
      (trace.combinedBlocks (widthBound := widthBound))
      trace.combinedBlocks_nonempty
      (trace.combinedBlocks_positions_pairwise bounded)
      (fun _ present => trace.combinedBlock_length_le_width bounded present)
      trace.combinedBlocks_haveContinuingMismatch

/-- Listing a trace's counted combined advice recovers its elementary advice
with only the final, operationally irrelevant closing marker cleared. -/
theorem CanonicalTrace.toQueryList_combinedAdvice
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps)
    (bounded : formula.WidthAtMost widthBound) :
    (trace.combinedAdvice bounded).toQueryList =
      Switching.clearLastClose
        (trace.adviceList (widthBound := widthBound)) := by
  unfold CanonicalTrace.combinedAdvice
  rw [Switching.CombinedAdvice.toQueryList_transport]
  rw [Switching.CombinedAdvice.toQueryList_ofRelativeBlocks]
  exact trace.relativeBlocksToQueryList_combinedBlocks

/-- Reindex counted trace advice by an externally prescribed path length. -/
def CanonicalTrace.combinedAdviceOfLength
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    {pathLength : Nat}
    (trace : formula.CanonicalTrace rho steps)
    (bounded : formula.WidthAtMost widthBound)
    (lengthEq : steps.length = pathLength) :
    Switching.CombinedAdvice widthBound pathLength :=
  lengthEq ▸ trace.combinedAdvice bounded

/-- Reindexing does not change the combined replay list. -/
theorem CanonicalTrace.toQueryList_combinedAdviceOfLength
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    {pathLength : Nat}
    (trace : formula.CanonicalTrace rho steps)
    (bounded : formula.WidthAtMost widthBound)
    (lengthEq : steps.length = pathLength) :
    (trace.combinedAdviceOfLength bounded lengthEq).toQueryList =
      Switching.clearLastClose
        (trace.adviceList (widthBound := widthBound)) := by
  unfold CanonicalTrace.combinedAdviceOfLength
  rw [Switching.CombinedAdvice.toQueryList_transport]
  exact trace.toQueryList_combinedAdvice bounded

/-- Combined advice replays exactly the original canonical path coordinates.
-/
theorem CanonicalTrace.replayIndices_combinedAdviceOfLength
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    {pathLength : Nat}
    (trace : formula.CanonicalTrace rho steps)
    (bounded : formula.WidthAtMost widthBound)
    (lengthEq : steps.length = pathLength) :
    Switching.replayIndices formula
        (rho.refine
          (trace.satisfyingAssignment (widthBound := widthBound))) none
        (trace.combinedAdviceOfLength bounded lengthEq).toQueryList =
      DecisionTree.PathStep.indices steps := by
  rw [trace.toQueryList_combinedAdviceOfLength bounded lengthEq]
  rw [Switching.replayIndices_clearLastClose]
  exact trace.replayIndices_satisfyingAssignment bounded

/-- The combined replay-and-clear decoder is a left inverse of every valid
canonical path encoding. -/
theorem CanonicalPath.decodeCombined_satisfyingEncoding
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {pathLength : Nat}
    (path : formula.CanonicalPath rho pathLength)
    (trace : formula.CanonicalTrace rho path.steps)
    (bounded : formula.WidthAtMost widthBound) :
    Switching.decodeCombined formula
        (rho.refine
          (trace.satisfyingAssignment (widthBound := widthBound)),
          trace.combinedAdviceOfLength bounded path.length_steps) =
      rho := by
  unfold Switching.decodeCombined
  rw [trace.replayIndices_combinedAdviceOfLength bounded path.length_steps]
  have coordinatesEqual :
      (DecisionTree.PathStep.indices path.steps).toFinset =
        (trace.satisfyingAssignment
          (widthBound := widthBound)).fixedVariables := by
    rw [trace.satisfyingAssignment_fixedVariables,
      DecisionTree.PathStep.fixedVariables_assignment]
  rw [coordinatesEqual]
  exact PartialAssignment.clear_refine_fixedVariables rho
    (trace.satisfyingAssignment (widthBound := widthBound))
    (path.satisfyingAssignment_fixesOnlyLive trace)

end DNF
end AC0
end Algebraic
