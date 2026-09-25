/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedCanonicalEncoding
public import Mathlib.Data.List.NodupEquivFin

/-!
# Canonical traces as combined switching blocks

This module extracts the source-term block structure of a canonical DNF path.
Each raw block stores increasing source positions and path bits relative to the
values satisfying the selected term. Every nonfinal block is proved to contain
a mismatch: without one, that term would remain the first surviving term after
its last live variable was fixed, so canonical selection could not start a
later nonempty block.

The result is the structural input to the counted combined advice type. No
formulas, paths, assignments, or circuits are enumerated here.
-/

@[expose] public section

namespace Algebraic
namespace AC0

private theorem idxOf_map_pairwise_lt_of_sublist
    {source selected : List α}
    [BEq α] [LawfulBEq α]
    (sourceNodup : source.Nodup)
    (sublist : selected.Sublist source) :
    (selected.map source.idxOf).Pairwise (· < ·) := by
  obtain ⟨embedding, get_eq⟩ :=
    List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp sublist
  apply List.SortedLT.pairwise
  rw [List.sortedLT_iff_strictMono_get]
  intro left right less
  let left' : Fin selected.length :=
    ⟨left.val, by simpa using left.isLt⟩
  let right' : Fin selected.length :=
    ⟨right.val, by simpa using right.isLt⟩
  simp only [List.get_eq_getElem, List.getElem_map]
  change source.idxOf (selected.get left') <
    source.idxOf (selected.get right')
  rw [get_eq left', get_eq right',
    List.get_idxOf sourceNodup (embedding left'),
    List.get_idxOf sourceNodup (embedding right')]
  exact embedding.strictMono (by simpa [left', right'] using less)

private theorem sourcePositions_pairwise_lt_of_sublist
    [NeZero widthBound]
    (term : Term n)
    (bounded : term.width ≤ widthBound)
    {selected : List (Fin n)}
    (sublist : selected.Sublist term.orderedSupport) :
    (selected.map (term.sourcePosition (widthBound := widthBound))).Pairwise
      (· < ·) := by
  have rankSorted := idxOf_map_pairwise_lt_of_sublist
    term.nodup_orderedSupport sublist
  rw [List.pairwise_map] at rankSorted ⊢
  apply rankSorted.imp_of_mem
  intro left right leftPresent rightPresent less
  change (term.sourcePosition (widthBound := widthBound) left).val <
    (term.sourcePosition (widthBound := widthBound) right).val
  rw [term.sourcePosition_val_of_mem_support left bounded,
    term.sourcePosition_val_of_mem_support right bounded]
  · exact less
  · exact (term.mem_orderedSupport right).1
      (sublist.subset rightPresent)
  · exact (term.mem_orderedSupport left).1
      (sublist.subset leftPresent)

namespace Switching

/-- Position and relative path bit before a block boundary is synthesized. -/
abbrev RelativeQuery (width : Nat) := Fin width × Bool

/-- Forget the block-boundary bit of elementary query advice. -/
def QueryAdvice.toRelativeQuery
    (advice : QueryAdvice width) : RelativeQuery width :=
  (advice.position, advice.difference)

/-- A raw source-term block contains a path value that falsifies one of the
selected term's literals. -/
def RelativeBlockHasMismatch
    (block : List (RelativeQuery width)) : Prop :=
  ∃ query ∈ block, query.2 = true

/-- Every block except the last has a relative path mismatch. -/
def RelativeBlocksHaveContinuingMismatch :
    List (List (RelativeQuery width)) → Prop
  | [] => True
  | [_] => True
  | block :: next :: rest =>
      RelativeBlockHasMismatch block ∧
        RelativeBlocksHaveContinuingMismatch (next :: rest)

/-- Prepend a query to the first block, creating that block when necessary. -/
def prependToFirstBlock
    (query : α) : List (List α) → List (List α)
  | [] => [[query]]
  | block :: rest => (query :: block) :: rest

@[simp] private theorem flatten_prependToFirstBlock
    (query : α)
    (blocks : List (List α)) :
    (prependToFirstBlock query blocks).flatten =
      query :: blocks.flatten := by
  cases blocks <;> simp [prependToFirstBlock]

end Switching

namespace DNF

mutual

/-- Partition a canonical trace into maximal source-term blocks. -/
def CanonicalTrace.combinedBlocks
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) :
    List (List (Switching.RelativeQuery widthBound)) :=
  match trace with
  | .nil _ => []
  | .start _ _ _ block => block.combinedBlocks

/-- Partition the remaining part of a canonical source-term traversal. -/
def CanonicalBlockTrace.combinedBlocks
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) :
    List (List (Switching.RelativeQuery widthBound)) :=
  match trace with
  | .nil _ _ _ => []
  | .takeMore (index := index) (value := value) tail =>
      Switching.prependToFirstBlock
        (term.sourcePosition index,
          Bool.xor (term.satisfyingValue index) value)
        tail.combinedBlocks
  | .takeLast (index := index) (value := value) tail =>
      [(term.sourcePosition index,
        Bool.xor (term.satisfyingValue index) value)] ::
          tail.combinedBlocks

end

mutual

/-- Flattening raw blocks forgets exactly the boundary bit of elementary
canonical advice. -/
theorem CanonicalTrace.flatten_combinedBlocks
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) :
    (trace.combinedBlocks (widthBound := widthBound)).flatten =
      (trace.adviceList (widthBound := widthBound)).map
        Switching.QueryAdvice.toRelativeQuery :=
  match trace with
  | .nil _ => rfl
  | .start _ _ _ block => block.flatten_combinedBlocks

/-- The same flattening correspondence inside one source-term block. -/
theorem CanonicalBlockTrace.flatten_combinedBlocks
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) :
    (trace.combinedBlocks (widthBound := widthBound)).flatten =
      (trace.adviceList (widthBound := widthBound)).map
        Switching.QueryAdvice.toRelativeQuery :=
  match trace with
  | .nil _ _ _ => rfl
  | .takeMore (index := index) (value := value) tail => by
      simp [CanonicalBlockTrace.combinedBlocks,
        CanonicalBlockTrace.adviceList_takeMore,
        Switching.QueryAdvice.toRelativeQuery,
        tail.flatten_combinedBlocks]
  | .takeLast (index := index) (value := value) tail => by
      simp [CanonicalBlockTrace.combinedBlocks,
        CanonicalBlockTrace.adviceList_takeLast,
        Switching.QueryAdvice.toRelativeQuery,
        tail.flatten_combinedBlocks]

end

mutual

/-- Every raw block extracted from a canonical trace is nonempty. -/
theorem CanonicalTrace.combinedBlocks_nonempty
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) :
    ∀ block ∈ trace.combinedBlocks (widthBound := widthBound),
      block ≠ [] :=
  match trace with
  | .nil _ => by simp [CanonicalTrace.combinedBlocks]
  | .start _ _ _ block => block.combinedBlocks_nonempty

/-- The same nonemptiness invariant inside one source-term traversal. -/
theorem CanonicalBlockTrace.combinedBlocks_nonempty
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) :
    ∀ block ∈ trace.combinedBlocks (widthBound := widthBound),
      block ≠ [] :=
  match trace with
  | .nil _ _ _ => by simp [CanonicalBlockTrace.combinedBlocks]
  | .takeMore (term := term) (index := index) (value := value) tail => by
      intro block present
      cases blocksEq : tail.combinedBlocks (widthBound := widthBound) with
      | nil =>
          simp [CanonicalBlockTrace.combinedBlocks,
            Switching.prependToFirstBlock, blocksEq] at present
          subst block
          simp
      | cons head rest =>
          simp only [CanonicalBlockTrace.combinedBlocks,
            Switching.prependToFirstBlock, blocksEq, List.mem_cons] at present
          rcases present with equal | present
          · subst block
            simp
          · exact tail.combinedBlocks_nonempty block
              (by rw [blocksEq]; exact List.mem_cons_of_mem head present)
  | .takeLast (term := term) (index := index) (value := value) tail => by
      intro block present
      simp only [CanonicalBlockTrace.combinedBlocks, List.mem_cons] at present
      rcases present with equal | present
      · subst block
        simp
      · exact tail.combinedBlocks_nonempty block present

end

/-- Canonical block decomposition partitions every query exactly once. -/
theorem CanonicalTrace.sum_length_combinedBlocks
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) :
    ((trace.combinedBlocks (widthBound := widthBound)).map
      List.length).sum = steps.length := by
  rw [← List.length_flatten, trace.flatten_combinedBlocks,
    List.length_map, trace.length_adviceList]

/-- Positions in the first raw block form a sublist of the selected term's
remaining source positions. -/
theorem CanonicalBlockTrace.firstBlock_positions_sublist
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) :
    ∀ block blocks,
      trace.combinedBlocks (widthBound := widthBound) = block :: blocks →
      (block.map Prod.fst).Sublist
        (indices.map (term.sourcePosition (widthBound := widthBound))) :=
  match trace with
  | .nil _ _ _ => by
      simp [CanonicalBlockTrace.combinedBlocks]
  | .takeMore (term := term) (index := index) (next := next)
      (rest := rest) (value := value) tail => by
      intro block blocks equal
      cases tailEq : tail.combinedBlocks (widthBound := widthBound) with
      | nil =>
          simp only [CanonicalBlockTrace.combinedBlocks,
            Switching.prependToFirstBlock, tailEq] at equal
          injection equal with blockEq blocksEq
          subst block
          subst blocks
          simp
      | cons head later =>
          simp only [CanonicalBlockTrace.combinedBlocks,
            Switching.prependToFirstBlock, tailEq] at equal
          injection equal with blockEq blocksEq
          subst block
          subst blocks
          simp only [List.map_cons]
          exact (tail.firstBlock_positions_sublist head later tailEq).cons_cons _
  | .takeLast (term := term) (index := index) (value := value) tail => by
      intro block blocks equal
      simp only [CanonicalBlockTrace.combinedBlocks] at equal
      injection equal with blockEq blocksEq
      subst block
      subst blocks
      simp

mutual

/-- Source positions are strictly increasing within every canonical block. -/
theorem CanonicalTrace.combinedBlocks_positions_pairwise
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps)
    (bounded : formula.WidthAtMost widthBound) :
    ∀ block ∈ trace.combinedBlocks (widthBound := widthBound),
      (block.map Prod.fst).Pairwise (· < ·) :=
  match trace with
  | .nil _ => by simp [CanonicalTrace.combinedBlocks]
  | @CanonicalTrace.start _ _ rho term indices steps found supportEq
      nonempty block => by
      exact block.combinedBlocks_positions_pairwise bounded
        (bounded term (firstSurvivingIn_mem rho formula.terms found))
        supportEq

/-- The same strict source-order invariant inside one source-term traversal. -/
theorem CanonicalBlockTrace.combinedBlocks_positions_pairwise
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps)
    (bounded : formula.WidthAtMost widthBound)
    (termBound : term.width ≤ widthBound)
    (supportEq : liveSupport term rho = indices) :
    ∀ block ∈ trace.combinedBlocks (widthBound := widthBound),
      (block.map Prod.fst).Pairwise (· < ·) :=
  match trace with
  | .nil _ _ _ => by simp [CanonicalBlockTrace.combinedBlocks]
  | .takeMore (rho := rho) (index := index) (next := next)
      (rest := rest) (value := value) tail => by
      intro selected present
      have tailSupport : liveSupport term
          (rho.refine (PartialAssignment.fix index value)) = next :: rest :=
        liveSupport_refine_fix_eq_tail term rho index (next :: rest)
          value supportEq
      cases tailEq : tail.combinedBlocks (widthBound := widthBound) with
      | nil =>
          simp only [CanonicalBlockTrace.combinedBlocks,
            Switching.prependToFirstBlock, tailEq, List.mem_singleton] at present
          subst selected
          simp
      | cons head later =>
          simp only [CanonicalBlockTrace.combinedBlocks,
            Switching.prependToFirstBlock, tailEq, List.mem_cons] at present
          rcases present with current | laterPresent
          · subst selected
            have indicesSublist :
                (index :: next :: rest).Sublist term.orderedSupport := by
              rw [← supportEq]
              exact List.filter_sublist
            have indicesSorted := sourcePositions_pairwise_lt_of_sublist
              term termBound indicesSublist
            have currentSublist :=
              (CanonicalBlockTrace.takeMore tail).firstBlock_positions_sublist
                ((term.sourcePosition index,
                  Bool.xor (term.satisfyingValue index) value) :: head)
                later (by
                  simp [CanonicalBlockTrace.combinedBlocks,
                    Switching.prependToFirstBlock, tailEq])
            exact List.Pairwise.sublist currentSublist indicesSorted
          · exact tail.combinedBlocks_positions_pairwise bounded termBound
              tailSupport selected (by
                rw [tailEq]
                exact List.mem_cons_of_mem head laterPresent)
  | .takeLast (rho := rho) (index := index) (value := value) tail => by
      intro selected present
      simp only [CanonicalBlockTrace.combinedBlocks, List.mem_cons] at present
      rcases present with current | laterPresent
      · subst selected
        simp
      · exact tail.combinedBlocks_positions_pairwise bounded selected laterPresent

end

/-- Every canonical block contains at most the declared source width. -/
theorem CanonicalTrace.combinedBlock_length_le_width
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps)
    (bounded : formula.WidthAtMost widthBound)
    {block : List (Switching.RelativeQuery widthBound)}
    (present : block ∈ trace.combinedBlocks (widthBound := widthBound)) :
    block.length ≤ widthBound := by
  have sorted := trace.combinedBlocks_positions_pairwise bounded block present
  have nodup : (block.map Prod.fst).Nodup := sorted.nodup
  have lengthLe := nodup.length_le_card
  simpa using lengthLe

/-- Queries remaining in the source-term block currently being traversed. -/
def CanonicalBlockTrace.currentRelativeBlock
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) :
    List (Switching.RelativeQuery widthBound) :=
  match trace with
  | .nil _ _ _ => []
  | .takeMore (index := index) (value := value) tail =>
      (term.sourcePosition index,
        Bool.xor (term.satisfyingValue index) value) ::
          tail.currentRelativeBlock
  | .takeLast (index := index) (value := value) _ =>
      [(term.sourcePosition index,
        Bool.xor (term.satisfyingValue index) value)]

/-- Complete source-term blocks following the block currently traversed. -/
def CanonicalBlockTrace.followingRelativeBlocks
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) :
    List (List (Switching.RelativeQuery widthBound)) :=
  match trace with
  | .nil _ _ _ => []
  | .takeMore tail => tail.followingRelativeBlocks
  | .takeLast tail => tail.combinedBlocks

private theorem CanonicalBlockTrace.followingRelativeBlocks_eq_nil_of_current_eq_nil
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps)
    (empty : trace.currentRelativeBlock (widthBound := widthBound) = []) :
    trace.followingRelativeBlocks (widthBound := widthBound) = [] := by
  cases trace <;> simp [CanonicalBlockTrace.currentRelativeBlock,
    CanonicalBlockTrace.followingRelativeBlocks] at empty ⊢

/-- The direct block decomposition is the current nonempty block followed by
the blocks reached after its boundary. -/
theorem CanonicalBlockTrace.combinedBlocks_eq_current_cons_following
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) :
    trace.combinedBlocks (widthBound := widthBound) =
      match trace.currentRelativeBlock (widthBound := widthBound) with
      | [] => []
      | block => block ::
          trace.followingRelativeBlocks (widthBound := widthBound) :=
  match trace with
  | .nil _ _ _ => rfl
  | .takeMore (index := index) (value := value) tail => by
      rw [CanonicalBlockTrace.combinedBlocks,
        CanonicalBlockTrace.currentRelativeBlock,
        CanonicalBlockTrace.followingRelativeBlocks,
        tail.combinedBlocks_eq_current_cons_following]
      cases currentEq :
          tail.currentRelativeBlock (widthBound := widthBound) with
      | nil =>
          have followingEq :=
            tail.followingRelativeBlocks_eq_nil_of_current_eq_nil currentEq
          simp [Switching.prependToFirstBlock, followingEq]
      | cons head remaining =>
          simp [Switching.prependToFirstBlock]
  | .takeLast _ => rfl

/-- A completed current block must contain a falsifying relative bit whenever
canonical selection proceeds to a later block. -/
theorem CanonicalBlockTrace.currentRelativeBlock_hasMismatch_of_following
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps)
    (found : formula.firstSurviving rho = some term)
    (supportEq : liveSupport term rho = indices)
    (hasFollowing :
      trace.followingRelativeBlocks (widthBound := widthBound) ≠ []) :
    Switching.RelativeBlockHasMismatch
      (trace.currentRelativeBlock (widthBound := widthBound)) :=
  match trace with
  | .nil _ _ _ => by
      exact False.elim (hasFollowing rfl)
  | .takeMore (rho := rho) (index := index) (next := next)
      (rest := rest) (value := value) tail => by
      by_cases differs :
          Bool.xor (term.satisfyingValue index) value = true
      · exact ⟨(term.sourcePosition index,
          Bool.xor (term.satisfyingValue index) value), by
            simp [CanonicalBlockTrace.currentRelativeBlock], differs⟩
      · have valueEq : value = term.satisfyingValue index := by
          cases required : term.satisfyingValue index <;>
            cases value <;> simp_all
        have indexData := (mem_liveSupport term rho index).1 (by
          rw [supportEq]
          simp)
        have noConflict := firstSurvivingIn_not_conflicts
          rho formula.terms found
        have survives := term.not_conflicts_refine_fix_satisfying
          rho index noConflict indexData.2 indexData.1
        have tailFound :
            formula.firstSurviving
                (rho.refine (PartialAssignment.fix index value)) =
              some term := by
          rw [valueEq]
          exact formula.firstSurviving_refine rho _ found survives
        have tailSupport :
            liveSupport term
                (rho.refine (PartialAssignment.fix index value)) =
              next :: rest :=
          liveSupport_refine_fix_eq_tail term rho index (next :: rest)
            value supportEq
        obtain ⟨query, queryPresent, queryDiffers⟩ :=
          tail.currentRelativeBlock_hasMismatch_of_following
            tailFound tailSupport (by
              simpa [CanonicalBlockTrace.followingRelativeBlocks] using
                hasFollowing)
        exact ⟨query, by
          simp [CanonicalBlockTrace.currentRelativeBlock, queryPresent],
            queryDiffers⟩
  | .takeLast (rho := rho) (index := index) (value := value) tail => by
      by_cases differs :
          Bool.xor (term.satisfyingValue index) value = true
      · exact ⟨(term.sourcePosition index,
          Bool.xor (term.satisfyingValue index) value), by
            simp [CanonicalBlockTrace.currentRelativeBlock], differs⟩
      · have valueEq : value = term.satisfyingValue index := by
          cases required : term.satisfyingValue index <;>
            cases value <;> simp_all
        subst value
        have indexData := (mem_liveSupport term rho index).1 (by
          rw [supportEq]
          simp)
        have noConflict := firstSurvivingIn_not_conflicts
          rho formula.terms found
        have survives := term.not_conflicts_refine_fix_satisfying
          rho index noConflict indexData.2 indexData.1
        have tailFound :
            formula.firstSurviving
                (rho.refine (PartialAssignment.fix index
                  (term.satisfyingValue index))) = some term :=
          formula.firstSurviving_refine rho _ found survives
        have tailSupportEmpty :
            liveSupport term
                (rho.refine (PartialAssignment.fix index
                  (term.satisfyingValue index))) = [] :=
          liveSupport_refine_fix_eq_tail term rho index []
            (term.satisfyingValue index) supportEq
        cases tail with
        | nil _ =>
            exact False.elim (hasFollowing rfl)
        | @start _ selected selectedIndices tailSteps selectedFound
            selectedSupport selectedNonempty block =>
            have selectedEq : selected = term := by
              rw [tailFound] at selectedFound
              exact (Option.some.inj selectedFound).symm
            subst selected
            rw [tailSupportEmpty] at selectedSupport
            exact False.elim (selectedNonempty selectedSupport.symm)

mutual

/-- Every nonfinal block extracted from a canonical trace has a mismatch. -/
theorem CanonicalTrace.combinedBlocks_haveContinuingMismatch
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps) :
    Switching.RelativeBlocksHaveContinuingMismatch
      (trace.combinedBlocks (widthBound := widthBound)) :=
  match trace with
  | .nil _ => trivial
  | .start found supportEq nonempty block => by
      change Switching.RelativeBlocksHaveContinuingMismatch
        (block.combinedBlocks (widthBound := widthBound))
      rw [block.combinedBlocks_eq_current_cons_following]
      cases currentEq :
          block.currentRelativeBlock (widthBound := widthBound) with
      | nil => trivial
      | cons query queries =>
          cases followingEq :
              block.followingRelativeBlocks (widthBound := widthBound) with
          | nil => trivial
          | cons next rest =>
              have hasFollowing :
                  block.followingRelativeBlocks
                      (widthBound := widthBound) ≠ [] := by
                rw [followingEq]
                simp
              have mismatch :=
                block.currentRelativeBlock_hasMismatch_of_following
                  found supportEq hasFollowing
              rw [currentEq] at mismatch
              have followingValid :=
                block.followingRelativeBlocks_haveContinuingMismatch
                  (widthBound := widthBound)
              rw [followingEq] at followingValid
              exact ⟨mismatch, followingValid⟩

/-- Blocks reached after the current source term inherit the nonfinal mismatch
property from their nested canonical traces. -/
theorem CanonicalBlockTrace.followingRelativeBlocks_haveContinuingMismatch
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalBlockTrace term rho indices steps) :
    Switching.RelativeBlocksHaveContinuingMismatch
      (trace.followingRelativeBlocks (widthBound := widthBound)) :=
  match trace with
  | .nil _ _ _ => trivial
  | .takeMore tail =>
      tail.followingRelativeBlocks_haveContinuingMismatch
  | .takeLast tail => tail.combinedBlocks_haveContinuingMismatch

end

end DNF

end AC0
end Algebraic
