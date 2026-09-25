/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.CanonicalDecisionTree
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.Encoding

/-!
# Canonical switching-path advice

This module turns a typed canonical DNF path trace into the local data used by
the switching-lemma injection. Each query is annotated with

* its position in the selected source term,
* whether it closes the current term block,
* whether the original path bit differs from the satisfying literal value, and
* the value satisfying that source literal.

Only the first three fields become finite advice. The queried coordinate and
satisfying value remain internal witnesses used to define the output
restriction and prove reconstruction. No paths or circuits are enumerated.
-/

@[expose] public section

namespace Algebraic
namespace AC0

namespace LiteralSet

/-- Deterministic Boolean value extracted from a literal requirement. On the
support of the literal set this is its unique satisfying value. -/
def satisfyingValue
    (set : LiteralSet n)
    (index : Fin n) : Bool :=
  (set.requirements index).getD false

end LiteralSet

namespace Switching

/-- One symbol of switching advice. The position names a variable within the
currently selected source term. -/
structure QueryAdvice (widthBound : Nat) where
  /-- Zero-based position in the selected source term's ordered support. -/
  position : Fin widthBound
  /-- Whether this query is the last one in the current source-term block. -/
  closesBlock : Bool
  /-- Whether the path bit differs from the selected literal's satisfying
  value. -/
  difference : Bool
  deriving DecidableEq, Fintype

/-- Recover the original path bit from its value relative to the selected
literal's satisfying value. -/
def QueryAdvice.decodeValue
    (advice : QueryAdvice widthBound)
    (satisfyingValue : Bool) : Bool :=
  Bool.xor satisfyingValue advice.difference

/-- Encoding a path bit by its difference from the satisfying value and then
decoding it recovers that path bit. -/
@[simp] theorem QueryAdvice.decodeValue_mk_xor
    (position : Fin widthBound)
    (closesBlock satisfyingValue pathValue : Bool) :
    (QueryAdvice.mk position closesBlock
        (Bool.xor satisfyingValue pathValue)).decodeValue satisfyingValue =
      pathValue := by
  cases satisfyingValue <;> cases pathValue <;> rfl

/-- Fixed-length switching advice. -/
abbrev Advice (widthBound pathLength : Nat) :=
  Fin pathLength → QueryAdvice widthBound

/-- Internal annotation of one canonical query. The source term, coordinate,
and satisfying value are deliberately not part of the finite advice. -/
structure QueryRecord (n widthBound : Nat) where
  /-- Source term selected for this block. -/
  term : Term n
  /-- Coordinate queried at this step. -/
  index : Fin n
  /-- Value that satisfies the source literal at `index`. -/
  satisfyingValue : Bool
  /-- Finite symbol retained by the switching encoding. -/
  advice : QueryAdvice widthBound
  deriving DecidableEq

/-- The two local facts needed to decode an internal query record: its hidden
value satisfies the named literal, and its public position selects the hidden
coordinate from the source term. -/
def QueryRecord.WellFormed
    (record : QueryRecord n widthBound) : Prop :=
  record.term.requirements record.index = some record.satisfyingValue ∧
    record.term.orderedSupport[record.advice.position.val]? =
      some record.index

/-- The internal query record's satisfying assignment step. -/
def QueryRecord.satisfyingStep
    (record : QueryRecord n widthBound) : DecisionTree.PathStep n :=
  ⟨record.index, record.satisfyingValue⟩

/-- Forget the internal fields of a query record. -/
def QueryRecord.toAdvice
    (record : QueryRecord n widthBound) : QueryAdvice widthBound :=
  record.advice

/-- Query advice is exactly a bounded position and two bits. -/
def QueryAdvice.equivProduct (widthBound : Nat) :
    QueryAdvice widthBound ≃ Fin widthBound × Bool × Bool where
  toFun advice := (advice.position, advice.closesBlock, advice.difference)
  invFun fields := ⟨fields.1, fields.2.1, fields.2.2⟩
  left_inv advice := by cases advice; rfl
  right_inv fields := by rcases fields with ⟨position, closes, value⟩; rfl

/-- There are exactly `4 * widthBound` possible symbols per query. -/
theorem card_queryAdvice (widthBound : Nat) :
    Fintype.card (QueryAdvice widthBound) = 4 * widthBound := by
  rw [Fintype.card_congr (QueryAdvice.equivProduct widthBound)]
  simp
  omega

/-- Fixed-length advice has the exact cardinality used by the weighted
switching calculation. -/
theorem card_advice (widthBound pathLength : Nat) :
    Fintype.card (Advice widthBound pathLength) =
      (4 * widthBound) ^ pathLength := by
  simp [Advice, card_queryAdvice]

/-- Reindex a list of known length as a fixed finite function. -/
def listToFn
    (values : List α)
    {length : Nat}
    (length_eq : values.length = length) : Fin length → α :=
  fun index => values.get (Fin.cast length_eq.symm index)

/-- Reindexing a list and then listing the function loses no information. -/
theorem ofFn_listToFn
    (values : List α)
    {length : Nat}
    (length_eq : values.length = length) :
    List.ofFn (listToFn values length_eq) = values := by
  subst length
  exact List.ofFn_get values

/-- Choose the source term currently being decoded. A term is retained inside
a block; at a block boundary the canonical first-surviving selector is run on
the replay state. -/
def selectTerm
    (formula : DNF n)
    (state : PartialAssignment n) : Option (Term n) → Option (Term n)
  | some term => some term
  | none => formula.firstSurviving state

/-- Replay switching advice and recover its queried coordinates. Malformed
advice is handled totally by returning the successfully decoded prefix. -/
def replayIndices
    (formula : DNF n) :
    PartialAssignment n → Option (Term n) →
      List (QueryAdvice widthBound) → List (Fin n)
  | _, _, [] => []
  | state, currentTerm, symbol :: rest =>
      match selectTerm formula state currentTerm with
      | none => []
      | some term =>
          match term.orderedSupport[symbol.position.val]? with
          | none => []
          | some index =>
              index :: replayIndices formula
                ((PartialAssignment.fix index
                    (symbol.decodeValue (term.satisfyingValue index))).refine
                  state)
                (if symbol.closesBlock then none else some term) rest

/-- Decode an encoded restriction/advice pair by replaying its coordinates and
clearing them from the refined restriction. -/
def decode
    (formula : DNF n)
    (encoded : PartialAssignment n × Advice widthBound pathLength) :
    PartialAssignment n :=
  encoded.1.clear
    (replayIndices formula encoded.1 none (List.ofFn encoded.2)).toFinset

/-- If the canonical selector returns `term`, replay from a block boundary is
the same as replay with `term` already selected. -/
theorem replayIndices_none_eq_some_of_firstSurviving
    (formula : DNF n)
    (state : PartialAssignment n)
    (term : Term n)
    (found : formula.firstSurviving state = some term)
    (advice : List (QueryAdvice widthBound)) :
    replayIndices formula state none advice =
      replayIndices formula state (some term) advice := by
  cases advice with
  | nil => rfl
  | cons symbol rest => simp [replayIndices, selectTerm, found]

end Switching

namespace LiteralSet

/-- Position of a coordinate in a source term, reduced into the declared
width bound. Valid traced queries are proved below to lie below the bound, so
the reduction does not change their position. -/
def sourcePosition
    [NeZero widthBound]
    (set : LiteralSet n)
    (index : Fin n) : Fin widthBound :=
  Fin.ofNat widthBound (set.orderedSupport.idxOf index)

/-- A support coordinate's extracted Boolean value is its literal's required
value. -/
theorem requirements_satisfyingValue_of_mem_support
    (set : LiteralSet n)
    (index : Fin n)
    (present : index ∈ set.support) :
    set.requirements index = some (set.satisfyingValue index) := by
  rw [mem_support] at present
  unfold satisfyingValue
  cases required : set.requirements index with
  | none => exact False.elim (present required)
  | some value => rfl

/-- The ordered support lists each support coordinate exactly once, so its
length is the literal-set width. -/
theorem length_orderedSupport (set : LiteralSet n) :
    set.orderedSupport.length = set.width := by
  rw [← List.toFinset_card_of_nodup set.nodup_orderedSupport]
  congr 1
  ext index
  simp

/-- For a valid bounded term coordinate, reduction modulo the width bound is
inert. -/
theorem sourcePosition_val_of_mem_support
    [NeZero widthBound]
    (set : LiteralSet n)
    (index : Fin n)
    (bounded : set.width ≤ widthBound)
    (present : index ∈ set.support) :
    (set.sourcePosition (widthBound := widthBound) index).val =
      set.orderedSupport.idxOf index := by
  have orderedPresent : index ∈ set.orderedSupport :=
    (mem_orderedSupport set index).2 present
  have belowWidth : set.orderedSupport.idxOf index < set.width := by
    rw [← set.length_orderedSupport]
    exact List.idxOf_lt_length_iff.mpr orderedPresent
  simp [sourcePosition,
    Nat.mod_eq_of_lt (belowWidth.trans_le bounded)]

/-- Decoding a valid bounded source position recovers its coordinate. -/
theorem getElem?_sourcePosition_of_mem_support
    [NeZero widthBound]
    (set : LiteralSet n)
    (index : Fin n)
    (bounded : set.width ≤ widthBound)
    (present : index ∈ set.support) :
    set.orderedSupport[
        (set.sourcePosition (widthBound := widthBound) index).val]? =
      some index := by
  rw [set.sourcePosition_val_of_mem_support index bounded present]
  exact List.getElem?_idxOf ((mem_orderedSupport set index).2 present)

/-- Assigning a live support coordinate its satisfying value preserves
nonconflict with the literal set. -/
theorem not_conflicts_refine_fix_satisfying
    (set : LiteralSet n)
    (rho : PartialAssignment n)
    (index : Fin n)
    (noConflict : ¬set.ConflictsWith rho)
    (live : rho index = none)
    (present : index ∈ set.support) :
    ¬set.ConflictsWith
      (rho.refine (PartialAssignment.fix index (set.satisfyingValue index))) := by
  intro conflict
  obtain ⟨current, required, fixed, setValue, refinedValue, different⟩ :=
    conflict
  by_cases equal : current = index
  · subst current
    have requiredValue :=
      set.requirements_satisfyingValue_of_mem_support index present
    rw [requiredValue] at setValue
    injection setValue with requiredEqual
    subst required
    simp [PartialAssignment.refine, PartialAssignment.fix, live] at refinedValue
    exact different refinedValue
  · cases sourceValue : rho current with
    | none =>
        simp [PartialAssignment.refine, PartialAssignment.fix, equal,
          sourceValue] at refinedValue
    | some source =>
        have fixedEqual : fixed = source := by
          simpa [PartialAssignment.refine, sourceValue] using refinedValue.symm
        subst fixed
        exact noConflict
          ⟨current, required, source, setValue, sourceValue, different⟩

/-- Once a nonconflicting literal set has no live support, no later
refinement can create a conflict with it. -/
theorem not_conflicts_refine_of_liveSupport_eq_nil
    (set : LiteralSet n)
    (rho extension : PartialAssignment n)
    (noConflict : ¬set.ConflictsWith rho)
    (supportEmpty : DNF.liveSupport set rho = []) :
    ¬set.ConflictsWith (rho.refine extension) := by
  intro conflict
  obtain ⟨index, required, fixed, setValue, refinedValue, different⟩ :=
    conflict
  cases sourceValue : rho index with
  | some source =>
      have fixedEqual : fixed = source := by
        simpa [PartialAssignment.refine, sourceValue] using refinedValue.symm
      subst fixed
      exact noConflict
        ⟨index, required, source, setValue, sourceValue, different⟩
  | none =>
      have supportPresent : index ∈ set.support :=
        (mem_support set index).2 (by simp [setValue])
      have livePresent : index ∈ DNF.liveSupport set rho :=
        (DNF.mem_liveSupport set rho index).2 ⟨supportPresent, sourceValue⟩
      rw [supportEmpty] at livePresent
      simp at livePresent

/-- A refinement cannot falsify a nonconflicting literal set when every value
it adds on the set's live support is either absent or the satisfying value. -/
theorem not_conflicts_refine_of_satisfying_on_liveSupport
    (set : LiteralSet n)
    (rho extension : PartialAssignment n)
    (noConflict : ¬set.ConflictsWith rho)
    (compatible : ∀ index, index ∈ DNF.liveSupport set rho →
      extension index = none ∨
        extension index = some (set.satisfyingValue index)) :
    ¬set.ConflictsWith (rho.refine extension) := by
  intro conflict
  obtain ⟨index, required, fixed, setValue, refinedValue, different⟩ :=
    conflict
  cases sourceValue : rho index with
  | some source =>
      have fixedEqual : fixed = source := by
        simpa [PartialAssignment.refine, sourceValue] using refinedValue.symm
      subst fixed
      exact noConflict
        ⟨index, required, source, setValue, sourceValue, different⟩
  | none =>
      have supportPresent : index ∈ set.support :=
        (mem_support set index).2 (by simp [setValue])
      have livePresent : index ∈ DNF.liveSupport set rho :=
        (DNF.mem_liveSupport set rho index).2 ⟨supportPresent, sourceValue⟩
      rcases compatible index livePresent with extensionLive | extensionValue
      · simp [PartialAssignment.refine, sourceValue, extensionLive] at refinedValue
      · have requiredValue :=
          set.requirements_satisfyingValue_of_mem_support index supportPresent
        rw [requiredValue] at setValue
        injection setValue with requiredEqual
        subst required
        have fixedEqual : fixed = set.satisfyingValue index := by
          simpa [PartialAssignment.refine, sourceValue, extensionValue] using
            refinedValue.symm
        exact different fixedEqual.symm

end LiteralSet

namespace DNF

/-- Fixing the head of a live-support list removes exactly that coordinate. -/
theorem liveSupport_refine_fix_eq_tail
    (term : Term n)
    (rho : PartialAssignment n)
    (index : Fin n)
    (rest : List (Fin n))
    (value : Bool)
    (support_eq : liveSupport term rho = index :: rest) :
    liveSupport term
        (rho.refine (PartialAssignment.fix index value)) = rest := by
  have filterEq :
      liveSupport term (rho.refine (PartialAssignment.fix index value)) =
        (liveSupport term rho).filter fun current => decide (current ≠ index) := by
    unfold liveSupport
    rw [List.filter_filter]
    apply List.filter_congr
    intro current _
    apply Bool.eq_iff_iff.mpr
    by_cases sourceLive : rho current = none
    · by_cases equal : current = index
      · subst current
        simp [PartialAssignment.refine, PartialAssignment.fix, sourceLive]
      · simp [PartialAssignment.refine, PartialAssignment.fix, sourceLive,
          equal]
    · cases sourceValue : rho current with
      | none => contradiction
      | some fixed =>
          simp [PartialAssignment.refine, sourceValue]
  rw [filterEq, support_eq]
  have nodup : (index :: rest).Nodup := by
    simpa [support_eq] using nodup_liveSupport term rho
  have indexAbsent : index ∉ rest := (List.nodup_cons.mp nodup).1
  have allDifferent : ∀ current ∈ rest, current ≠ index := by
    intro current present equal
    subst current
    exact indexAbsent present
  rw [List.filter_cons_of_neg (by simp)]
  apply List.filter_eq_self.mpr
  intro current present
  simp [allDifferent current present]

mutual

/-- Annotate all queries in a canonical trace. -/
def CanonicalTrace.queryRecords
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    List (Switching.QueryRecord n widthBound) :=
  match trace with
  | .nil _ => []
  | .start _ _ _ block => block.queryRecords

/-- Annotate the queries remaining in one canonical source-term block. -/
def CanonicalBlockTrace.queryRecords
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalBlockTrace formula term rho indices steps) :
    List (Switching.QueryRecord n widthBound) :=
  match trace with
  | .nil _ _ _ => []
  | .takeMore (index := index) (value := value) tail =>
      ⟨term, index, term.satisfyingValue index,
        ⟨term.sourcePosition index, false,
          Bool.xor (term.satisfyingValue index) value⟩⟩ ::
        tail.queryRecords
  | .takeLast (index := index) (value := value) tail =>
      ⟨term, index, term.satisfyingValue index,
        ⟨term.sourcePosition index, true,
          Bool.xor (term.satisfyingValue index) value⟩⟩ ::
        tail.queryRecords

end

/-- The satisfying query transcript underlying the output assignment. -/
def CanonicalTrace.satisfyingSteps
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    List (DecisionTree.PathStep n) :=
  trace.queryRecords (widthBound := widthBound) |>.map
    Switching.QueryRecord.satisfyingStep

/-- Satisfying transcript for the remaining queries of one source-term
block. -/
def CanonicalBlockTrace.satisfyingSteps
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalBlockTrace formula term rho indices steps) :
    List (DecisionTree.PathStep n) :=
  trace.queryRecords (widthBound := widthBound) |>.map
    Switching.QueryRecord.satisfyingStep

/-- Satisfying assignment placed into the injection's output restriction. -/
def CanonicalTrace.satisfyingAssignment
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) : PartialAssignment n :=
  DecisionTree.PathStep.assignment
    (trace.satisfyingSteps (widthBound := widthBound))

/-- Satisfying assignment for the remaining queries of one source-term
block. -/
def CanonicalBlockTrace.satisfyingAssignment
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalBlockTrace formula term rho indices steps) :
    PartialAssignment n :=
  DecisionTree.PathStep.assignment
    (trace.satisfyingSteps (widthBound := widthBound))

/-- Variable-length advice before it is reindexed by the prescribed path
length. -/
def CanonicalTrace.adviceList
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    List (Switching.QueryAdvice widthBound) :=
  trace.queryRecords.map Switching.QueryRecord.toAdvice

/-- Variable-length advice for the remaining queries in one source-term
block. -/
def CanonicalBlockTrace.adviceList
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalBlockTrace formula term rho indices steps) :
    List (Switching.QueryAdvice widthBound) :=
  trace.queryRecords.map Switching.QueryRecord.toAdvice

@[simp] theorem CanonicalTrace.satisfyingAssignment_start
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {term : Term n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (found : formula.firstSurviving rho = some term)
    (support_eq : liveSupport term rho = indices)
    (nonempty : indices ≠ [])
    (block : DNF.CanonicalBlockTrace formula term rho indices steps) :
    (CanonicalTrace.start found support_eq nonempty block).satisfyingAssignment
        (widthBound := widthBound) =
      block.satisfyingAssignment (widthBound := widthBound) := rfl

@[simp] theorem CanonicalTrace.adviceList_start
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {term : Term n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (found : formula.firstSurviving rho = some term)
    (support_eq : liveSupport term rho = indices)
    (nonempty : indices ≠ [])
    (block : DNF.CanonicalBlockTrace formula term rho indices steps) :
    (CanonicalTrace.start found support_eq nonempty block).adviceList
        (widthBound := widthBound) =
      block.adviceList (widthBound := widthBound) := rfl

@[simp] theorem CanonicalBlockTrace.satisfyingAssignment_takeMore
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {index next : Fin n}
    {rest : List (Fin n)}
    {value : Bool}
    {steps : List (DecisionTree.PathStep n)}
    (tail : DNF.CanonicalBlockTrace formula term
      (rho.refine (PartialAssignment.fix index value))
      (next :: rest) steps) :
    (CanonicalBlockTrace.takeMore tail).satisfyingAssignment
        (widthBound := widthBound) =
      (PartialAssignment.fix index (term.satisfyingValue index)).refine
        (tail.satisfyingAssignment (widthBound := widthBound)) := rfl

@[simp] theorem CanonicalBlockTrace.adviceList_takeMore
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {index next : Fin n}
    {rest : List (Fin n)}
    {value : Bool}
    {steps : List (DecisionTree.PathStep n)}
    (tail : DNF.CanonicalBlockTrace formula term
      (rho.refine (PartialAssignment.fix index value))
      (next :: rest) steps) :
    (CanonicalBlockTrace.takeMore tail).adviceList
        (widthBound := widthBound) =
      ⟨term.sourcePosition index, false,
        Bool.xor (term.satisfyingValue index) value⟩ ::
        tail.adviceList := rfl

@[simp] theorem CanonicalBlockTrace.satisfyingAssignment_takeLast
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {index : Fin n}
    {value : Bool}
    {steps : List (DecisionTree.PathStep n)}
    (tail : DNF.CanonicalTrace formula
      (rho.refine (PartialAssignment.fix index value)) steps) :
    (CanonicalBlockTrace.takeLast (term := term) tail).satisfyingAssignment
        (widthBound := widthBound) =
      (PartialAssignment.fix index (term.satisfyingValue index)).refine
        (tail.satisfyingAssignment (widthBound := widthBound)) := rfl

@[simp] theorem CanonicalBlockTrace.adviceList_takeLast
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {index : Fin n}
    {value : Bool}
    {steps : List (DecisionTree.PathStep n)}
    (tail : DNF.CanonicalTrace formula
      (rho.refine (PartialAssignment.fix index value)) steps) :
    (CanonicalBlockTrace.takeLast (term := term) tail).adviceList
        (widthBound := widthBound) =
      ⟨term.sourcePosition index, true,
        Bool.xor (term.satisfyingValue index) value⟩ ::
        tail.adviceList := rfl

mutual

/-- Query-record coordinates agree exactly with the original path
coordinates. -/
theorem CanonicalTrace.queryRecords_indices
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    (trace.queryRecords (widthBound := widthBound)).map
        Switching.QueryRecord.index =
      DecisionTree.PathStep.indices steps :=
  match trace with
  | .nil _ => rfl
  | .start _ _ _ block => block.queryRecords_indices

/-- The same coordinate agreement while traversing a source-term block. -/
theorem CanonicalBlockTrace.queryRecords_indices
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalBlockTrace formula term rho indices steps) :
    (trace.queryRecords (widthBound := widthBound)).map
        Switching.QueryRecord.index =
      DecisionTree.PathStep.indices steps :=
  match trace with
  | .nil _ _ _ => rfl
  | .takeMore tail => congrArg (List.cons _) tail.queryRecords_indices
  | .takeLast tail => congrArg (List.cons _) tail.queryRecords_indices

end

mutual

/-- Every record extracted from a width-bounded canonical trace carries a
genuine satisfying literal value and a correctly decodable source position.
-/
theorem CanonicalTrace.queryRecords_wellFormed
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps)
    (bounded : formula.WidthAtMost widthBound) :
    ∀ record ∈ trace.queryRecords (widthBound := widthBound),
      Switching.QueryRecord.WellFormed record :=
  match trace with
  | .nil _ => by simp [CanonicalTrace.queryRecords]
  | @CanonicalTrace.start _ _ rho term indices steps found support_eq
      _ block =>
      block.queryRecords_wellFormed
        bounded
        (bounded term (firstSurvivingIn_mem rho formula.terms found))
        (fun index present =>
          (mem_liveSupport term rho index).1 (by
            simpa [support_eq] using present) |>.1)

/-- The record invariant while traversing one source-term block. -/
theorem CanonicalBlockTrace.queryRecords_wellFormed
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalBlockTrace formula term rho indices steps)
    (bounded : formula.WidthAtMost widthBound)
    (termBound : term.width ≤ widthBound)
    (supported : ∀ index, index ∈ indices → index ∈ term.support) :
    ∀ record ∈ trace.queryRecords (widthBound := widthBound),
      Switching.QueryRecord.WellFormed record :=
  match trace with
  | .nil _ _ _ => by simp [CanonicalBlockTrace.queryRecords]
  | @CanonicalBlockTrace.takeMore _ _ _ _ index next rest value steps tail =>
      by
        intro record present
        simp only [CanonicalBlockTrace.queryRecords,
          List.mem_cons] at present
        rcases present with rfl | present
        · exact ⟨term.requirements_satisfyingValue_of_mem_support index
              (supported index (by simp)),
            term.getElem?_sourcePosition_of_mem_support index termBound
              (supported index (by simp))⟩
        · exact tail.queryRecords_wellFormed bounded termBound
            (fun current currentPresent =>
              supported current (by simp [currentPresent])) record present
  | @CanonicalBlockTrace.takeLast _ _ _ _ index value steps tail =>
      by
        intro record present
        simp only [CanonicalBlockTrace.queryRecords,
          List.mem_cons] at present
        rcases present with rfl | present
        · exact ⟨term.requirements_satisfyingValue_of_mem_support index
              (supported index (by simp)),
            term.getElem?_sourcePosition_of_mem_support index termBound
              (supported index (by simp))⟩
        · exact tail.queryRecords_wellFormed bounded record present

end

/-- The satisfying transcript queries precisely the original path's
coordinates, changing only their Boolean values. -/
theorem CanonicalTrace.satisfyingSteps_indices
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    DecisionTree.PathStep.indices
        (trace.satisfyingSteps (widthBound := widthBound)) =
      DecisionTree.PathStep.indices steps := by
  simpa [CanonicalTrace.satisfyingSteps,
    DecisionTree.PathStep.indices, List.map_map,
    Function.comp_def, Switching.QueryRecord.satisfyingStep] using
    trace.queryRecords_indices (widthBound := widthBound)

/-- The satisfying assignment fixes the same coordinates as the original
path assignment. -/
theorem CanonicalTrace.satisfyingAssignment_fixedVariables
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    (trace.satisfyingAssignment (widthBound := widthBound)).fixedVariables =
      (DecisionTree.PathStep.assignment steps).fixedVariables := by
  unfold CanonicalTrace.satisfyingAssignment
  rw [DecisionTree.PathStep.fixedVariables_assignment,
    DecisionTree.PathStep.fixedVariables_assignment]
  exact congrArg List.toFinset
    (trace.satisfyingSteps_indices (widthBound := widthBound))

/-- Variable-length advice has one symbol per original path query. -/
theorem CanonicalTrace.length_adviceList
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps) :
    (trace.adviceList (widthBound := widthBound)).length = steps.length := by
  have equalLengths := congrArg List.length
    (trace.queryRecords_indices (widthBound := widthBound))
  simpa [CanonicalTrace.adviceList,
    DecisionTree.PathStep.indices] using equalLengths

/-- Fixed-length advice associated to a trace whose path has the prescribed
length. -/
def CanonicalTrace.advice
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    {pathLength : Nat}
    (trace : DNF.CanonicalTrace formula rho steps)
    (length_eq : steps.length = pathLength) :
    Switching.Advice widthBound pathLength :=
  Switching.listToFn trace.adviceList
    ((trace.length_adviceList (widthBound := widthBound)).trans length_eq)

/-- Listing fixed-length trace advice recovers the original advice list. -/
theorem CanonicalTrace.ofFn_advice
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    {pathLength : Nat}
    (trace : DNF.CanonicalTrace formula rho steps)
    (length_eq : steps.length = pathLength) :
    List.ofFn (trace.advice (widthBound := widthBound) length_eq) =
      trace.adviceList := by
  unfold CanonicalTrace.advice
  apply Switching.ofFn_listToFn

/-- On every pending coordinate, a block's satisfying assignment either
leaves the variable live or assigns the selected term's satisfying value. -/
theorem CanonicalBlockTrace.satisfyingAssignment_compatible
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalBlockTrace formula term rho indices steps)
    (nodup : indices.Nodup) :
    ∀ index, index ∈ indices →
      trace.satisfyingAssignment (widthBound := widthBound) index = none ∨
        trace.satisfyingAssignment (widthBound := widthBound) index =
          some (term.satisfyingValue index) :=
  match trace with
  | .nil _ index rest => by
      intro current present
      left
      simp [CanonicalBlockTrace.satisfyingAssignment,
        CanonicalBlockTrace.satisfyingSteps,
        CanonicalBlockTrace.queryRecords, PartialAssignment.empty]
  | .takeMore (index := index) (next := next) (rest := rest) tail =>
      by
        intro current present
        have data := List.mem_cons.mp present
        rcases data with equal | inRest
        · subst current
          right
          simp [CanonicalBlockTrace.satisfyingAssignment,
            CanonicalBlockTrace.satisfyingSteps,
            CanonicalBlockTrace.queryRecords,
            Switching.QueryRecord.satisfyingStep,
            PartialAssignment.refine, PartialAssignment.fix]
        · have headAbsent : index ∉ next :: rest :=
            (List.nodup_cons.mp nodup).1
          have different : current ≠ index := by
            intro equal
            subst current
            exact headAbsent inRest
          have tailCompatible :=
            tail.satisfyingAssignment_compatible
              (widthBound := widthBound)
              (List.nodup_cons.mp nodup).2 current inRest
          simpa [CanonicalBlockTrace.satisfyingAssignment,
            CanonicalBlockTrace.satisfyingSteps,
            CanonicalBlockTrace.queryRecords,
            Switching.QueryRecord.satisfyingStep,
            PartialAssignment.refine, PartialAssignment.fix, different] using
            tailCompatible
  | .takeLast (index := index) tail =>
      by
        intro current present
        have equal : current = index := by simpa using present
        subst current
        right
        simp [CanonicalBlockTrace.satisfyingAssignment,
          CanonicalBlockTrace.satisfyingSteps,
          CanonicalBlockTrace.queryRecords,
          Switching.QueryRecord.satisfyingStep,
          PartialAssignment.refine, PartialAssignment.fix]

/-- Satisfying all queries remaining in one source-term block never falsifies
that term. The invariant `support_eq` says precisely which of its source
coordinates are still live at the current state. -/
theorem CanonicalBlockTrace.not_conflicts_refine_satisfyingAssignment
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalBlockTrace formula term rho indices steps)
    (support_eq : liveSupport term rho = indices)
    (noConflict : ¬term.ConflictsWith rho) :
    ¬term.ConflictsWith
      (rho.refine
        (trace.satisfyingAssignment (widthBound := widthBound))) := by
  apply term.not_conflicts_refine_of_satisfying_on_liveSupport
    rho trace.satisfyingAssignment noConflict
  intro index present
  apply trace.satisfyingAssignment_compatible
  · rw [← support_eq]
    exact nodup_liveSupport term rho
  · simpa [support_eq] using present

/-- A source term surviving at the start of a canonical trace still survives
after the trace's satisfying assignment is added. -/
theorem CanonicalTrace.not_conflicts_refine_satisfyingAssignment
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps)
    {term : Term n}
    (found : formula.firstSurviving rho = some term) :
    ¬term.ConflictsWith
      (rho.refine
        (trace.satisfyingAssignment (widthBound := widthBound))) :=
  match trace with
  | .nil _ => by
      have noConflict := firstSurvivingIn_not_conflicts
        rho formula.terms found
      simpa [CanonicalTrace.satisfyingAssignment,
        CanonicalTrace.satisfyingSteps,
        CanonicalTrace.queryRecords] using noConflict
  | @CanonicalTrace.start _ _ rho selected indices steps selectedFound
      support_eq nonempty block => by
      have termEqual : term = selected := by
        rw [selectedFound] at found
        exact (Option.some.inj found).symm
      subst term
      have noConflict := firstSurvivingIn_not_conflicts
        rho formula.terms selectedFound
      have compatible :=
        block.not_conflicts_refine_satisfyingAssignment
          (widthBound := widthBound) support_eq noConflict
      change ¬selected.ConflictsWith
        (rho.refine
          (block.satisfyingAssignment (widthBound := widthBound)))
      exact compatible

/-- The first-surviving source-term selector is unchanged when the satisfying
assignment extracted from the trace is added. This is the selector equation
used by the reconstruction decoder. -/
theorem CanonicalTrace.firstSurviving_refine_satisfyingAssignment
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps)
    {term : Term n}
    (found : formula.firstSurviving rho = some term) :
    formula.firstSurviving
        (rho.refine
          (trace.satisfyingAssignment (widthBound := widthBound))) =
      some term :=
  formula.firstSurviving_refine rho
    (trace.satisfyingAssignment (widthBound := widthBound)) found
    (trace.not_conflicts_refine_satisfyingAssignment found)

mutual

/-- Replaying the advice extracted from a satisfying canonical trace recovers
the original path's query coordinates exactly. -/
theorem CanonicalTrace.replayIndices_satisfyingAssignment
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalTrace formula rho steps)
    (bounded : formula.WidthAtMost widthBound) :
    Switching.replayIndices formula
        (rho.refine
          (trace.satisfyingAssignment (widthBound := widthBound)))
        none (trace.adviceList (widthBound := widthBound)) =
      DecisionTree.PathStep.indices steps :=
  match trace with
  | .nil _ => rfl
  | @CanonicalTrace.start _ _ rho term indices steps found support_eq
      nonempty block => by
      change Switching.replayIndices formula
          (rho.refine
            (block.satisfyingAssignment (widthBound := widthBound)))
          none (block.adviceList (widthBound := widthBound)) =
        DecisionTree.PathStep.indices steps
      have noConflict := firstSurvivingIn_not_conflicts
        rho formula.terms found
      have compatible :=
        block.not_conflicts_refine_satisfyingAssignment
          (widthBound := widthBound) support_eq noConflict
      have selector := formula.firstSurviving_refine rho
        (block.satisfyingAssignment (widthBound := widthBound))
        found compatible
      have boundary :=
        Switching.replayIndices_none_eq_some_of_firstSurviving formula
          (rho.refine
            (block.satisfyingAssignment (widthBound := widthBound)))
          term selector (block.adviceList (widthBound := widthBound))
      rw [boundary]
      exact block.replayIndices_satisfyingAssignment bounded
        (bounded term (firstSurvivingIn_mem rho formula.terms found))
        support_eq

/-- The replay invariant inside one selected source-term block. -/
theorem CanonicalBlockTrace.replayIndices_satisfyingAssignment
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {term : Term n}
    {rho : PartialAssignment n}
    {indices : List (Fin n)}
    {steps : List (DecisionTree.PathStep n)}
    (trace : DNF.CanonicalBlockTrace formula term rho indices steps)
    (bounded : formula.WidthAtMost widthBound)
    (termBound : term.width ≤ widthBound)
    (support_eq : liveSupport term rho = indices) :
    Switching.replayIndices formula
        (rho.refine
          (trace.satisfyingAssignment (widthBound := widthBound)))
        (some term) (trace.adviceList (widthBound := widthBound)) =
      DecisionTree.PathStep.indices steps :=
  match trace with
  | .nil _ index rest => rfl
  | .takeMore (rho := rho) (index := index) (next := next)
      (rest := rest) (value := value) tail => by
      have indexData := (mem_liveSupport term rho index).1 (by
        rw [support_eq]
        simp)
      have decoded := term.getElem?_sourcePosition_of_mem_support
        index termBound indexData.1
      have stateEqual := PartialAssignment.fix_refine_refine_fix
        rho (tail.satisfyingAssignment (widthBound := widthBound))
        index value (term.satisfyingValue index) indexData.2
      have tailSupport :
          liveSupport term
              (rho.refine (PartialAssignment.fix index value)) =
            next :: rest :=
        liveSupport_refine_fix_eq_tail term rho index (next :: rest)
          value support_eq
      have tailReplay := tail.replayIndices_satisfyingAssignment
        bounded termBound tailSupport
      rw [CanonicalBlockTrace.satisfyingAssignment_takeMore,
        CanonicalBlockTrace.adviceList_takeMore]
      simp only [Switching.replayIndices, Switching.selectTerm]
      rw [decoded]
      simp only [Bool.false_eq_true, ite_false]
      rw [Switching.QueryAdvice.decodeValue_mk_xor]
      rw [stateEqual]
      simpa [DecisionTree.PathStep.indices] using
        congrArg (List.cons index) tailReplay
  | .takeLast (rho := rho) (index := index) (value := value) tail => by
      have indexData := (mem_liveSupport term rho index).1 (by
        rw [support_eq]
        simp)
      have decoded := term.getElem?_sourcePosition_of_mem_support
        index termBound indexData.1
      have stateEqual := PartialAssignment.fix_refine_refine_fix
        rho (tail.satisfyingAssignment (widthBound := widthBound))
        index value (term.satisfyingValue index) indexData.2
      have tailReplay := tail.replayIndices_satisfyingAssignment bounded
      rw [CanonicalBlockTrace.satisfyingAssignment_takeLast,
        CanonicalBlockTrace.adviceList_takeLast]
      simp only [Switching.replayIndices, Switching.selectTerm]
      rw [decoded]
      simp only [ite_true]
      rw [Switching.QueryAdvice.decodeValue_mk_xor]
      rw [stateEqual]
      simpa [DecisionTree.PathStep.indices] using
        congrArg (List.cons index) tailReplay

end

/-- A traced satisfying assignment fixes exactly the prescribed canonical
path length. -/
theorem CanonicalPath.satisfyingAssignment_fixedCount
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {pathLength : Nat}
    (path : DNF.CanonicalPath formula rho pathLength)
    (trace : DNF.CanonicalTrace formula rho path.steps) :
    (trace.satisfyingAssignment (widthBound := widthBound)).fixedCount =
      pathLength := by
  calc
    (trace.satisfyingAssignment (widthBound := widthBound)).fixedCount =
        (DecisionTree.PathStep.assignment path.steps).fixedCount := by
      unfold PartialAssignment.fixedCount
      rw [trace.satisfyingAssignment_fixedVariables]
    _ = pathLength := path.assignment_fixedCount

/-- A traced satisfying assignment fixes only variables live before the path
began. -/
theorem CanonicalPath.satisfyingAssignment_fixesOnlyLive
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {pathLength : Nat}
    (path : DNF.CanonicalPath formula rho pathLength)
    (trace : DNF.CanonicalTrace formula rho path.steps) :
    (trace.satisfyingAssignment
        (widthBound := widthBound)).fixedVariables ⊆ rho.liveVariables := by
  rw [trace.satisfyingAssignment_fixedVariables]
  exact path.assignment_fixesOnlyLive

/-- The explicit replay-and-clear decoder is a left inverse of every valid
canonical trace encoding. -/
theorem CanonicalPath.decode_satisfyingEncoding
    {widthBound : Nat}
    [NeZero widthBound]
    {formula : DNF n}
    {rho : PartialAssignment n}
    {pathLength : Nat}
    (path : DNF.CanonicalPath formula rho pathLength)
    (trace : DNF.CanonicalTrace formula rho path.steps)
    (bounded : formula.WidthAtMost widthBound) :
    Switching.decode formula
        (rho.refine
          (trace.satisfyingAssignment (widthBound := widthBound)),
          trace.advice (widthBound := widthBound) path.length_steps) =
      rho := by
  unfold Switching.decode
  rw [trace.ofFn_advice]
  rw [trace.replayIndices_satisfyingAssignment bounded]
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
