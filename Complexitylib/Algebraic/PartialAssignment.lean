/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Restriction
public import Mathlib.Data.Finset.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card

/-!
# Boolean partial assignments

A partial assignment records, for each named Boolean variable, either a fixed
value or a live variable. Restricted functions retain the original input
indexing: values supplied at fixed coordinates are ignored. This representation
is convenient for random restrictions and decision trees, while conversion to
`InputSubstitution` connects it to the library's existing semantic interface.

Sequential refinement is left-biased. In `rho.refine sigma`, assignments
already fixed by `rho` remain fixed, and `sigma` is consulted only at variables
left live by `rho`.
-/

@[expose] public section

namespace Algebraic

/-- A Boolean restriction on `n` named variables. `none` means that a variable
is live; `some value` fixes it to `value`. -/
abbrev PartialAssignment (n : Nat) := Fin n -> Option Bool

namespace PartialAssignment

/-- Two partial assignments are equal when they agree on every variable. -/
theorem ext
    {rho sigma : PartialAssignment n}
    (equal : forall index, rho index = sigma index) :
    rho = sigma :=
  funext equal

/-- The empty partial assignment leaves every variable live. -/
def empty : PartialAssignment n :=
  fun _ => none

/-- A total assignment fixes every variable. -/
def total (input : Fin n -> Bool) : PartialAssignment n :=
  fun index => some (input index)

/-- The partial assignment fixing exactly one variable. -/
def fix (selected : Fin n) (value : Bool) : PartialAssignment n :=
  fun index => if index = selected then some value else none

@[simp] theorem empty_apply (index : Fin n) :
    (empty : PartialAssignment n) index = none := rfl

@[simp] theorem total_apply
    (input : Fin n -> Bool)
    (index : Fin n) :
    total input index = some (input index) := rfl

@[simp] theorem fix_selected
    (selected : Fin n)
    (value : Bool) :
    fix selected value selected = some value := by
  simp [fix]

@[simp] theorem fix_other
    (selected index : Fin n)
    (value : Bool)
    (different : index ≠ selected) :
    fix selected value index = none := by
  simp [fix, different]

/-- Apply a partial assignment to a complete input. Values at fixed variables
are overwritten, while values at live variables are retained. -/
def apply
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) : Fin n -> Bool :=
  fun index => (rho index).getD (input index)

@[simp] theorem apply_of_live
    (rho : PartialAssignment n)
    (input : Fin n -> Bool)
    {index : Fin n}
    (live : rho index = none) :
    rho.apply input index = input index := by
  simp [apply, live]

@[simp] theorem apply_of_fixed
    (rho : PartialAssignment n)
    (input : Fin n -> Bool)
    {index : Fin n}
    {value : Bool}
    (fixed : rho index = some value) :
    rho.apply input index = value := by
  simp [apply, fixed]

@[simp] theorem apply_empty (input : Fin n -> Bool) :
    (empty : PartialAssignment n).apply input = input := by
  funext index
  simp [apply]

@[simp] theorem apply_total
    (fixed input : Fin n -> Bool) :
    (total fixed).apply input = fixed := by
  funext index
  simp [apply]

/-- Fixing a variable to the value it already has leaves a complete input
unchanged. -/
theorem apply_fix_eq_self
    (input : Fin n -> Bool)
    (selected : Fin n)
    (value : Bool)
    (selectedValue : input selected = value) :
    (fix selected value).apply input = input := by
  funext index
  by_cases equal : index = selected
  · subst index
    simp [apply, fix, selectedValue]
  · simp [apply, fix, equal]

/-- Refine `rho` with `sigma`, retaining every value already fixed by `rho`. -/
def refine
    (rho sigma : PartialAssignment n) : PartialAssignment n :=
  fun index =>
    match rho index with
    | some value => some value
    | none => sigma index

/-- Clear a designated finite set of coordinates, leaving every other value
unchanged. This is the inverse operation used by refinement encodings once
their newly fixed support has been reconstructed. -/
def clear
    (rho : PartialAssignment n)
    (coordinates : Finset (Fin n)) : PartialAssignment n :=
  fun index => if index ∈ coordinates then none else rho index

@[simp] theorem clear_of_mem
    (rho : PartialAssignment n)
    (coordinates : Finset (Fin n))
    {index : Fin n}
    (present : index ∈ coordinates) :
    rho.clear coordinates index = none := by
  simp [clear, present]

@[simp] theorem clear_of_not_mem
    (rho : PartialAssignment n)
    (coordinates : Finset (Fin n))
    {index : Fin n}
    (absent : index ∉ coordinates) :
    rho.clear coordinates index = rho index := by
  simp [clear, absent]

@[simp] theorem empty_refine (rho : PartialAssignment n) :
    empty.refine rho = rho := by
  apply ext
  intro index
  rfl

@[simp] theorem refine_empty (rho : PartialAssignment n) :
    rho.refine empty = rho := by
  apply ext
  intro index
  cases fixed : rho index <;> simp [refine, fixed]

/-- Applying a sequential refinement is function composition on inputs. -/
theorem apply_refine
    (rho sigma : PartialAssignment n)
    (input : Fin n -> Bool) :
    (rho.refine sigma).apply input = rho.apply (sigma.apply input) := by
  funext index
  cases fixed : rho index with
  | none => simp [refine, apply, fixed]
  | some value => simp [refine, apply, fixed]

/-- Sequential refinement is associative. -/
theorem refine_assoc
    (rho sigma tau : PartialAssignment n) :
    (rho.refine sigma).refine tau = rho.refine (sigma.refine tau) := by
  apply ext
  intro index
  cases first : rho index <;>
    cases second : sigma index <;>
      simp [refine, first, second]

/-- Replacing the freshly assigned head coordinate by a path value commutes
with retaining the rest of a refinement. The selected coordinate must be live
in the original restriction. -/
theorem fix_refine_refine_fix
    (rho tail : PartialAssignment n)
    (selected : Fin n)
    (pathValue satisfyingValue : Bool)
    (live : rho selected = none) :
    (fix selected pathValue).refine
        (rho.refine ((fix selected satisfyingValue).refine tail)) =
      (rho.refine (fix selected pathValue)).refine tail := by
  apply ext
  intro index
  by_cases equal : index = selected
  · subst index
    simp [refine, fix, live]
  · cases fixed : rho index <;>
      simp [refine, fix, equal, fixed]

/-- View a partial assignment as a semantic input substitution on the same
named variables. -/
def toInputSubstitution
    (rho : PartialAssignment n) : InputSubstitution Bool n n :=
  fun index input => rho.apply input index

@[simp] theorem toInputSubstitution_apply
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    rho.toInputSubstitution.apply input = rho.apply input := rfl

@[simp] theorem toInputSubstitution_empty :
    (empty : PartialAssignment n).toInputSubstitution =
      (InputSubstitution.id : InputSubstitution Bool n n) := by
  funext index input
  simp [toInputSubstitution, InputSubstitution.id, apply]

/-- Conversion to input substitutions preserves sequential composition. -/
theorem toInputSubstitution_refine
    (rho sigma : PartialAssignment n) :
    (rho.refine sigma).toInputSubstitution =
      rho.toInputSubstitution.comp sigma.toInputSubstitution := by
  funext index input
  exact congrFun (apply_refine rho sigma input) index

/-- The finite set of variables left live by a partial assignment. -/
def liveVariables (rho : PartialAssignment n) : Finset (Fin n) :=
  Finset.univ.filter fun index => rho index = none

@[simp] theorem mem_liveVariables
    (rho : PartialAssignment n)
    (index : Fin n) :
    index ∈ rho.liveVariables ↔ rho index = none := by
  simp [liveVariables]

/-- The number of variables left live by a partial assignment. -/
def liveCount (rho : PartialAssignment n) : Nat :=
  rho.liveVariables.card

/-- The increasing bijection from a compact input namespace to the variables
left live by a partial assignment. -/
noncomputable def liveOrderIso (rho : PartialAssignment n) :
    Fin rho.liveCount ≃o {index : Fin n // index ∈ rho.liveVariables} :=
  rho.liveVariables.orderIsoOfFin rfl

/-- The original input coordinate represented by a compact live-input index. -/
noncomputable def liveVariable
    (rho : PartialAssignment n) : Fin rho.liveCount → Fin n :=
  fun index => rho.liveOrderIso index

theorem liveVariable_mem
    (rho : PartialAssignment n)
    (index : Fin rho.liveCount) :
    rho.liveVariable index ∈ rho.liveVariables :=
  (rho.liveOrderIso index).property

theorem liveVariable_isLive
    (rho : PartialAssignment n)
    (index : Fin rho.liveCount) :
    rho (rho.liveVariable index) = none :=
  (mem_liveVariables rho (rho.liveVariable index)).1
    (liveVariable_mem rho index)

/-- The compact index of an original coordinate known to be live. -/
noncomputable def liveIndex
    (rho : PartialAssignment n)
    (index : Fin n)
    (live : rho index = none) : Fin rho.liveCount :=
  rho.liveOrderIso.symm
    ⟨index, (mem_liveVariables rho index).2 live⟩

@[simp] theorem liveVariable_liveIndex
    (rho : PartialAssignment n)
    (index : Fin n)
    (live : rho index = none) :
    rho.liveVariable (rho.liveIndex index live) = index := by
  change ↑(rho.liveOrderIso
    (rho.liveOrderIso.symm
      ⟨index, (mem_liveVariables rho index).2 live⟩)) = index
  simp

@[simp] theorem liveIndex_liveVariable
    (rho : PartialAssignment n)
    (index : Fin rho.liveCount) :
    rho.liveIndex (rho.liveVariable index)
        (rho.liveVariable_isLive index) = index := by
  have represented :
      (⟨rho.liveVariable index,
          (mem_liveVariables rho (rho.liveVariable index)).2
            (rho.liveVariable_isLive index)⟩ :
        {source : Fin n // source ∈ rho.liveVariables}) =
        rho.liveOrderIso index := by
    apply Subtype.ext
    rfl
  change rho.liveOrderIso.symm _ = index
  rw [represented, rho.liveOrderIso.symm_apply_apply]

/-- Read a complete input only at the coordinates left live by `rho`. -/
noncomputable def projectLive
    (rho : PartialAssignment n)
    (input : Fin n → Bool) : Fin rho.liveCount → Bool :=
  fun index => input (rho.liveVariable index)

/-- Express every original input as either a fixed Boolean or one of the
compactly reindexed live inputs. -/
noncomputable def toLiveInputSubstitution
    (rho : PartialAssignment n) :
    InputSubstitution Bool n rho.liveCount :=
  fun index input =>
    if live : rho index = none then
        input (rho.liveIndex index live)
    else (rho index).getD false

@[simp] theorem toLiveInputSubstitution_of_fixed
    (rho : PartialAssignment n)
    (input : Fin rho.liveCount → Bool)
    {index : Fin n}
    {value : Bool}
    (fixed : rho index = some value) :
    rho.toLiveInputSubstitution.apply input index = value := by
  simp [toLiveInputSubstitution, InputSubstitution.apply, fixed]

@[simp] theorem toLiveInputSubstitution_liveVariable
    (rho : PartialAssignment n)
    (input : Fin rho.liveCount → Bool)
    (index : Fin rho.liveCount) :
    rho.toLiveInputSubstitution.apply input (rho.liveVariable index) =
      input index := by
  have live := liveVariable_isLive rho index
  simp only [InputSubstitution.apply, toLiveInputSubstitution, dite_eq_left live]
  exact congrArg input (liveIndex_liveVariable rho index)

/-- Projecting a complete input to its live coordinates and then restoring
fixed coordinates is exactly ordinary application of the restriction. -/
theorem toLiveInputSubstitution_projectLive
    (rho : PartialAssignment n)
    (input : Fin n → Bool) :
    rho.toLiveInputSubstitution.apply (rho.projectLive input) =
      rho.apply input := by
  funext index
  cases fixed : rho index with
  | none =>
      simp only [InputSubstitution.apply, toLiveInputSubstitution,
        dite_eq_left fixed, projectLive]
      rw [apply_of_live rho input fixed]
      exact congrArg input (liveVariable_liveIndex rho index fixed)
  | some value =>
      simp [toLiveInputSubstitution, InputSubstitution.apply, fixed,
        apply_of_fixed]

/-- Compact live inputs are recovered after restoring the original input
namespace. -/
@[simp] theorem projectLive_toLiveInputSubstitution
    (rho : PartialAssignment n)
    (input : Fin rho.liveCount → Bool) :
    rho.projectLive (rho.toLiveInputSubstitution.apply input) = input := by
  funext index
  exact toLiveInputSubstitution_liveVariable rho input index

/-- The finite set of variables fixed by a partial assignment. -/
def fixedVariables (rho : PartialAssignment n) : Finset (Fin n) :=
  Finset.univ.filter fun index => rho index ≠ none

@[simp] theorem mem_fixedVariables
    (rho : PartialAssignment n)
    (index : Fin n) :
    index ∈ rho.fixedVariables ↔ rho index ≠ none := by
  simp [fixedVariables]

/-- The number of variables fixed by a partial assignment. -/
def fixedCount (rho : PartialAssignment n) : Nat :=
  rho.fixedVariables.card

@[simp] theorem liveVariables_empty :
    (empty : PartialAssignment n).liveVariables = Finset.univ := by
  apply Finset.ext
  intro index
  simp

@[simp] theorem liveCount_empty :
    (empty : PartialAssignment n).liveCount = n := by
  simp [liveCount]

@[simp] theorem fixedVariables_empty :
    (empty : PartialAssignment n).fixedVariables = {} := by
  apply Finset.ext
  intro index
  simp

@[simp] theorem fixedCount_empty :
    (empty : PartialAssignment n).fixedCount = 0 := by
  simp [fixedCount]

@[simp] theorem liveVariables_total (input : Fin n -> Bool) :
    (total input).liveVariables = {} := by
  apply Finset.ext
  intro index
  simp

@[simp] theorem liveCount_total (input : Fin n -> Bool) :
    (total input).liveCount = 0 := by
  simp [liveCount]

@[simp] theorem fixedVariables_total (input : Fin n -> Bool) :
    (total input).fixedVariables = Finset.univ := by
  apply Finset.ext
  intro index
  simp

@[simp] theorem fixedCount_total (input : Fin n -> Bool) :
    (total input).fixedCount = n := by
  simp [fixedCount]

/-- Every variable is either live or fixed, but not both. -/
theorem liveVariables_union_fixedVariables
    (rho : PartialAssignment n) :
    rho.liveVariables ∪ rho.fixedVariables = Finset.univ := by
  apply Finset.ext
  intro index
  cases fixed : rho index <;> simp [fixed]

/-- The live and fixed variable sets are disjoint. -/
theorem disjoint_liveVariables_fixedVariables
    (rho : PartialAssignment n) :
    Disjoint rho.liveVariables rho.fixedVariables := by
  rw [Finset.disjoint_left]
  intro index live fixed
  exact (mem_fixedVariables rho index).1 fixed
    ((mem_liveVariables rho index).1 live)

/-- Live and fixed variables partition the input coordinates exactly. -/
theorem liveCount_add_fixedCount
    (rho : PartialAssignment n) :
    rho.liveCount + rho.fixedCount = n := by
  rw [liveCount, fixedCount,
    ← Finset.card_union_of_disjoint
      (disjoint_liveVariables_fixedVariables rho),
    liveVariables_union_fixedVariables, Finset.card_fin]

/-- Fixing one variable removes exactly that variable from the live set. -/
theorem liveVariables_fix
    (selected : Fin n)
    (value : Bool) :
    (fix selected value).liveVariables = Finset.univ.erase selected := by
  apply Finset.ext
  intro index
  simp [liveVariables, fix]

/-- A one-variable assignment fixes exactly its selected coordinate. -/
theorem fixedVariables_fix
    (selected : Fin n)
    (value : Bool) :
    (fix selected value).fixedVariables = {selected} := by
  apply Finset.ext
  intro index
  simp [fixedVariables, fix]

/-- The live variables after sequential refinement are the variables left live
by both constituent partial assignments. -/
theorem liveVariables_refine
    (rho sigma : PartialAssignment n) :
    (rho.refine sigma).liveVariables =
      rho.liveVariables ∩ sigma.liveVariables := by
  apply Finset.ext
  intro index
  simp only [mem_liveVariables, Finset.mem_inter]
  cases fixed : rho index with
  | none => simp [refine, fixed]
  | some value => simp [refine, fixed]

/-- The variables fixed by a sequential refinement are exactly those fixed by
either constituent assignment. -/
theorem fixedVariables_refine
    (rho sigma : PartialAssignment n) :
    (rho.refine sigma).fixedVariables =
      rho.fixedVariables ∪ sigma.fixedVariables := by
  apply Finset.ext
  intro index
  simp only [mem_fixedVariables, Finset.mem_union]
  cases fixed : rho index with
  | none => simp [refine, fixed]
  | some value => simp [refine, fixed]

/-- Sequential refinement cannot increase the number of live variables. -/
theorem liveCount_refine_le_left
    (rho sigma : PartialAssignment n) :
    (rho.refine sigma).liveCount ≤ rho.liveCount := by
  rw [liveCount, liveVariables_refine]
  exact Finset.card_le_card Finset.inter_subset_left

/-- Refining by a one-variable assignment removes exactly that variable from
the live set. If it was already fixed, the set is unchanged. -/
theorem liveVariables_refine_fix
    (rho : PartialAssignment n)
    (selected : Fin n)
    (value : Bool) :
    (rho.refine (fix selected value)).liveVariables =
      rho.liveVariables.erase selected := by
  rw [liveVariables_refine, liveVariables_fix, Finset.inter_erase]
  simp

/-- Fixing a currently live variable strictly decreases the live count. -/
theorem liveCount_refine_fix_lt_of_live
    (rho : PartialAssignment n)
    (selected : Fin n)
    (value : Bool)
    (live : rho selected = none) :
    (rho.refine (fix selected value)).liveCount < rho.liveCount := by
  rw [liveCount, liveVariables_refine_fix]
  exact Finset.card_erase_lt_of_mem
    ((mem_liveVariables rho selected).2 live)

/-- If the second assignment fixes only variables left live by the first,
their fixed-variable counts add under refinement. -/
theorem fixedCount_refine_eq_add
    (rho sigma : PartialAssignment n)
    (newFixes : sigma.fixedVariables ⊆ rho.liveVariables) :
    (rho.refine sigma).fixedCount = rho.fixedCount + sigma.fixedCount := by
  have disjoint : Disjoint rho.fixedVariables sigma.fixedVariables := by
    rw [Finset.disjoint_left]
    intro index fixedByRho fixedBySigma
    have liveByRho := newFixes fixedBySigma
    exact (Finset.disjoint_left.mp
      (disjoint_liveVariables_fixedVariables rho)) liveByRho fixedByRho
  rw [fixedCount, fixedVariables_refine,
    Finset.card_union_of_disjoint disjoint, fixedCount, fixedCount]

/-- Clearing exactly the support added by a refinement recovers the original
restriction, provided the refinement fixed only previously live variables. -/
theorem clear_refine_fixedVariables
    (rho extension : PartialAssignment n)
    (newFixes : extension.fixedVariables ⊆ rho.liveVariables) :
    (rho.refine extension).clear extension.fixedVariables = rho := by
  apply ext
  intro index
  by_cases fixed : extension index = none
  · have absent : index ∉ extension.fixedVariables := by
      simpa using fixed
    cases source : rho index <;>
      simp [clear, absent, refine, fixed, source]
  · have present : index ∈ extension.fixedVariables :=
      (mem_fixedVariables extension index).2 fixed
    have live : rho index = none :=
      (mem_liveVariables rho index).1 (newFixes present)
    simp [clear, present, live]

/-- Under a refinement that fixes only live variables, the decrease in live
count is exactly the second assignment's fixed count. -/
theorem liveCount_refine_add_fixedCount_eq
    (rho sigma : PartialAssignment n)
    (newFixes : sigma.fixedVariables ⊆ rho.liveVariables) :
    (rho.refine sigma).liveCount + sigma.fixedCount = rho.liveCount := by
  have refinedPartition := liveCount_add_fixedCount (rho.refine sigma)
  have sourcePartition := liveCount_add_fixedCount rho
  rw [fixedCount_refine_eq_add rho sigma newFixes] at refinedPartition
  omega

/-- Inputs that agree on every live variable become equal after applying the
partial assignment. -/
theorem apply_eq_of_agree_live
    (rho : PartialAssignment n)
    {left right : Fin n -> Bool}
    (agree : forall index, index ∈ rho.liveVariables ->
      left index = right index) :
    rho.apply left = rho.apply right := by
  funext index
  cases fixed : rho index with
  | none =>
      rw [apply_of_live rho left fixed, apply_of_live rho right fixed]
      exact agree index ((mem_liveVariables rho index).2 fixed)
  | some value =>
      rw [apply_of_fixed rho left fixed, apply_of_fixed rho right fixed]

end PartialAssignment

namespace ScalarFunction

/-- Restrict a scalar Boolean function by a partial assignment. -/
def restrict
    (function : ScalarFunction Bool n)
    (rho : PartialAssignment n) : ScalarFunction Bool n :=
  fun input => function (rho.apply input)

@[simp] theorem restrict_apply
    (function : ScalarFunction Bool n)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    function.restrict rho input = function (rho.apply input) := rfl

@[simp] theorem restrict_empty
    (function : ScalarFunction Bool n) :
    function.restrict PartialAssignment.empty = function := rfl

/-- Restricting twice agrees with restriction by sequential refinement. -/
theorem restrict_refine
    (function : ScalarFunction Bool n)
    (rho sigma : PartialAssignment n) :
    (function.restrict rho).restrict sigma =
      function.restrict (rho.refine sigma) := by
  funext input
  rw [restrict_apply, restrict_apply, restrict_apply,
    PartialAssignment.apply_refine]

/-- A restricted scalar function depends only on variables left live. -/
theorem restrict_dependsOnlyOn_live
    (function : ScalarFunction Bool n)
    (rho : PartialAssignment n) :
    DependsOnlyOn (function.restrict rho) rho.liveVariables := by
  intro left right agree
  exact congrArg function (rho.apply_eq_of_agree_live agree)

end ScalarFunction

namespace Target

/-- Restrict every output of a Boolean target by a partial assignment. -/
def restrict
    (target : Target Bool n m)
    (rho : PartialAssignment n) : Target Bool n m :=
  target.substitute rho.toInputSubstitution

@[simp] theorem restrict_apply
    (target : Target Bool n m)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    target.restrict rho input = target (rho.apply input) := rfl

@[simp] theorem restrict_empty
    (target : Target Bool n m) :
    target.restrict PartialAssignment.empty = target := rfl

/-- Restricting a target twice agrees with sequential refinement. -/
theorem restrict_refine
    (target : Target Bool n m)
    (rho sigma : PartialAssignment n) :
    (target.restrict rho).restrict sigma =
      target.restrict (rho.refine sigma) := by
  funext input
  rw [restrict_apply, restrict_apply, restrict_apply,
    PartialAssignment.apply_refine]

/-- A restricted target depends only on variables left live. -/
theorem restrict_dependsOnlyOn_live
    (target : Target Bool n m)
    (rho : PartialAssignment n) :
    DependsOnlyOn (target.restrict rho) rho.liveVariables := by
  intro left right agree
  change target (rho.apply left) = target (rho.apply right)
  exact congrArg target (rho.apply_eq_of_agree_live agree)

end Target

end Algebraic
