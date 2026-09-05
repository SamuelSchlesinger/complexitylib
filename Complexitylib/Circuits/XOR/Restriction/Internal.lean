/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DecisionTree.Finite
public import Complexitylib.Circuits.XOR.Restriction.Defs
public import Complexitylib.Circuits.XOR

/-!
# Parity on a finite support -- proof internals
-/


public section

namespace Complexity
namespace Schnorr

theorem xorOn_empty_internal (input : BitString N) :
    xorOn ∅ input = false := by
  rfl

theorem xorOn_insert_internal (support : Finset (Fin N))
    (index : Fin N) (hindex : index ∉ support)
    (input : BitString N) :
    xorOn (insert index support) input =
      xorOp (input index) (xorOn support input) := by
  exact Finset.fold_insert hindex

theorem xorOn_update_of_not_mem_internal
    (support : Finset (Fin N)) (index : Fin N)
    (hindex : index ∉ support) (value : Bool)
    (input : BitString N) :
    xorOn support (Function.update input index value) =
      xorOn support input := by
  unfold xorOn
  apply Finset.fold_congr
  intro queried hqueried
  have hne : queried ≠ index := by
    intro heq
    subst queried
    exact hindex hqueried
  simp [Function.update, hne]

theorem xorOn_update_false_eq_erase_internal
    (support : Finset (Fin N)) (index : Fin N)
    (input : BitString N) :
    xorOn support (Function.update input index false) =
      xorOn (support.erase index) input := by
  by_cases hindex : index ∈ support
  · have hnot : index ∉ support.erase index := by simp
    calc
      xorOn support (Function.update input index false) =
          xorOn (insert index (support.erase index))
            (Function.update input index false) := by
              rw [Finset.insert_erase hindex]
      _ = xorOp false (xorOn (support.erase index)
            (Function.update input index false)) := by
              rw [xorOn_insert_internal _ index hnot,
                Function.update_self]
      _ = xorOp false (xorOn (support.erase index) input) := by
              rw [xorOn_update_of_not_mem_internal _ index hnot]
      _ = xorOn (support.erase index) input := by
              cases xorOn (support.erase index) input <;> rfl
  · rw [xorOn_update_of_not_mem_internal support index hindex,
      Finset.erase_eq_self.mpr hindex]

theorem xorOn_flip_internal
    (support : Finset (Fin N)) (index : Fin N)
    (hindex : index ∈ support) (input : BitString N) :
    xorOn support (Function.update input index (!input index)) =
      !(xorOn support input) := by
  have hnot : index ∉ support.erase index := by simp
  calc
    xorOn support (Function.update input index (!input index)) =
        xorOn (insert index (support.erase index))
          (Function.update input index (!input index)) := by
            rw [Finset.insert_erase hindex]
    _ = xorOp (!input index) (xorOn (support.erase index)
          (Function.update input index (!input index))) := by
            rw [xorOn_insert_internal _ index hnot,
              Function.update_self]
    _ = xorOp (!input index) (xorOn (support.erase index) input) := by
            rw [xorOn_update_of_not_mem_internal _ index hnot]
    _ = !(xorOp (input index) (xorOn (support.erase index) input)) := by
            cases input index <;>
              cases xorOn (support.erase index) input <;> rfl
    _ = !(xorOn (insert index (support.erase index)) input) := by
            rw [xorOn_insert_internal _ index hnot]
    _ = !(xorOn support input) := by
            rw [Finset.insert_erase hindex]

theorem xorOn_applyTo_internal
    (support : Finset (Fin N))
    (restriction : Restriction.On N)
    (input : BitString N) :
    xorOn support (restriction.applyTo input) =
      xorOp
        (xorOn support
          (restriction.applyTo fun _ => false))
        (xorOn (support.filter fun index =>
          restriction index = none) input) := by
  induction support using Finset.induction with
  | empty => rfl
  | @insert index support hindex ih =>
      rw [xorOn_insert_internal support index hindex,
        xorOn_insert_internal support index hindex]
      cases hρ : restriction index with
      | none =>
          rw [Finset.filter_insert, ite_eq_left hρ,
            xorOn_insert_internal _ index (by simp [hindex])]
          simp only [Restriction.On.applyTo,
            hρ, Option.getD_none, ih]
          cases xorOn support
              (restriction.applyTo fun _ => false) <;>
            cases xorOn (support.filter fun queried =>
              restriction queried = none) input <;>
            cases input index <;> rfl
      | some value =>
          rw [Finset.filter_insert,
            ite_eq_right (by simp [hρ])]
          simp only [Restriction.On.applyTo,
            hρ, Option.getD_some, ih]
          cases value <;>
            cases xorOn support
              (restriction.applyTo fun _ => false) <;>
            cases xorOn (support.filter fun queried =>
              restriction queried = none) input <;> rfl

private theorem xorOn_false_internal (support : Finset (Fin N)) :
    xorOn support (fun _ => false) = false := by
  induction support using Finset.induction with
  | empty => rfl
  | insert index support hindex ih =>
      rw [xorOn_insert_internal support index hindex]
      simpa [xorOp] using ih

private theorem xorBool_false_internal (N : ℕ) :
    xorBool N (fun _ => false) = false := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simp only [xorBool]
      simpa using ih

theorem xorOn_univ_eq_xorBool_internal (input : BitString N) :
    xorOn Finset.univ input = xorBool N input := by
  generalize hcount :
    (Finset.univ.filter fun index => input index = true).card =
      count
  induction count using Nat.strong_induction_on generalizing input with
  | h count ih =>
      by_cases hzero : count = 0
      · have hfalse : input = (fun _ => false) := by
          funext index
          cases hvalue : input index
          · rfl
          · have hmem : index ∈
                (Finset.univ.filter fun queried =>
                  input queried = true) := by
              simp [hvalue]
            have hpositive :
                0 < (Finset.univ.filter fun queried =>
                  input queried = true).card :=
              Finset.card_pos.mpr ⟨index, hmem⟩
            omega
        subst input
        rw [xorOn_false_internal, xorBool_false_internal]
      · have hpositive :
            0 < (Finset.univ.filter fun index =>
              input index = true).card := by
          omega
        obtain ⟨index, hindex⟩ :=
          Finset.card_pos.mp hpositive
        have htrue : input index = true :=
          (Finset.mem_filter.mp hindex).2
        let reduced : BitString N :=
          Function.update input index false
        have hfilter :
            (Finset.univ.filter fun queried =>
                reduced queried = true) =
              (Finset.univ.filter fun queried =>
                input queried = true).erase index := by
          ext queried
          by_cases heq : queried = index
          · subst queried
            simp [reduced, Function.update, htrue]
          · simp [reduced, Function.update, heq]
        have hreducedLt :
            (Finset.univ.filter fun queried =>
              reduced queried = true).card < count := by
          rw [hfilter, Finset.card_erase_of_mem hindex, hcount]
          omega
        have ihReduced := ih _ hreducedLt reduced rfl
        have hrestore :
            Function.update reduced index (!reduced index) =
              input := by
          funext queried
          by_cases heq : queried = index
          · subst queried
            simp [reduced, htrue]
          · simp [reduced, Function.update, heq]
        calc
          xorOn Finset.univ input =
              xorOn Finset.univ
                (Function.update reduced index
                  (!reduced index)) :=
            congrArg (xorOn Finset.univ) hrestore.symm
          _ = !(xorOn Finset.univ reduced) :=
            xorOn_flip_internal Finset.univ index
              (by simp) reduced
          _ = !(xorBool N reduced) :=
            congrArg (fun value => !value) ihReduced
          _ = xorBool N
              (Function.update reduced index (!reduced index)) :=
            (xorBool_flip N reduced index).symm
          _ = xorBool N input :=
            congrArg (xorBool N) hrestore

theorem xorBool_applyTo_internal
    (restriction : Restriction.On N)
    (input : BitString N) :
    xorBool N (restriction.applyTo input) =
      xorOp
        (xorBool N
          (restriction.applyTo fun _ => false))
        (xorOn restriction.freeVariables input) := by
  rw [← xorOn_univ_eq_xorBool_internal,
    ← xorOn_univ_eq_xorBool_internal,
    xorOn_applyTo_internal]
  rfl

theorem card_support_le_depth_internal
    (tree : DecisionTree.On N) (support : Finset (Fin N))
    (computes : ∀ input, tree.eval input = xorOn support input) :
    support.card ≤ tree.depth := by
  induction hdepth : tree.depth using Nat.strong_induction_on
      generalizing tree support with
  | h depth ih =>
      cases tree with
      | leaf value =>
          have hempty : support = ∅ := by
            by_contra hsupport
            obtain ⟨index, hindex⟩ :=
              Finset.nonempty_iff_ne_empty.mpr hsupport
            let input : BitString N := fun _ => false
            have hflip :=
              xorOn_flip_internal support index hindex input
            rw [← computes
                (Function.update input index (!input index)),
              ← computes input] at hflip
            cases value <;>
              simp [DecisionTree.On.eval] at hflip
          subst support
          simp
      | node index ifFalse ifTrue =>
          let restriction : Restriction.On N :=
            Restriction.On.single index false
          let child : DecisionTree.On N :=
            ifFalse.restrict restriction
          have hchildComputes : ∀ input,
              child.eval input =
                xorOn (support.erase index) input := by
            intro input
            rw [DecisionTree.On.eval_restrict]
            rw [Restriction.On.applyTo_single]
            have hroot :=
              computes (Function.update input index false)
            simp only [DecisionTree.On.eval,
              Function.update_self, Bool.false_eq_true,
              ↓reduceIte] at hroot
            exact hroot.trans
              (xorOn_update_false_eq_erase_internal
                support index input)
          have hchildLe : child.depth ≤ ifFalse.depth :=
            DecisionTree.On.depth_restrict_le restriction ifFalse
          have hchildLt : child.depth < depth := by
            simp only [DecisionTree.On.depth] at hdepth
            omega
          have ihbound :
              (support.erase index).card ≤ child.depth :=
            ih child.depth hchildLt child (support.erase index)
              hchildComputes rfl
          have hcard :
              support.card ≤ (support.erase index).card + 1 := by
            by_cases hindex : index ∈ support
            · have hpositive : 0 < support.card :=
                Finset.card_pos.mpr ⟨index, hindex⟩
              rw [Finset.card_erase_of_mem hindex]
              omega
            · rw [Finset.erase_eq_self.mpr hindex]
              omega
          simp only [DecisionTree.On.depth] at hdepth
          omega

theorem card_support_le_depth_offset_internal
    (tree : DecisionTree.On N)
    (support : Finset (Fin N)) (offset : Bool)
    (computes : ∀ input,
      tree.eval input =
        xorOp offset (xorOn support input)) :
    support.card ≤ tree.depth := by
  cases offset with
  | false =>
      apply card_support_le_depth_internal tree support
      intro input
      simpa [xorOp] using computes input
  | true =>
      rw [← DecisionTree.On.depth_neg]
      apply card_support_le_depth_internal tree.neg support
      intro input
      rw [DecisionTree.On.eval_neg, computes]
      cases xorOn support input <;> rfl

theorem freeVariables_card_le_depth_of_restricted_xor_internal
    (tree : DecisionTree.On N)
    (restriction : Restriction.On N)
    (computes : ∀ input,
      tree.eval input =
        xorBool N (restriction.applyTo input)) :
    restriction.freeVariables.card ≤ tree.depth := by
  apply card_support_le_depth_offset_internal tree
    restriction.freeVariables
    (xorBool N
      (restriction.applyTo fun _ => false))
  intro input
  rw [computes, xorBool_applyTo_internal]

end Schnorr
end Complexity
