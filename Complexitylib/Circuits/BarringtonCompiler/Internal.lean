/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BarringtonCompiler.Defs
public import Complexitylib.Circuits.BarringtonLength
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# An executable Barrington compiler -- proof internals
-/


public section

open scoped commutatorElement
open Equiv

set_option maxRecDepth 100000

namespace Complexity

theorem mem_allPermutationsFin_internal {n : ℕ} (permutation : Perm (Fin n)) :
    permutation ∈ allPermutationsFin n := by
  induction n with
  | zero =>
      have hpermutation : permutation = 1 := Subsingleton.elim _ _
      simp [allPermutationsFin, hpermutation]
  | succ n ih =>
      simp only [allPermutationsFin, List.mem_flatMap, List.mem_map]
      refine ⟨(Equiv.Perm.decomposeFin permutation).1, by simp,
        (Equiv.Perm.decomposeFin permutation).2, ih _, ?_⟩
      simp

theorem firstConjugator5_spec_internal
    (source target : Perm (Fin 5))
    (hexists : ∃ g, g * source * g⁻¹ = target) :
    firstConjugator5 source target * source *
      (firstConjugator5 source target)⁻¹ = target := by
  unfold firstConjugator5
  generalize hfind :
    (allPermutationsFin 5).find? (isConjugator5 source target) = found
  cases found with
  | none =>
      exfalso
      obtain ⟨g, hg⟩ := hexists
      have hsome :
          ((allPermutationsFin 5).find?
            (isConjugator5 source target)).isSome :=
        List.find?_isSome.mpr ⟨g, mem_allPermutationsFin_internal g, by
          simp [isConjugator5, hg]⟩
      simp [hfind] at hsome
  | some g =>
      simp only [Option.getD_some]
      have hg := List.find?_some hfind
      simpa only [isConjugator5, decide_eq_true_eq] using hg

theorem barringtonLeftBase_spec_internal :
    barringtonLeftBase.IsCycle ∧ orderOf barringtonLeftBase = 5 := by
  apply isCycle_orderOf_five_of_pow
  · decide
  · decide

theorem barringtonRightBase_spec_internal :
    barringtonRightBase.IsCycle ∧ orderOf barringtonRightBase = 5 := by
  apply isCycle_orderOf_five_of_pow
  · decide
  · decide

theorem barringtonTargetBase_spec_internal :
    barringtonTargetBase.IsCycle ∧ orderOf barringtonTargetBase = 5 := by
  apply isCycle_orderOf_five_of_pow
  · decide
  · decide

private theorem cycleType_five {cycle : Perm (Fin 5)}
    (hcycle : cycle.IsCycle) (horder : orderOf cycle = 5) :
    cycle.cycleType = {5} := by
  have hsupport : cycle.support.card = 5 := by
    rw [← hcycle.orderOf]
    exact horder
  rw [hcycle.cycleType, hsupport]

theorem barringtonConjugator_spec_internal
    (target : Perm (Fin 5)) (hcycle : target.IsCycle)
    (horder : orderOf target = 5) :
    barringtonConjugator target * barringtonTargetBase *
      (barringtonConjugator target)⁻¹ = target := by
  have hbase := barringtonTargetBase_spec_internal
  have hconj : IsConj barringtonTargetBase target :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr
      (by rw [cycleType_five hbase.1 hbase.2,
        cycleType_five hcycle horder])
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  exact firstConjugator5_spec_internal barringtonTargetBase target ⟨g, hg⟩

theorem barringtonLeft_spec_internal
    (target : Perm (Fin 5)) :
    (barringtonLeft target).IsCycle ∧
      orderOf (barringtonLeft target) = 5 := by
  simpa only [barringtonLeft] using
    conj_isCycle_orderOf_five barringtonLeftBase_spec_internal
      (barringtonConjugator target)

theorem barringtonRight_spec_internal
    (target : Perm (Fin 5)) :
    (barringtonRight target).IsCycle ∧
      orderOf (barringtonRight target) = 5 := by
  simpa only [barringtonRight] using
    conj_isCycle_orderOf_five barringtonRightBase_spec_internal
      (barringtonConjugator target)

theorem barrington_commutator_internal
    (target : Perm (Fin 5)) (hcycle : target.IsCycle)
    (horder : orderOf target = 5) :
    ⁅barringtonLeft target, barringtonRight target⁆ = target := by
  calc
    ⁅barringtonLeft target, barringtonRight target⁆ =
        barringtonConjugator target * barringtonTargetBase *
          (barringtonConjugator target)⁻¹ := by
      simp only [barringtonLeft, barringtonRight, barringtonTargetBase,
        commutatorElement_def]
      group
    _ = target := barringtonConjugator_spec_internal target hcycle horder

theorem BP.length_commutatorProgram_internal {w : ℕ} (p q : BP w) :
    (BP.commutatorProgram p q).length =
      2 * p.length + 2 * q.length := by
  simp only [BP.commutatorProgram, List.length_append, BP.length_inverse]
  omega

private theorem BP.forall_var_inverse_internal {w bound : ℕ}
    (program : BP w)
    (hvars : ∀ instruction ∈ program, instruction.var ≤ bound) :
    ∀ instruction ∈ BP.inverse program, instruction.var ≤ bound := by
  intro instruction hinstruction
  simp only [BP.inverse, List.mem_reverse, List.mem_map] at hinstruction
  obtain ⟨source, hsource, rfl⟩ := hinstruction
  exact hvars source hsource

private theorem BP.forall_var_postMul_internal {w bound : ℕ}
    (program : BP w) (permutation : Equiv.Perm (Fin w))
    (hvars : ∀ instruction ∈ program, instruction.var ≤ bound) :
    ∀ instruction ∈ BP.postMul program permutation,
      instruction.var ≤ bound := by
  induction program using List.reverseRecOn with
  | nil =>
      intro instruction hinstruction
      simp [BP.postMul, BPInstr.const] at hinstruction
      subst instruction
      exact Nat.zero_le bound
  | append_singleton program last ih =>
      intro instruction hinstruction
      have hnonempty : program ++ [last] ≠ [] := by simp
      simp only [BP.postMul, ite_eq_right hnonempty,
        List.modifyLast_concat, List.mem_append,
        List.mem_singleton] at hinstruction
      rcases hinstruction with hprefix | rfl
      · exact hvars instruction (List.mem_append_left _ hprefix)
      · exact hvars last (by simp)

private theorem BP.forall_var_commutatorProgram_internal
    {bound : ℕ} (left right : BP 5)
    (hleft : ∀ instruction ∈ left, instruction.var ≤ bound)
    (hright : ∀ instruction ∈ right, instruction.var ≤ bound) :
    ∀ instruction ∈ BP.commutatorProgram left right,
      instruction.var ≤ bound := by
  have hleftInverse := BP.forall_var_inverse_internal left hleft
  have hrightInverse := BP.forall_var_inverse_internal right hright
  intro instruction hinstruction
  simp only [BP.commutatorProgram, List.mem_append] at hinstruction
  rcases hinstruction with hinstruction | hinstruction
  · rcases hinstruction with hinstruction | hinstruction
    · rcases hinstruction with hinstruction | hinstruction
      · exact hleft instruction hinstruction
      · exact hright instruction hinstruction
    · exact hleftInverse instruction hinstruction
  · exact hrightInverse instruction hinstruction

theorem barringtonCompile_computes_internal (formula : BoolFormula) :
    ∀ (target : Perm (Fin 5)), target.IsCycle → orderOf target = 5 →
      BP.Computes target (barringtonCompile formula target)
        (fun assignment => BoolFormula.eval assignment formula) := by
  induction formula with
  | var i =>
      intro target hcycle horder
      simpa only [barringtonCompile, BoolFormula.eval] using
        BP.Computes_var target i
  | tru =>
      intro target hcycle horder
      simpa only [barringtonCompile, BoolFormula.eval] using
        BP.Computes_true target
  | fls =>
      intro target hcycle horder
      simpa only [barringtonCompile, BoolFormula.eval] using
        BP.Computes_false target
  | neg formula ih =>
      intro target hcycle horder
      have hinvCycle : target⁻¹.IsCycle := hcycle.inv
      have hinvOrder : orderOf target⁻¹ = 5 := by
        rw [orderOf_inv]
        exact horder
      have h := BP.Computes_not_compact
        (ih target⁻¹ hinvCycle hinvOrder)
      simpa only [barringtonCompile, BoolFormula.eval, inv_inv] using h
  | conj left right ihleft ihright =>
      intro target hcycle horder
      have hleftSpec := barringtonLeft_spec_internal target
      have hrightSpec := barringtonRight_spec_internal target
      have hleft := ihleft (barringtonLeft target)
        hleftSpec.1 hleftSpec.2
      have hright := ihright (barringtonRight target)
        hrightSpec.1 hrightSpec.2
      have h := BP.Computes_and hleft hright
      rw [barrington_commutator_internal target hcycle horder] at h
      simpa only [barringtonCompile, BP.commutatorProgram,
        BoolFormula.eval] using h
  | disj left right ihleft ihright =>
      intro target hcycle horder
      let innerTarget := target⁻¹
      let leftTarget := barringtonLeft innerTarget
      let rightTarget := barringtonRight innerTarget
      let leftProgram := BP.postMul
        (barringtonCompile left leftTarget⁻¹) leftTarget
      let rightProgram := BP.postMul
        (barringtonCompile right rightTarget⁻¹) rightTarget
      have hinnerCycle : innerTarget.IsCycle := hcycle.inv
      have hinnerOrder : orderOf innerTarget = 5 := by
        dsimp only [innerTarget]
        rw [orderOf_inv]
        exact horder
      have hleftSpec := barringtonLeft_spec_internal innerTarget
      have hrightSpec := barringtonRight_spec_internal innerTarget
      have hleftInvCycle : leftTarget⁻¹.IsCycle := hleftSpec.1.inv
      have hleftInvOrder : orderOf leftTarget⁻¹ = 5 := by
        rw [orderOf_inv]
        exact hleftSpec.2
      have hrightInvCycle : rightTarget⁻¹.IsCycle := hrightSpec.1.inv
      have hrightInvOrder : orderOf rightTarget⁻¹ = 5 := by
        rw [orderOf_inv]
        exact hrightSpec.2
      have hleftBase := ihleft leftTarget⁻¹
        hleftInvCycle hleftInvOrder
      have hrightBase := ihright rightTarget⁻¹
        hrightInvCycle hrightInvOrder
      have hleft : BP.Computes leftTarget leftProgram
          (fun assignment => !BoolFormula.eval assignment left) := by
        simpa only [leftProgram, inv_inv] using
          BP.Computes_not_compact hleftBase
      have hright : BP.Computes rightTarget rightProgram
          (fun assignment => !BoolFormula.eval assignment right) := by
        simpa only [rightProgram, inv_inv] using
          BP.Computes_not_compact hrightBase
      have hinner := BP.Computes_and hleft hright
      rw [barrington_commutator_internal innerTarget
        hinnerCycle hinnerOrder] at hinner
      have hfinal := BP.Computes_not_compact hinner
      have hfun :
          (fun assignment =>
            !((!BoolFormula.eval assignment left) &&
              (!BoolFormula.eval assignment right))) =
          (fun assignment =>
            BoolFormula.eval assignment (.disj left right)) := by
        funext assignment
        simp [BoolFormula.eval, Bool.not_and, Bool.not_not]
      rw [hfun] at hfinal
      simpa only [BP.commutatorProgram, barringtonCompile, innerTarget, leftTarget, rightTarget,
        leftProgram, rightProgram, inv_inv] using hfinal

theorem barringtonCompile_length_le_internal
    (formula : BoolFormula) (target : Perm (Fin 5)) :
    (barringtonCompile formula target).length ≤ 4 ^ formula.depth := by
  induction formula generalizing target with
  | var i =>
      simp [barringtonCompile, BoolFormula.depth]
  | tru =>
      simp [barringtonCompile, BoolFormula.depth]
  | fls =>
      simp [barringtonCompile, BoolFormula.depth]
  | neg formula ih =>
      rw [barringtonCompile, BP.length_postMul]
      apply le_trans (max_le (Nat.one_le_pow _ _ (by omega)) (ih target⁻¹))
      exact Nat.pow_le_pow_right (by omega) (by simp [BoolFormula.depth])
  | conj left right ihleft ihright =>
      rw [barringtonCompile, BP.length_commutatorProgram_internal]
      have hleft :
          (barringtonCompile left (barringtonLeft target)).length ≤
            4 ^ max left.depth right.depth :=
        le_trans (ihleft (barringtonLeft target))
          (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
      have hright :
          (barringtonCompile right (barringtonRight target)).length ≤
            4 ^ max left.depth right.depth :=
        le_trans (ihright (barringtonRight target))
          (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
      simp only [BoolFormula.depth, Nat.pow_succ]
      omega
  | disj left right ihleft ihright =>
      let innerTarget := target⁻¹
      let leftTarget := barringtonLeft innerTarget
      let rightTarget := barringtonRight innerTarget
      let leftProgram := BP.postMul
        (barringtonCompile left leftTarget⁻¹) leftTarget
      let rightProgram := BP.postMul
        (barringtonCompile right rightTarget⁻¹) rightTarget
      have hleft : leftProgram.length ≤ 4 ^ left.depth := by
        dsimp only [leftProgram]
        rw [BP.length_postMul]
        exact max_le (Nat.one_le_pow _ _ (by omega))
          (ihleft leftTarget⁻¹)
      have hright : rightProgram.length ≤ 4 ^ right.depth := by
        dsimp only [rightProgram]
        rw [BP.length_postMul]
        exact max_le (Nat.one_le_pow _ _ (by omega))
          (ihright rightTarget⁻¹)
      have hleftMax : leftProgram.length ≤
          4 ^ max left.depth right.depth :=
        le_trans hleft
          (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
      have hrightMax : rightProgram.length ≤
          4 ^ max left.depth right.depth :=
        le_trans hright
          (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
      have hcommutator :
          (BP.commutatorProgram leftProgram rightProgram).length ≤
            4 ^ (max left.depth right.depth + 1) := by
        rw [BP.length_commutatorProgram_internal, Nat.pow_succ]
        omega
      change (BP.postMul
        (BP.commutatorProgram leftProgram rightProgram) target).length ≤
          4 ^ (max left.depth right.depth + 1)
      rw [BP.length_postMul]
      exact max_le (Nat.one_le_pow _ _ (by omega)) hcommutator

/-- Internal variable-locality theorem for the executable compiler. -/
theorem barringtonCompile_var_bound_internal
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) (bound : ℕ)
    (hvars : ∀ index ∈ formula.vars, index ≤ bound) :
    ∀ instruction ∈ barringtonCompile formula target,
      instruction.var ≤ bound := by
  induction formula generalizing target with
  | var index =>
      intro instruction hinstruction
      simp only [barringtonCompile, List.mem_singleton] at hinstruction
      subst instruction
      exact hvars index (by simp [BoolFormula.vars])
  | tru =>
      intro instruction hinstruction
      simp [barringtonCompile, BPInstr.const] at hinstruction
      subst instruction
      exact Nat.zero_le bound
  | fls => simp [barringtonCompile]
  | neg formula ih =>
      exact BP.forall_var_postMul_internal _ _
        (ih target⁻¹ (by simpa only [BoolFormula.vars] using hvars))
  | conj left right ihLeft ihRight =>
      apply BP.forall_var_commutatorProgram_internal
      · apply ihLeft
        intro index hindex
        exact hvars index (Finset.mem_union_left _ hindex)
      · apply ihRight
        intro index hindex
        exact hvars index (Finset.mem_union_right _ hindex)
  | disj left right ihLeft ihRight =>
      simp only [barringtonCompile]
      apply BP.forall_var_postMul_internal
      apply BP.forall_var_commutatorProgram_internal
      · apply BP.forall_var_postMul_internal
        apply ihLeft
        intro index hindex
        exact hvars index (Finset.mem_union_left _ hindex)
      · apply BP.forall_var_postMul_internal
        apply ihRight
        intro index hindex
        exact hvars index (Finset.mem_union_right _ hindex)

end Complexity
