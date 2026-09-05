/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BarringtonConverse.Defs

/-!
# The converse direction of Barrington's theorem -- proof internals

This file proves correctness and logarithmic depth for balanced branching-program
evaluation, then lifts that construction to polynomial-length families.
-/


public section

open Equiv

namespace Complexity

namespace BoolFormula

private theorem eval_disjoin (α : ℕ → Bool) :
    ∀ fs, eval α (disjoin fs) = fs.any (fun φ => eval α φ)
  | [] => rfl
  | _ :: _ => by simp [disjoin, eval, eval_disjoin]

private theorem eval_disjoin_eq_true (α : ℕ → Bool) (fs : List BoolFormula) :
    eval α (disjoin fs) = true ↔ ∃ φ ∈ fs, eval α φ = true := by
  rw [eval_disjoin, List.any_eq_true]

private theorem eval_conj_eq_true (α : ℕ → Bool) (φ ψ : BoolFormula) :
    eval α (.conj φ ψ) = true ↔ eval α φ = true ∧ eval α ψ = true := by
  simp [eval]

private theorem depth_disjoin_le {fs : List BoolFormula} {d : ℕ}
    (h : ∀ φ ∈ fs, depth φ ≤ d) :
    depth (disjoin fs) ≤ d + fs.length := by
  induction fs with
  | nil => simp [disjoin, depth]
  | cons φ fs ih =>
    simp only [disjoin, depth, List.length_cons]
    have hφ := h φ List.mem_cons_self
    have hfs : ∀ ψ ∈ fs, depth ψ ≤ d :=
      fun ψ hψ => h ψ (List.mem_cons_of_mem φ hψ)
    have hi := ih hfs
    omega

private theorem vars_disjoin_lt {n : ℕ} {fs : List BoolFormula}
    (h : ∀ formula ∈ fs, ∀ index ∈ formula.vars, index < n) :
    ∀ index ∈ (disjoin fs).vars, index < n := by
  induction fs with
  | nil => simp [disjoin, vars]
  | cons formula formulas ih =>
      intro index hindex
      simp only [disjoin, vars, Finset.mem_union] at hindex
      rcases hindex with hformula | hformulas
      · exact h formula List.mem_cons_self index hformula
      · exact ih (fun other hother =>
          h other (List.mem_cons_of_mem formula hother)) index hformulas

end BoolFormula

namespace BPInstr

private theorem eval_reachesFormula_internal {w : ℕ} (α : ℕ → Bool)
    (ins : BPInstr w) (x y : Fin w) :
    BoolFormula.eval α (reachesFormula ins x y) = true ↔
      BPInstr.eval α ins x = y := by
  simp only [reachesFormula, BPInstr.eval]
  split_ifs <;> simp_all [BoolFormula.eval]

private theorem depth_reachesFormula_le_internal {w : ℕ}
    (ins : BPInstr w) (x y : Fin w) :
    (reachesFormula ins x y).depth ≤ 1 := by
  simp only [reachesFormula]
  split_ifs <;> simp [BoolFormula.depth]

private theorem vars_reachesFormula_lt_internal {w n : ℕ}
    (ins : BPInstr w) (x y : Fin w) (hvar : ins.var < n) :
    ∀ index ∈ (ins.reachesFormula x y).vars, index < n := by
  intro index hindex
  simp only [reachesFormula] at hindex
  split_ifs at hindex <;> simp_all [BoolFormula.vars]

end BPInstr

namespace BP

theorem eval_reachesFormula_internal {w : ℕ} (α : ℕ → Bool) :
    ∀ (d : ℕ) (p : BP w) (x y : Fin w), p.length ≤ 2 ^ d →
      (BoolFormula.eval α (reachesFormula d p x y) = true ↔ BP.eval α p x = y) := by
  intro d
  induction d with
  | zero =>
    intro p x y hp
    cases p with
    | nil =>
      simp only [reachesFormula]
      split_ifs <;> simp_all [BoolFormula.eval, BP.eval]
    | cons ins tail =>
      have htail : tail = [] := by
        cases tail <;> simp_all
      subst tail
      simpa [reachesFormula, BP.eval] using BPInstr.eval_reachesFormula_internal α ins x y
  | succ d ih =>
    intro p x y hp
    have htake : (p.take (2 ^ d)).length ≤ 2 ^ d := List.length_take_le ..
    have hdrop : (p.drop (2 ^ d)).length ≤ 2 ^ d := by
      rw [List.length_drop]
      simpa [Nat.pow_succ, Nat.mul_two] using Nat.sub_le_iff_le_add.mpr hp
    rw [reachesFormula, BoolFormula.eval_disjoin_eq_true]
    simp only [List.mem_ofFn]
    constructor
    · rintro ⟨φ, ⟨z, hz⟩, hφ⟩
      subst φ
      obtain ⟨hzLeft, hzRight⟩ :=
        (BoolFormula.eval_conj_eq_true α _ _).mp hφ
      have hzLeft' := (ih _ _ _ htake).mp hzLeft
      have hzRight' := (ih _ _ _ hdrop).mp hzRight
      rw [← List.take_append_drop (2 ^ d) p, BP.eval_append,
        Equiv.Perm.mul_apply]
      rw [hzRight', hzLeft']
    · intro h
      let z := BP.eval α (p.drop (2 ^ d)) x
      refine ⟨_, ⟨z, rfl⟩,
        (BoolFormula.eval_conj_eq_true α _ _).mpr ⟨?_, ?_⟩⟩
      · apply (ih _ _ _ htake).mpr
        rw [← List.take_append_drop (2 ^ d) p, BP.eval_append,
          Equiv.Perm.mul_apply] at h
        exact h
      · exact (ih _ _ _ hdrop).mpr rfl

theorem depth_reachesFormula_le_internal {w : ℕ} :
    ∀ (d : ℕ) (p : BP w) (x y : Fin w),
      (reachesFormula d p x y).depth ≤ (w + 1) * d + 1 := by
  intro d
  induction d with
  | zero =>
    intro p x y
    cases p with
    | nil =>
      simp only [reachesFormula]
      split_ifs <;> simp [BoolFormula.depth]
    | cons ins tail =>
      simpa [reachesFormula] using
        BPInstr.depth_reachesFormula_le_internal ins x y
  | succ d ih =>
    intro p x y
    apply le_trans
      (BoolFormula.depth_disjoin_le (d := (w + 1) * d + 2) ?_)
    · simp only [List.length_ofFn]
      ring_nf
      exact le_rfl
    · intro φ hφ
      rw [List.mem_ofFn] at hφ
      obtain ⟨z, rfl⟩ := hφ
      simp only [BoolFormula.depth]
      have hLeft := ih (p.take (2 ^ d)) z y
      have hRight := ih (p.drop (2 ^ d)) x z
      omega

private theorem vars_reachesFormula_lt_internal {w n : ℕ} {p : BP w}
    (hvars : ∀ instruction ∈ p, instruction.var < n) :
    ∀ (d : ℕ) (x y : Fin w) index,
      index ∈ (reachesFormula d p x y).vars → index < n := by
  intro d
  induction d generalizing p with
  | zero =>
      intro x y index hindex
      cases p with
      | nil =>
          simp only [reachesFormula] at hindex
          split_ifs at hindex <;> simp_all [BoolFormula.vars]
      | cons instruction tail =>
          exact BPInstr.vars_reachesFormula_lt_internal instruction x y
            (hvars instruction List.mem_cons_self) index hindex
  | succ d ih =>
      intro x y index hindex
      apply BoolFormula.vars_disjoin_lt
        (fs := List.ofFn fun z : Fin w =>
          .conj (reachesFormula d (p.take (2 ^ d)) z y)
            (reachesFormula d (p.drop (2 ^ d)) x z))
      · intro formula hformula index' hindex'
        rw [List.mem_ofFn] at hformula
        obtain ⟨z, rfl⟩ := hformula
        simp only [BoolFormula.vars, Finset.mem_union] at hindex'
        rcases hindex' with hleft | hright
        · exact ih (fun instruction hinstruction =>
            hvars instruction (List.mem_of_mem_take hinstruction))
            z y index' hleft
        · exact ih (fun instruction hinstruction =>
            hvars instruction (List.mem_of_mem_drop hinstruction))
            x z index' hright
      · simpa only [reachesFormula] using hindex

theorem eval_decisionFormula_eq_true_internal {w : ℕ} (α : ℕ → Bool)
    (p : BP w) (x : Fin w) :
    BoolFormula.eval α (decisionFormula p x) = true ↔ BP.eval α p x ≠ x := by
  have hlen : p.length ≤ 2 ^ Nat.clog 2 p.length :=
    Nat.le_pow_clog Nat.one_lt_two p.length
  have hreach := eval_reachesFormula_internal α
    (Nat.clog 2 p.length) p x x hlen
  simp only [decisionFormula, BoolFormula.eval]
  cases hval : BoolFormula.eval α
      (reachesFormula (Nat.clog 2 p.length) p x x) <;>
    simp_all

theorem depth_decisionFormula_le_internal {w : ℕ} (p : BP w) (x : Fin w) :
    (decisionFormula p x).depth ≤ (w + 1) * Nat.clog 2 p.length + 2 := by
  have h := depth_reachesFormula_le_internal
    (Nat.clog 2 p.length) p x x
  simpa [decisionFormula, BoolFormula.depth] using Nat.succ_le_succ h

theorem vars_decisionFormula_lt_internal {w n : ℕ}
    (p : BP w) (x : Fin w)
    (hvars : ∀ instruction ∈ p, instruction.var < n) :
    ∀ index ∈ (decisionFormula p x).vars, index < n := by
  intro index hindex
  apply vars_reachesFormula_lt_internal hvars
    (Nat.clog 2 p.length) x x index
  simpa only [decisionFormula, BoolFormula.vars] using hindex

end BP

theorem clog_le_of_polynomial_bound_internal
    (C p n m : ℕ) (h : m ≤ C * (n + 1) ^ p) :
    Nat.clog 2 m ≤ Nat.clog 2 C + p * (Nat.log 2 n + 1) := by
  apply Nat.clog_le_of_le_pow
  calc
    m ≤ C * (n + 1) ^ p := h
    _ ≤ 2 ^ Nat.clog 2 C * (2 ^ (Nat.log 2 n + 1)) ^ p := by
      apply Nat.mul_le_mul
      · exact Nat.le_pow_clog Nat.one_lt_two C
      · exact Nat.pow_le_pow_left (Nat.succ_le_of_lt
          (Nat.lt_pow_succ_log_self Nat.one_lt_two n)) p
    _ = 2 ^ (Nat.clog 2 C + p * (Nat.log 2 n + 1)) := by
      rw [← pow_mul, Nat.mul_comm (Nat.log 2 n + 1) p, ← pow_add]

namespace BPFamily

theorem toFormulaFamily_computes_internal {w : ℕ} {R : BPFamily w}
    {x : ℕ → Fin w} {f : ℕ → (ℕ → Bool) → Bool}
    (h : R.DecidesOnTotalAssignments x f) :
    (R.toFormulaFamily x).ComputesOnTotalAssignments f := by
  intro n α
  apply Bool.eq_iff_iff.mpr
  exact (BP.eval_decisionFormula_eq_true_internal α (R n) (x n)).trans
    (h n α)

theorem toFormulaFamily_logDepth_internal {R : BPFamily 5}
    {x : ℕ → Fin 5} (h : R.PolynomialLength) :
    (R.toFormulaFamily x).LogDepth := by
  obtain ⟨C, p, hp⟩ := h
  let c := 6 * (Nat.clog 2 C + p + 1) + 2
  refine ⟨c, fun n => ?_⟩
  have hdepth : (BP.decisionFormula (R n) (x n)).depth ≤
      6 * Nat.clog 2 (R n).length + 2 := by
    simpa using BP.depth_decisionFormula_le_internal (R n) (x n)
  have hclog :=
    clog_le_of_polynomial_bound_internal C p n (R n).length (hp n)
  have hcoefficient : 6 * p ≤ c := by
    simp only [c]
    omega
  have hconstant : 6 * Nat.clog 2 C + 6 * p + 2 ≤ c := by
    simp only [c]
    omega
  calc
    (R.toFormulaFamily x n).depth
        ≤ 6 * Nat.clog 2 (R n).length + 2 := hdepth
    _ ≤ 6 * (Nat.clog 2 C + p * (Nat.log 2 n + 1)) + 2 := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 6 hclog) 2
    _ = (6 * p) * Nat.log 2 n +
        (6 * Nat.clog 2 C + 6 * p + 2) := by ring
    _ ≤ c * Nat.log 2 n + c :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hcoefficient) hconstant

end BPFamily

theorem formulaNC1OnTotalAssignments_subset_width5BPOnTotalAssignments_internal :
    FormulaNC1OnTotalAssignments ⊆ Width5BPOnTotalAssignments := by
  rintro f ⟨F, hdepth, hcomputes⟩
  obtain ⟨R, x, C, p, hlength, hdecides⟩ :=
    F.logDepth_polyLength_decides hdepth
  refine ⟨R, x, ⟨C, p, hlength⟩, fun n α => ?_⟩
  simpa only [hcomputes n α] using hdecides n α

theorem width5BPOnTotalAssignments_subset_formulaNC1OnTotalAssignments_internal :
    Width5BPOnTotalAssignments ⊆ FormulaNC1OnTotalAssignments := by
  rintro f ⟨R, x, hlength, hdecides⟩
  exact ⟨R.toFormulaFamily x,
    BPFamily.toFormulaFamily_logDepth_internal hlength,
    BPFamily.toFormulaFamily_computes_internal hdecides⟩

end Complexity
