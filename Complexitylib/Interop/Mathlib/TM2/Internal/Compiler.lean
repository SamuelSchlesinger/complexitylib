/-
Copyright (c) 2026 OpenAI, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM2.Internal.Simulation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite-state compilation of arbitrary supported TM2 programs

This packages the existing Mathlib compiler and its timing lemmas for any
finitely supported stack program with finite auxiliary state. The target's
alphabet is exactly Mathlib's stack-track alphabet; no external recoding is
hidden in the input or output contract. The timing lemmas remain in the
rational hitting-list development; `compile_source` generalizes the assembly
used in its `FiniteCompiler` module.
-/

@[expose] public section

namespace Complexity.MathlibTM2

open Turing
open scoped BigOperators

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Inhabited Λ] [Inhabited σ] [Fintype σ]

lemma compile_source (M : Λ → TM2.Stmt Γ Λ σ) (F : Finset Λ) (hF : TM2.Supports M F) :
    ∃ (m : ℕ) (G : TM0.Machine (TM2to1.Γ' K Γ) (Fin (m + 1))) (C : ℕ),
      0 < C ∧ ∀ (k : K) (w : List (Γ k)) (b : TM2.Cfg Γ Λ σ) (t : ℕ),
        exec (TM2.step M) t (TM2.init k w) = some b → TM2.step M b = none →
        ∃ u ≤ C * (w.length + t + 1) ^ 2, ∃ a,
          exec (TM0.step G) u (TM0.init (TM2to1.trInit k w)) = some a ∧
          TM0.step G a = none ∧
          ∃ c : TM1.Cfg (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ,
            TM2to1.TrCfg b c ∧ a.Tape = c.Tape := by
  classical
  let A := 1 + ∑ l ∈ F, (StackToOne.stackWeight (M l) + 1)
  have hA : 1 ≤ A := by simp [A]
  have hAC : ∀ l ∈ F, StackToOne.stackWeight (M l) + 1 ≤ A := by
    intro l hl
    exact (Finset.single_le_sum (f := fun l => StackToOne.stackWeight (M l) + 1)
      (fun _ _ => Nat.zero_le _) hl).trans (Nat.le_add_left _ _)
  let M₁ := TM2to1.tr M
  let F₁ := TM2to1.trSupp M F
  have hF₁ : TM1.Supports M₁ F₁ := TM2to1.tr_supports M hF
  let B := 1 + ∑ l ∈ F₁, OneToZero.weight (M₁ l)
  have hB : 1 ≤ B := by simp [B]
  have hBC : ∀ l ∈ F₁, OneToZero.weight (M₁ l) ≤ B := by
    intro l hl
    exact (Finset.single_le_sum (f := fun l => OneToZero.weight (M₁ l))
      (fun _ _ => Nat.zero_le _) hl).trans (Nat.le_add_left _ _)
  let F₀ := TM1to0.trStmts M₁ F₁
  have hF₀ : TM0.Supports (TM1to0.tr M₁) (F₀ : Set (TM1to0.Λ' M₁)) :=
    TM1to0.tr_supports M₁ hF₁
  obtain ⟨m, G, hG⟩ := FiniteStates.finite_machine (TM1to0.tr M₁) F₀ hF₀
  refine ⟨m, G, 10 * B * (A + 1) ^ 2, by positivity, ?_⟩
  intro k w b t hr hh
  have hlen : ∀ j, ((TM2.init k w : TM2.Cfg Γ Λ σ).stk j).length ≤ w.length := by
    intro j
    by_cases hj : j = k
    · subst j; simp [TM2.init]
    · simp [TM2.init, Function.update_of_ne hj]
  obtain ⟨u, c, hu, hc, he⟩ := StackToOne.execution_time M F hF A hAC t _ b
    (TM1.init (TM2to1.trInit k w)) w.length
    (Finset.some_mem_insertNone.mpr hF.1) hlen (TM2to1.trCfg_init k w) hr
  obtain ⟨v, hv, he'⟩ := OneToZero.execution_time M₁ F₁ hF₁ B hBC u _ c
    (Finset.some_mem_insertNone.mpr hF₁.1) he
  have hinit : TM1to0.trCfg M₁ (TM1.init (TM2to1.trInit k w)) =
      TM0.init (TM2to1.trInit k w) := rfl
  rw [hinit] at he'
  obtain ⟨a, ha, hhalt, htape⟩ := hG (TM2to1.trInit k w) v _ he'
    (OneToZero.halts M₁ c (StackToOne.halts M b c hc hh))
  refine ⟨v, ?_, a, ha, hhalt, c, hc, htape⟩
  have ht : t ≤ w.length + t + 1 := by omega
  have hs : w.length + A * t ≤ (A + 1) * (w.length + t + 1) := by
    nlinarith only [Nat.zero_le (A * w.length)]
  have hscan : 2 * (w.length + A * t) + 4 ≤
      4 * (A + 1) * (w.length + t + 1) := by
    nlinarith only [hs, hA, Nat.zero_le w.length, Nat.zero_le t]
  calc v ≤ B * u := hv
    _ ≤ B * (A * t * (2 * (w.length + A * t) + 4)) := Nat.mul_le_mul_left _ hu
    _ ≤ B * (A * (w.length + t + 1) * (4 * (A + 1) * (w.length + t + 1))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ ht) hscan)
    _ ≤ 10 * B * (A + 1) ^ 2 * (w.length + t + 1) ^ 2 := by
      nlinarith [Nat.zero_le (B * (w.length + t + 1) ^ 2)]

omit [DecidableEq K] [Inhabited Λ] [Inhabited σ] [Fintype σ] in
lemma tape_unique {a b : TM2.Cfg Γ Λ σ}
    {c d : TM1.Cfg (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ}
    (h : TM2to1.TrCfg a c) (h' : TM2to1.TrCfg b d) (hs : a.stk = b.stk) :
    c.Tape = d.Tape := by
  cases h with
  | mk L hL =>
    cases h' with
    | mk L' hL' =>
      have he : L = L' := by
        apply ListBlank.ext
        intro i
        funext k
        have hh := (hL k).trans
          ((congrArg (fun S => ListBlank.mk ((S k).map some).reverse) hs).trans (hL' k).symm)
        have hh' := congrArg (fun T => T.nth i) hh
        simpa only [ListBlank.nth_map, proj, PointedMap.mk_val] using hh'
      rw [he]

lemma exec_eq_iterate {α : Type*} (step : α → Option α) (t : ℕ) (a : α) :
    exec step t a = (fun s => s.bind step)^[t] (some a) := by
  suffices h : ∀ s : Option α, s.bind (exec step t) =
      (fun s : Option α => s.bind step)^[t] s by
    exact h (some a)
  intro s
  induction t generalizing s with
  | zero => cases s <;> rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply]
      cases s with
      | none => exact ih none
      | some a => exact ih (step a)

lemma output_length_bound (tm : FinTM2) :
    ∃ C : ℕ, 0 < C ∧ ∀ (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (time : ℕ),
      TM2OutputsInTime tm input (some output) time →
      output.length ≤ input.length + C * time := by
  classical
  let : Inhabited tm.Λ := ⟨tm.main⟩
  let F : Finset tm.Λ := @Finset.univ tm.Λ tm.ΛFin
  have supported : ∀ q : tm.Stmt, TM2.SupportsStmt F q := by
    intro q
    induction q <;> simp_all [TM2.SupportsStmt, F]
  have hF : TM2.Supports tm.m F := ⟨by simp [F], fun l _ => supported (tm.m l)⟩
  let C := 1 + ∑ l ∈ F, (StackToOne.stackWeight (tm.m l) + 1)
  have hC : ∀ l ∈ F, StackToOne.stackWeight (tm.m l) + 1 ≤ C := by
    intro l hl
    exact (Finset.single_le_sum (f := fun l => StackToOne.stackWeight (tm.m l) + 1)
      (fun _ _ => Nat.zero_le _) hl).trans (Nat.le_add_left _ _)
  refine ⟨C, by simp [C], ?_⟩
  intro input output time h
  change StateTransition.EvalsToInTime tm.step (initList tm input)
    (some (haltList tm output)) time at h
  have hr := (exec_eq_iterate tm.step h.steps (initList tm input)).trans h.evals_in_steps
  have hlen : ∀ k, ((initList tm input).stk k).length ≤ input.length := by
    intro k
    by_cases hk : k = tm.k₀
    · subst k; simp [initList]
    · simp [initList, hk]
  have hb := StackToOne.execution_length tm.m F hF C hC h.steps
    (initList tm input) (haltList tm output) input.length
    (by change some tm.main ∈ Finset.insertNone F; simp [F]) hlen hr tm.k₁
  have hb' : output.length ≤ input.length + C * h.steps := by simpa [haltList] using hb
  exact hb'.trans (Nat.add_le_add_left (Nat.mul_le_mul_left C h.steps_le_m) _)

lemma compile_bundled (tm : FinTM2) :
    ∃ (m : ℕ) (G : TM0.Machine (TM2to1.Γ' tm.K tm.Γ) (Fin (m + 1))) (C : ℕ),
      0 < C ∧ ∀ (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (time : ℕ),
        TM2OutputsInTime tm input (some output) time →
        ∃ u ≤ C * (input.length + time + 1) ^ 2, ∃ a,
          exec (TM0.step G) u (TM0.init (TM2to1.trInit tm.k₀ input)) = some a ∧
          TM0.step G a = none ∧ a.Tape = Tape.mk₁ (TM2to1.trInit tm.k₁ output) := by
  classical
  let : Inhabited tm.Λ := ⟨tm.main⟩
  let : Inhabited tm.σ := ⟨tm.initialState⟩
  let : Fintype tm.σ := tm.σFin
  let F : Finset tm.Λ := @Finset.univ tm.Λ tm.ΛFin
  have supported : ∀ q : tm.Stmt, TM2.SupportsStmt F q := by
    intro q
    induction q <;> simp_all [TM2.SupportsStmt, F]
  have hF : TM2.Supports tm.m F := ⟨by simp [F], fun l _ => supported (tm.m l)⟩
  obtain ⟨m, G, C, hC, hG⟩ := compile_source tm.m F hF
  refine ⟨m, G, C, hC, ?_⟩
  intro input output time h
  change StateTransition.EvalsToInTime tm.step (initList tm input)
    (some (haltList tm output)) time at h
  have hi : initList tm input = (TM2.init tm.k₀ input : tm.Cfg) := by
    change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
    congr 1
    funext k
    by_cases hk : k = tm.k₀
    · subst k; simp
    · simp [hk]
  have run := (exec_eq_iterate tm.step h.steps (initList tm input)).trans h.evals_in_steps
  have hr := (congrArg (fun c : tm.Cfg => exec tm.step h.steps c) hi).symm.trans run
  obtain ⟨u, hu, a, ha, hh, c, hc, ht⟩ := hG tm.k₀ input (haltList tm output)
    h.steps hr rfl
  refine ⟨u, hu.trans (Nat.mul_le_mul_left C
    (Nat.pow_le_pow_left (by have := h.steps_le_m; omega) 2)), a, ha, hh, ht.trans ?_⟩
  apply tape_unique hc (TM2to1.trCfg_init tm.k₁ output)
  funext k
  by_cases hk : k = tm.k₁
  · subst k; simp [haltList, TM2.init]
  · simp [haltList, TM2.init, hk]

end Complexity.MathlibTM2
