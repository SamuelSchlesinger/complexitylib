/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM2.Defs
public import Complexitylib.RationalHitting.Internal.StackSimulation

/-!
# Stack-growth bounds using the existing simulation tools

The rational hitting-list development already proves timing bounds for
Mathlib's TM2-to-TM1 and TM1-to-TM0 compilers, together with finite-state
restriction. Those proofs remain in their original modules and namespaces.
This module reuses them and adds a bound on the length of each stack.
-/

@[expose] public section

namespace Complexity.MathlibTM2

open Turing

export RationalHitting.TMTime (exec_zero exec_add exec_trans exec_positive_congr)

namespace OneToZero
export RationalHitting.TMTime.OneToZero (weight weight_pos statement_time execution_time halts)
end OneToZero

namespace StackToOne
export RationalHitting.TMTime.StackToOne (go_time return_time stackWeight stackWeight_run
  stWrite_length updated_length continuation_time statement_length step_time execution_time halts)

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
variable [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ)

/-- Each stack grows at most linearly in the number of source transitions. -/
theorem execution_length [Inhabited Λ] (F : Finset Λ) (hF : TM2.Supports M F)
    (C : ℕ) (hC : ∀ l ∈ F, stackWeight (M l) + 1 ≤ C)
    (t : ℕ) (a b : TM2.Cfg Γ Λ σ) (L : ℕ)
    (ha : a.l ∈ Finset.insertNone F) (hS : ∀ k, (a.stk k).length ≤ L)
    (hr : exec (TM2.step M) t a = some b) :
    ∀ k, (b.stk k).length ≤ L + C * t := by
  induction t generalizing L a with
  | zero =>
    have he : a = b := Option.some.inj hr
    subst b
    simpa using hS
  | succ t ih =>
    obtain ⟨l, v, S⟩ := a
    cases l with
    | none => simp [exec, TM2.step] at hr
    | some l =>
      have hl := Finset.some_mem_insertNone.mp ha
      have hnext : (TM2.stepAux (M l) v S).l ∈ Finset.insertNone F :=
        TM2.step_supports M hF (by rfl) ha
      have hlen : ∀ k, ((TM2.stepAux (M l) v S).stk k).length ≤ L + C := by
        intro k
        exact (statement_length (M l) v S L hS k).trans (by have := hC l hl; omega)
      change exec (TM2.step M) t (TM2.stepAux (M l) v S) = some b at hr
      intro k
      have hk := ih _ (L + C) hnext hlen hr k
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk

end StackToOne

namespace FiniteStates
export RationalHitting.TMTime.FiniteStates (stateEncode stateDecode stateEncode_default
  stateDecode_encode machine cfg cfg_init step_cfg execution run_support finite_machine)
end FiniteStates

end Complexity.MathlibTM2
