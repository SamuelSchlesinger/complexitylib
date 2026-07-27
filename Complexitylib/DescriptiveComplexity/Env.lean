/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.DescriptiveComplexity.Vocabulary

/-!
  Variable environments for first-order logic.

  Since `Fin.cons` is absent from Lean 4 core, we define our own
  environment machinery for mapping de Bruijn variables to universe elements.
-/

@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

/-- An environment maps `n` de Bruijn variables to elements of `Fin card`. -/
abbrev Env (card n : Nat) := Fin n → Fin card

/-- Extend an environment with a new element at index 0. -/
def envCons (a : Fin card) (σ : Env card n) : Env card (n + 1) :=
  fun i => if h : i.val = 0 then a else σ ⟨i.val - 1, by omega⟩

/-- The empty environment (no free variables). -/
def emptyEnv (card : Nat) : Env card 0 := Fin.elim0

theorem envCons_zero (a : Fin card) (σ : Env card n) :
    envCons a σ ⟨0, by omega⟩ = a := by
  simp [envCons]

theorem envCons_succ (a : Fin card) (σ : Env card n) (i : Fin n) :
    envCons a σ ⟨i.val + 1, by omega⟩ = σ i := by
  simp [envCons]

theorem envCons_comp (f : Fin m → Fin k) (a : Fin m) (σ : Env m n) :
    f ∘ envCons a σ = envCons (f a) (f ∘ σ) := by
  funext i
  simp [Function.comp, envCons]
  split
  · rfl
  · rfl

theorem emptyEnv_comp (f : Fin m → Fin k) :
    f ∘ emptyEnv m = emptyEnv k := by
  funext i
  exact Fin.elim0 i

end DescriptiveComplexity

end Complexity
