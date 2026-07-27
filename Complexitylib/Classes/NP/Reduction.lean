/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.NP
public import Complexitylib.Classes.P

/-!
# Polynomial-time many-one reductions and NP-completeness

This file defines **polynomial-time many-one (Karp) reductions** `L ≤ₚ L'` and
the derived notions **`NPHard`** and **`NPComplete`**, following Arora–Barak
(Definitions 2.7, 2.8).

A reduction `L ≤ₚ L'` is a polynomial-time computable function `f` (i.e. `f ∈ FP`)
such that `x ∈ L ↔ f x ∈ L'`. A language is NP-hard when every language in `NP`
reduces to it, and NP-complete when it is additionally a member of `NP`.

The headline application is `SAT.NPComplete_language` (Cook–Levin), in
`Complexitylib/SAT/CookLevin.lean`.
-/

@[expose] public section

namespace Complexity


/-- **Polynomial-time many-one reduction.** `MapReducesPoly L L'` (written
    `L ≤ₚ L'`) holds when there is a polynomial-time computable function `f`
    (`f ∈ FP`) with `x ∈ L ↔ f x ∈ L'` for every input `x`. -/
def MapReducesPoly (L L' : Language) : Prop :=
  ∃ f : List Bool → List Bool, f ∈ FP ∧ ∀ x, x ∈ L ↔ f x ∈ L'

@[inherit_doc] infix:50 " ≤ₚ " => MapReducesPoly

/-- **NP-hardness.** `L` is NP-hard when every language in `NP` reduces to `L`
    in polynomial time. -/
def NPHard (L : Language) : Prop := ∀ L' ∈ NP, L' ≤ₚ L

/-- **NP-completeness.** `L` is NP-complete when it is in `NP` and NP-hard. -/
def NPComplete (L : Language) : Prop := L ∈ NP ∧ NPHard L

/-! ### `≤ₚ` is a preorder

Reflexivity follows from `id ∈ FP`, and transitivity follows from closure of
`FP` under composition. The parameterized helper theorems retain the individual
dependencies for reuse. -/

/-- **Reflexivity of `≤ₚ` reduces to `id ∈ FP`.** -/
theorem MapReducesPoly.refl_of_id_mem (hid : id ∈ FP) (L : Language) : L ≤ₚ L :=
  ⟨id, hid, fun _ => Iff.rfl⟩

/-- **Polynomial-time many-one reducibility is reflexive.** -/
theorem MapReducesPoly.refl (L : Language) : L ≤ₚ L :=
  MapReducesPoly.refl_of_id_mem id_mem_FP L

/-- **Transitivity of `≤ₚ` reduces to `FP` being closed under composition.** -/
theorem MapReducesPoly.trans_of_comp
    (hcomp : ∀ f g : List Bool → List Bool, f ∈ FP → g ∈ FP → (g ∘ f) ∈ FP)
    {L₁ L₂ L₃ : Language} (h₁ : L₁ ≤ₚ L₂) (h₂ : L₂ ≤ₚ L₃) : L₁ ≤ₚ L₃ := by
  obtain ⟨f, hf, hf'⟩ := h₁
  obtain ⟨g, hg, hg'⟩ := h₂
  exact ⟨g ∘ f, hcomp f g hf hg, fun x => (hf' x).trans (hg' (f x))⟩

/-- **Polynomial-time many-one reducibility is transitive.** -/
theorem MapReducesPoly.trans {L₁ L₂ L₃ : Language}
    (h₁ : L₁ ≤ₚ L₂) (h₂ : L₂ ≤ₚ L₃) : L₁ ≤ₚ L₃ :=
  MapReducesPoly.trans_of_comp (fun _ _ hf hg => mem_FP_comp hf hg) h₁ h₂

/-! ### Transporting P membership -/

/-- Membership in `P` transports backward along a polynomial-time many-one
reduction. -/
theorem MapReducesPoly.mem_P {L₁ L₂ : Language}
    (hred : L₁ ≤ₚ L₂) (hL₂ : L₂ ∈ P) : L₁ ∈ P := by
  obtain ⟨f, hf, hcorrect⟩ := hred
  have hpre : f ⁻¹' L₂ ∈ P := mem_P_preimage hf hL₂
  have heq : L₁ = f ⁻¹' L₂ := by
    ext x
    exact hcorrect x
  rwa [heq]

/-! ### Transporting NP-hardness and NP-completeness -/

/-- NP-hardness transfers forward along a polynomial-time many-one reduction. -/
theorem NPHard.of_reduction {L₁ L₂ : Language}
    (h₁ : NPHard L₁) (h₂ : L₁ ≤ₚ L₂) : NPHard L₂ := by
  intro L hL
  exact MapReducesPoly.trans (h₁ L hL) h₂

/-- A language in `NP` is NP-complete when an NP-hard language reduces to it. -/
theorem NPComplete.of_mem_of_reduction {L₁ L₂ : Language}
    (h₁ : NPHard L₁) (hmem : L₂ ∈ NP) (h₂ : L₁ ≤ₚ L₂) :
    NPComplete L₂ :=
  ⟨hmem, h₁.of_reduction h₂⟩

/-- NP-completeness transfers forward along a polynomial-time reduction once
membership of the target language in `NP` is known. -/
theorem NPComplete.transfer {L₁ L₂ : Language}
    (h₁ : NPComplete L₁) (hmem : L₂ ∈ NP) (h₂ : L₁ ≤ₚ L₂) :
    NPComplete L₂ :=
  NPComplete.of_mem_of_reduction h₁.2 hmem h₂

end Complexity
