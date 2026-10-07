/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Core
public import Mathlib.Data.List.Basic

/-!
# Unrestricted depth-three lower bound: restriction normalization

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionNormalization.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

namespace DepthThreeLowerBound

variable {V : Type uDepth1}

namespace Clause

theorem eval_true_of_not_normalized {C : Clause V} (h : ¬ C.Normalized)
    (x : Cube V) : C.eval x = true := by
  classical
  apply (eval_eq_true C x).mpr
  by_contra hx
  apply h
  intro v hf ht
  cases hv : x v
  · exact hx ⟨(v, false), hf, hv⟩
  · exact hx ⟨(v, true), ht, hv⟩

/-- The value that falsifies the selected literal of a normalized clause. -/
noncomputable def forbiddenValue (C : Clause V) (v : V) : Bool := by
  classical
  exact decide ((v, false) ∈ C)

theorem forbiddenValue_ne_literal {C : Clause V} (hC : C.Normalized)
    {l : Literal V} (hl : l ∈ C) : C.forbiddenValue l.1 ≠ l.2 := by
  classical
  rcases l with ⟨v, b⟩
  cases b
  · simp [forbiddenValue, hl]
  · have hf : (v, false) ∉ C := fun hf => hC v hf hl
    simp [forbiddenValue, hf]

theorem eval_eq_false_iff (C : Clause V) (x : Cube V) :
    C.eval x = false ↔ ∀ l ∈ C, x l.1 ≠ l.2 := by
  classical
  constructor
  · intro hx l hl he
    have ht := (eval_eq_true C x).mpr ⟨l, hl, he⟩
    simp [hx] at ht
  · intro hx
    cases he : C.eval x
    · rfl
    · obtain ⟨l, hl, hxl⟩ := (eval_eq_true C x).mp he
      exact (hx l hl hxl).elim

theorem eval_eq_false_iff_forbidden {C : Clause V} (hC : C.Normalized)
    (x : Cube V) :
    C.eval x = false ↔ ∀ v ∈ C.scope, x v = C.forbiddenValue v := by
  classical
  rw [eval_eq_false_iff]
  constructor
  · intro hx v hv
    obtain ⟨⟨w, b⟩, hl, hval⟩ := Finset.mem_image.mp hv
    change w = v at hval
    subst v
    have hxb := hx (w, b) hl
    have hfb := forbiddenValue_ne_literal hC hl
    cases hxx : x w <;> cases hff : C.forbiddenValue w <;> cases b <;>
      simp_all
  · intro hx l hl
    have hv : l.1 ∈ C.scope := Finset.mem_image_of_mem Prod.fst hl
    rw [hx l.1 hv]
    exact forbiddenValue_ne_literal hC hl

/-- The Boolean negation of a clause's evaluation. -/
noncomputable def violation (C : Clause V) (x : Cube V) : Bool := !(C.eval x)

@[simp] theorem violation_eq_true (C : Clause V) (x : Cube V) :
    C.violation x = true ↔ C.eval x = false := by
  cases h : C.eval x <;> simp [violation, h]

theorem violation_eq_true_iff_forbidden {C : Clause V} (hC : C.Normalized)
    (x : Cube V) :
    C.violation x = true ↔ ∀ v ∈ C.scope, x v = C.forbiddenValue v := by
  rw [violation_eq_true, eval_eq_false_iff_forbidden hC]

end Clause

namespace CNF

/-- Discard tautological clauses from a CNF. -/
noncomputable def normalize (H : CNF V) : CNF V := by
  classical
  exact H.filter fun C => decide C.Normalized

@[simp] theorem mem_normalize {H : CNF V} {C : Clause V} :
    C ∈ H.normalize ↔ C ∈ H ∧ C.Normalized := by
  classical
  simp [normalize]

theorem normalize_normalized (H : CNF V) : H.normalize.Normalized := by
  intro C hC
  exact (mem_normalize.mp hC).2

theorem normalize_widthAtMost {H : CNF V} {b : ℕ} (hH : H.WidthAtMost b) :
    H.normalize.WidthAtMost b := by
  intro C hC
  exact hH C (mem_normalize.mp hC).1

@[simp] theorem eval_normalize (H : CNF V) (x : Cube V) :
    H.normalize.eval x = H.eval x := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [eval_eq_true, eval_eq_true]
  constructor
  · intro hx C hC
    by_cases hn : C.Normalized
    · exact hx C (mem_normalize.mpr ⟨hC, hn⟩)
    · exact Clause.eval_true_of_not_normalized hn x
  · intro hx C hC
    exact hx C (mem_normalize.mp hC).1

end CNF

end DepthThreeLowerBound

end Complexity
