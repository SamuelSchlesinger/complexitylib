/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Core

/-!
# Unrestricted depth-three lower bound: circuit

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/Circuit.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {W : Type uDepth2}

namespace GateInput

/-- Substitute variables or constants into a gate input, respecting literal signs. -/
def subst (s : V → Sum W Bool) : GateInput V → GateInput W
  | .inl (v, b) => match s v with
    | .inl w => .inl (w, b)
    | .inr c => .inr (decide (c = b))
  | .inr b => .inr b

/-- Lift an assignment through a variable-or-constant substitution. -/
def assignment (s : V → Sum W Bool) (x : Cube W) : Cube V :=
  fun v => match s v with
    | .inl w => x w
    | .inr b => b

@[simp] theorem eval_subst (s : V → Sum W Bool) (l : GateInput V) (x : Cube W) :
    (subst s l).eval x = l.eval (assignment s x) := by
  cases l with
  | inl l =>
    rcases l with ⟨v, b⟩
    cases h : s v <;> simp [subst, eval, assignment, Literal.eval, h]
  | inr b => rfl

end GateInput

namespace RawClause

@[simp] theorem eval_eq_true (C : RawClause V) (x : Cube V) :
    C.eval x = true ↔ ∃ l ∈ C, l.eval x = true := by
  classical
  simp [eval]

@[simp] theorem eval_map_subst (s : V → Sum W Bool) (C : RawClause V)
    (x : Cube W) : RawClause.eval (C.map (GateInput.subst s)) x =
      C.eval (GateInput.assignment s x) := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [eval_eq_true, eval_eq_true]
  constructor
  · rintro ⟨a, ha, hx⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    exact ⟨l, hl, by simpa only [GateInput.eval_subst] using hx⟩
  · rintro ⟨l, hl, hx⟩
    refine ⟨GateInput.subst s l, List.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩
    simpa only [GateInput.eval_subst] using hx

end RawClause

namespace Circuit3

@[simp] theorem middleEval_eq_true (C : Circuit3 V) (j : Fin C.middleCount)
    (x : Cube V) : C.middleEval j x = true ↔
      ∀ i ∈ C.middle j, (C.bottom i).eval x = true := by
  classical
  simp [middleEval]

@[simp] theorem eval_eq_true (C : Circuit3 V) (x : Cube V) :
    C.eval x = true ↔ ∃ j ∈ C.top, C.middleEval j x = true := by
  classical
  simp [eval]

theorem bottomCount_le_gateCount (C : Circuit3 V) : C.bottomCount ≤ C.gateCount :=
  (Nat.le_add_right C.bottomCount C.middleCount).trans (Nat.le_succ _)

theorem middleCount_le_gateCount (C : Circuit3 V) : C.middleCount ≤ C.gateCount :=
  (Nat.le_add_left C.middleCount C.bottomCount).trans (Nat.le_succ _)

theorem middle_card_le_gateCount (C : Circuit3 V) (j : Fin C.middleCount) :
    (C.middle j).card ≤ C.gateCount := by
  exact (Finset.card_le_univ _).trans (by simpa using C.bottomCount_le_gateCount)

theorem top_card_le_gateCount (C : Circuit3 V) : C.top.card ≤ C.gateCount := by
  exact (Finset.card_le_univ _).trans (by simpa using C.middleCount_le_gateCount)

/-- Apply an input substitution to every bottom clause, preserving all gates. -/
def subst (C : Circuit3 V) (s : V → Sum W Bool) : Circuit3 W where
  bottomCount := C.bottomCount
  middleCount := C.middleCount
  bottom i := (C.bottom i).map (GateInput.subst s)
  middle := C.middle
  top := C.top

@[simp] theorem gateCount_subst (C : Circuit3 V) (s : V → Sum W Bool) :
    (C.subst s).gateCount = C.gateCount := rfl

@[simp] theorem middleEval_subst (C : Circuit3 V) (s : V → Sum W Bool)
    (j : Fin C.middleCount) (x : Cube W) :
    (C.subst s).middleEval j x = C.middleEval j (GateInput.assignment s x) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [middleEval_eq_true, subst, RawClause.eval_map_subst]

@[simp] theorem eval_subst (C : Circuit3 V) (s : V → Sum W Bool) (x : Cube W) :
    (C.subst s).eval x = C.eval (GateInput.assignment s x) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [eval_eq_true, middleEval_eq_true, subst, RawClause.eval_map_subst]

theorem computes_subst (C : Circuit3 V) {f : Cube V → Bool} (h : C.Computes f)
    (s : V → Sum W Bool) :
    (C.subst s).Computes (fun x => f (GateInput.assignment s x)) := by
  intro x
  rw [eval_subst, h]

end Circuit3

end DepthThreeLowerBound

end Complexity
