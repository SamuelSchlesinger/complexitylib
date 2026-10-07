/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Circuit
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionNormalization

/-!
# Unrestricted depth-three lower bound: circuit normalization

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/CircuitNormalization.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

namespace DepthThreeLowerBound

variable {V : Type uDepth1}

namespace RawClause

/-- Extract the literal inputs of a raw clause. -/
def literalPart : GateInput V → Option (Literal V)
  | .inl l => some l
  | .inr _ => none

/-- The finite set of literals occurring in a raw clause. -/
noncomputable def literals (C : RawClause V) : Clause V := by
  classical
  exact (C.filterMap literalPart).toFinset

@[simp] theorem mem_literals (C : RawClause V) (l : Literal V) :
    l ∈ C.literals ↔ Sum.inl l ∈ C := by
  classical
  simp only [literals, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, he⟩
    cases a with
    | inl k =>
      have hk : k = l := Option.some.inj he
      simpa [hk] using ha
    | inr b => simp [literalPart] at he
  · intro h
    exact ⟨.inl l, h, rfl⟩

theorem eval_true_iff (C : RawClause V) (x : Cube V) :
    C.eval x = true ↔ Sum.inr true ∈ C ∨ C.literals.eval x = true := by
  rw [eval_eq_true, Clause.eval_eq_true]
  constructor
  · rintro ⟨a, ha, hx⟩
    cases a with
    | inl l => exact Or.inr ⟨l, (mem_literals C l).mpr ha, (Literal.eval_eq_true l x).mp hx⟩
    | inr b =>
      change b = true at hx
      exact Or.inl (hx ▸ ha)
  · rintro (h | ⟨l, hl, hx⟩)
    · exact ⟨.inr true, h, rfl⟩
    · exact ⟨.inl l, (mem_literals C l).mp hl, (Literal.eval_eq_true l x).mpr hx⟩

/-- Normalize a raw clause, accounting for constants and complementary literals. -/
noncomputable def normalize (C : RawClause V) : Option (Clause V) := by
  classical
  exact if Sum.inr true ∈ C ∨ ¬ C.literals.Normalized then none else some C.literals

theorem normalized_of_normalize_eq_some {C : RawClause V} {D : Clause V}
    (h : C.normalize = some D) : D.Normalized := by
  classical
  unfold normalize at h
  split at h
  · contradiction
  · rename_i hn
    have hCD : C.literals = D := Option.some.inj h
    rw [← hCD]
    exact Classical.not_not.mp (fun hbad => hn (Or.inr hbad))

theorem normalize_eval (C : RawClause V) (x : Cube V) :
    ((C.normalize).map (fun D => D.eval x)).getD true = C.eval x := by
  classical
  unfold normalize
  split
  · rename_i h
    have ht : C.eval x = true := by
      apply (eval_true_iff C x).mpr
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Clause.eval_true_of_not_normalized h x)
    simp [ht]
  · rename_i h
    have hc : Sum.inr true ∉ C := fun hc => h (Or.inl hc)
    change C.literals.eval x = C.eval x
    apply Bool.eq_iff_iff.mpr
    rw [eval_true_iff]
    simp [hc]

end RawClause

namespace Circuit3

/-- Represent a middle gate as the conjunction of its normalized bottom clauses. -/
noncomputable def middleCNF (C : Circuit3 V) (j : Fin C.middleCount) : CNF V :=
  (C.middle j).toList.filterMap fun i => (C.bottom i).normalize

theorem mem_middleCNF (C : Circuit3 V) (j : Fin C.middleCount) (D : Clause V) :
    D ∈ C.middleCNF j ↔ ∃ i ∈ C.middle j, (C.bottom i).normalize = some D := by
  simp [middleCNF, List.mem_filterMap]

theorem middleCNF_normalized (C : Circuit3 V) (j : Fin C.middleCount) :
    (C.middleCNF j).Normalized := by
  intro D hD
  obtain ⟨i, _, hi⟩ := (mem_middleCNF C j D).mp hD
  exact RawClause.normalized_of_normalize_eq_some hi

theorem middleCNF_length_le_bottomCount (C : Circuit3 V) (j : Fin C.middleCount) :
    (C.middleCNF j).length ≤ C.bottomCount := by
  calc
    (C.middleCNF j).length ≤ (C.middle j).toList.length := List.length_filterMap_le _ _
    _ = (C.middle j).card := Finset.length_toList _
    _ ≤ C.bottomCount := by simpa using Finset.card_le_univ (C.middle j)

theorem middleCNF_length_le_gateCount (C : Circuit3 V) (j : Fin C.middleCount) :
    (C.middleCNF j).length ≤ C.gateCount :=
  (C.middleCNF_length_le_bottomCount j).trans C.bottomCount_le_gateCount

@[simp] theorem eval_middleCNF (C : Circuit3 V) (j : Fin C.middleCount) (x : Cube V) :
    (C.middleCNF j).eval x = C.middleEval j x := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [CNF.eval_eq_true, middleEval_eq_true]
  constructor
  · intro hx i hi
    have he := (C.bottom i).normalize_eval x
    cases hn : (C.bottom i).normalize with
    | none => simpa [hn] using he.symm
    | some D =>
      have hD := hx D ((mem_middleCNF C j D).mpr ⟨i, hi, hn⟩)
      simpa [hn, hD] using he.symm
  · intro hx D hD
    obtain ⟨i, hi, hn⟩ := (mem_middleCNF C j D).mp hD
    have he := (C.bottom i).normalize_eval x
    simpa [hn, hx i hi] using he

theorem eval_eq_true_iff_middleCNF (C : Circuit3 V) (x : Cube V) :
    C.eval x = true ↔ ∃ j ∈ C.top, (C.middleCNF j).eval x = true := by
  simp only [eval_middleCNF, eval_eq_true]

theorem middleCNF_implies_output (C : Circuit3 V) {j : Fin C.middleCount}
    (hj : j ∈ C.top) {x : Cube V} (hx : (C.middleCNF j).eval x = true) :
    C.eval x = true := (eval_eq_true_iff_middleCNF C x).mpr ⟨j, hj, hx⟩

end Circuit3

end DepthThreeLowerBound

end Complexity
