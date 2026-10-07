/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Defs

/-!
# Unrestricted depth-three lower bound: core

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/Core.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3

namespace DepthThreeLowerBound

/-- A finite set of signed input literals, interpreted as a disjunction. -/
abbrev Clause (V : Type uDepth1) := Finset (Literal V)
/-- A list of clauses, interpreted as a conjunction. -/
abbrev CNF (V : Type uDepth2) := List (Clause V)

variable {V : Type uDepth3}

namespace Literal

/-- Flip the satisfying value of a literal. -/
def compl (l : Literal V) : Literal V := (l.1, !l.2)

@[simp] theorem eval_eq_true (l : Literal V) (x : Cube V) :
    l.eval x = true ↔ x l.1 = l.2 := by simp [eval]

@[simp] theorem compl_compl (l : Literal V) : l.compl.compl = l := by
  cases l with
  | mk v b => cases b <;> rfl

@[simp] theorem eval_compl (l : Literal V) (x : Cube V) :
    l.compl.eval x = !(l.eval x) := by
  rcases l with ⟨v, b⟩
  cases b <;> cases h : x v <;> simp [compl, eval, h]

end Literal

namespace Clause

/-- Evaluate the disjunction of the literals in a clause. -/
noncomputable def eval (C : Clause V) (x : Cube V) : Bool := by
  classical
  exact decide (∃ l ∈ C, l.eval x = true)

/-- The variables appearing in a clause, forgetting signs. -/
noncomputable def scope (C : Clause V) : Finset V := by
  classical
  exact C.image Prod.fst

/-- The number of distinct variables appearing in a clause. -/
noncomputable def width (C : Clause V) : ℕ := C.scope.card

/-- No variable occurs with both signs in the clause. -/
def Normalized (C : Clause V) : Prop :=
  ∀ v, (v, false) ∈ C → (v, true) ∈ C → False

@[simp] theorem eval_eq_true (C : Clause V) (x : Cube V) :
    C.eval x = true ↔ ∃ l ∈ C, x l.1 = l.2 := by
  classical
  simp [eval]

@[simp] theorem eval_empty (x : Cube V) : (∅ : Clause V).eval x = false := by
  simp [eval]

@[simp] theorem scope_empty : (∅ : Clause V).scope = ∅ := by
  classical
  simp [scope]

@[simp] theorem width_empty : (∅ : Clause V).width = 0 := by
  simp [width]

@[simp] theorem eval_singleton (l : Literal V) (x : Cube V) :
    ({l} : Clause V).eval x = l.eval x := by
  classical
  simp [eval, Literal.eval]

theorem eval_mono {C D : Clause V} (h : C ⊆ D) {x : Cube V}
    (hx : C.eval x = true) : D.eval x = true := by
  rw [eval_eq_true] at hx ⊢
  obtain ⟨l, hl, hx⟩ := hx
  exact ⟨l, h hl, hx⟩

theorem Normalized.subset {C D : Clause V} (hD : D.Normalized) (h : C ⊆ D) :
    C.Normalized := by
  intro v hf ht
  exact hD v (h hf) (h ht)

theorem Normalized.fst_injOn {C : Clause V} (h : C.Normalized) :
    Set.InjOn Prod.fst (↑C : Set (Literal V)) := by
  rintro ⟨v, b⟩ hb ⟨w, c⟩ hc hv
  change v = w at hv
  subst w
  cases b <;> cases c
  · rfl
  · exact (h v hb hc).elim
  · exact (h v hc hb).elim
  · rfl

theorem Normalized.card_eq_width {C : Clause V} (h : C.Normalized) :
    C.card = C.width := by
  classical
  exact (Finset.card_image_of_injOn h.fst_injOn).symm

theorem scope_mono {C D : Clause V} (h : C ⊆ D) : C.scope ⊆ D.scope := by
  classical
  exact Finset.image_subset_image h

theorem width_mono {C D : Clause V} (h : C ⊆ D) : C.width ≤ D.width :=
  Finset.card_le_card (scope_mono h)

end Clause

namespace CNF

/-- Evaluate the conjunction of the clauses in a CNF. -/
noncomputable def eval (H : CNF V) (x : Cube V) : Bool := by
  classical
  exact decide (∀ C ∈ H, C.eval x = true)

/-- Every clause involves at most the given number of distinct variables. -/
def WidthAtMost (H : CNF V) (b : ℕ) : Prop := ∀ C ∈ H, C.width ≤ b

/-- Every clause has at most one sign for each variable. -/
def Normalized (H : CNF V) : Prop := ∀ C ∈ H, C.Normalized

@[simp] theorem eval_eq_true (H : CNF V) (x : Cube V) :
    H.eval x = true ↔ ∀ C ∈ H, C.eval x = true := by
  classical
  simp [eval]

@[simp] theorem eval_nil (x : Cube V) : CNF.eval ([] : CNF V) x = true := by
  simp [eval]

@[simp] theorem eval_cons (C : Clause V) (H : CNF V) (x : Cube V) :
    CNF.eval (C :: H) x = (C.eval x && H.eval x) := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [eval_eq_true, Bool.and_eq_true, eval_eq_true]
  constructor
  · intro h
    exact ⟨h C (by simp), fun D hD => h D (by simp [hD])⟩
  · rintro ⟨hc, hH⟩ D hD
    rcases List.mem_cons.mp hD with hD | hD
    · simpa only [hD] using hc
    · exact hH D hD

@[simp] theorem eval_append (H J : CNF V) (x : Cube V) :
    (H ++ J).eval x = (H.eval x && J.eval x) := by
  induction H with
  | nil => simp
  | cons C H ih => simp [ih, Bool.and_assoc]

theorem eval_antitone {H J : CNF V} (h : H ⊆ J) {x : Cube V}
    (hx : J.eval x = true) : H.eval x = true := by
  rw [eval_eq_true] at hx ⊢
  exact fun C hC => hx C (h hC)

theorem WidthAtMost.mono {H : CNF V} {b c : ℕ} (h : H.WidthAtMost b)
    (hbc : b ≤ c) : H.WidthAtMost c := fun C hC => (h C hC).trans hbc

end CNF

/-- The zero-one real indicator of a Boolean value. -/
def indicator (b : Bool) : ℝ := if b then 1 else 0
/-- Encode `true` by `1` and `false` by `-1`. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem indicator_false : indicator false = 0 := rfl
@[simp] theorem indicator_true : indicator true = 1 := rfl
@[simp] theorem sign_false : sign false = -1 := rfl
@[simp] theorem sign_true : sign true = 1 := rfl

@[simp] theorem indicator_and (b c : Bool) :
    indicator (b && c) = indicator b * indicator c := by
  cases b <;> cases c <;> simp [indicator]

theorem indicator_nonneg (b : Bool) : 0 ≤ indicator b := by
  cases b <;> simp [indicator]

theorem indicator_le_one (b : Bool) : indicator b ≤ 1 := by
  cases b <;> simp [indicator]

end DepthThreeLowerBound

end Complexity
