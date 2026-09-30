/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialCorrelation.Internal.Reduction

/-!
# Counting retained and exceptional generators

Toggling the chosen majority flag pairs the retained and omitted generators.
The unpaired generators have every block in the top `d` low-degree levels.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.PolynomialCorrelation.Internal

open Finset

variable {k m d : ℕ}

/-- A block whose low monomial lies within `d` levels of the middle. -/
abbrev ExceptionalAtom (m d : ℕ) := {a : Atom m // m < a.1.val.card + d}

/-- Toggle the selected majority flag, fixing generators without a pivot. -/
noncomputable def toggle (d : ℕ) (a : Term k m) : Term k m :=
  match pivot d a with
  | none => a
  | some i => setFlag a i (!(a i).2)

theorem pivot_toggle (a : Term k m) : pivot d (toggle d a) = pivot d a := by
  unfold toggle
  cases h : pivot d a <;> simp [pivot_setFlag, h]

theorem toggle_involutive : Function.Involutive (toggle (k := k) (m := m) d) := by
  intro a
  unfold toggle
  rw [show pivot d (match pivot d a with
      | none => a | some i => setFlag a i (!(a i).2)) = pivot d a from pivot_toggle a]
  cases h : pivot d a with
  | none => rfl
  | some i =>
    simp only [setFlag, Function.update_self, Bool.not_not, Function.update_idem]
    exact Function.update_eq_self i a

theorem allowed_of_pivot_none {a : Term k m} (h : pivot d a = none) : Allowed d a := by
  intro i hi
  simp [h] at hi

theorem allowed_iff_of_pivot {a : Term k m} {i : Fin k} (h : pivot d a = some i) :
    Allowed d a ↔ (a i).2 = false := by
  constructor
  · exact fun ha => ha i h
  · intro ha j hj
    rw [h] at hj
    cases Option.some.inj hj
    exact ha

theorem pivot_none_iff (a : Term k m) :
    pivot d a = none ↔ ∀ i, m < (a i).1.val.card + d := by
  simp only [pivot]
  split <;> simp_all

/-- A generator has no pivot exactly when each of its block indices is exceptional. -/
noncomputable def exceptionalEquiv :
    {a : Term k m // pivot d a = none} ≃ (Fin k → ExceptionalAtom m d) where
  toFun a i := ⟨a.val i, (pivot_none_iff a.val).mp a.property i⟩
  invFun a := ⟨fun i => (a i).val, (pivot_none_iff _).mpr fun i => (a i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_allowed :
    2 * Nat.card {a : Term k m // Allowed d a} =
      Nat.card (Term k m) + Nat.card (ExceptionalAtom m d) ^ k := by
  classical
  let : Fintype {a : Term k m // Allowed d a} := Fintype.ofFinite _
  let : Fintype {a : Term k m // pivot d a = none} := Fintype.ofFinite _
  have hi (a : Term k m) :
      (if Allowed d a then 1 else 0 : ℕ) + (if Allowed d (toggle d a) then 1 else 0) =
        1 + if pivot d a = none then 1 else 0 := by
    cases h : pivot d a with
    | none => simp [allowed_of_pivot_none h, toggle, h]
    | some i =>
      rw [allowed_iff_of_pivot h, allowed_iff_of_pivot (by simpa [pivot_toggle] using h)]
      simp only [toggle, h, setFlag, Function.update_self, reduceCtorEq, ↓reduceIte]
      cases (a i).2 <;> simp
  have hs := congrArg (fun f : Term k m → ℕ => ∑ a, f a) (funext hi)
  let e : Equiv.Perm (Term k m) :=
    ⟨toggle d, toggle d, toggle_involutive, toggle_involutive⟩
  have ht := Equiv.sum_comp e (fun a => if Allowed d a then (1 : ℕ) else 0)
  change (∑ a : Term k m, if Allowed d (toggle d a) then (1 : ℕ) else 0) =
    ∑ a : Term k m, if Allowed d a then (1 : ℕ) else 0 at ht
  simp only [Finset.sum_add_distrib] at hs
  rw [ht] at hs
  have he : Nat.card {a : Term k m // pivot d a = none} =
      Nat.card (ExceptionalAtom m d) ^ k := by
    rw [Nat.card_congr exceptionalEquiv]
    simp [Nat.card_eq_fintype_card]
  rw [← he]
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, two_mul] using hs

theorem compl_low {x : Finset (Fin (2 * m + 1))} (hx : m < x.card) : xᶜ.card ≤ m := by
  rw [card_compl, Fintype.card_fin]
  omega

theorem low_compl_high (a : Low (Fin (2 * m + 1)) m) : m < a.valᶜ.card := by
  rw [card_compl, Fintype.card_fin]
  have := a.property
  omega

/-- Pairing a lower-half subset with its complement enumerates the whole block. -/
def atomCubeEquiv : Atom m ≃ Finset (Fin (2 * m + 1)) where
  toFun a := if a.2 then a.1.valᶜ else a.1.val
  invFun x := if h : x.card ≤ m then (⟨x, h⟩, false)
    else (⟨xᶜ, compl_low (by omega)⟩, true)
  left_inv a := by
    rcases a with ⟨a, b⟩
    cases b
    · simp [a.property]
    · simp [not_le.mpr (low_compl_high a)]
  right_inv x := by
    dsimp only
    split <;> simp_all

theorem card_atom : Nat.card (Atom m) = 2 ^ (2 * m + 1) := by
  rw [Nat.card_congr atomCubeEquiv]
  simp [Nat.card_eq_fintype_card]

theorem card_term : Nat.card (Term k m) = Nat.card (BlockCube k m) := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
  rw [Fintype.card_congr atomCubeEquiv]

/-- The finite counting inequality underlying the exponential correlation bound. -/
theorem twice_agreement_card_le
    (p : MvPolynomial (Fin k × Fin (2 * m + 1)) (ZMod 2)) (hp : p.totalDegree ≤ d)
    (E : Set (BlockCube k m)) (hE : ∀ x ∈ E, polynomialEval p x = xorMajority x) :
    2 * Nat.card E ≤ Nat.card (BlockCube k m) + Nat.card (ExceptionalAtom m d) ^ k := by
  calc
    2 * Nat.card E ≤ 2 * Nat.card {a : Term k m // Allowed d a} :=
      Nat.mul_le_mul_left 2 (agreement_card_le p hp E hE)
    _ = _ := by rw [card_allowed, card_term]

end Complexity.BooleanAnalysis.PolynomialCorrelation.Internal
