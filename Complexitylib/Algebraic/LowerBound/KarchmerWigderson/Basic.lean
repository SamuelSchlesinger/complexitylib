/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Karchmer–Wigderson games

A De Morgan formula has literal leaves and binary AND and OR gates. The
Karchmer–Wigderson game of `f` gives Alice an input `x` with `f x = 1` and
Bob an input `y` with `f y = 0`; they must agree on a coordinate where `x`
and `y` differ. A deterministic protocol is a binary tree whose internal
nodes are owned by one player and branch on that player's input, and whose
leaves name a coordinate.

The Karchmer–Wigderson theorem says that formulas and protocols are the same
trees: an OR gate is a node where Alice says which side of the disjunction
her input satisfies, an AND gate is a node where Bob says which side his
input violates, and a literal leaf names its coordinate
(`Formula.toProtocol`). Conversely a protocol induces, at every node, a
rectangle of inputs still consistent with the transcript, and the formula
built with OR at Alice's nodes and AND at Bob's nodes is `1` on Alice's side
and `0` on Bob's side of every rectangle (`Protocol.toFormula`). Depth and
leaf count are preserved in both directions, so the minimum formula depth of
`f` equals the minimum protocol depth of its game
(`formulaDepth_eq_protocolDepth`), and likewise for leaf size.
-/

@[expose] public section

namespace Algebraic
namespace KW

open scoped Classical

/-! ### De Morgan formulas -/

/-- A De Morgan formula: literal leaves, constants, binary AND and OR. -/
inductive Formula (n : Nat)
  /-- The literal `x_i` when `positive`, otherwise `¬ x_i`. -/
  | lit (index : Fin n) (positive : Bool)
  /-- A Boolean constant. -/
  | const (value : Bool)
  /-- Conjunction. -/
  | and (left right : Formula n)
  /-- Disjunction. -/
  | or (left right : Formula n)

namespace Formula

variable {n : Nat}

/-- Evaluate a formula. -/
def eval : Formula n → (Fin n → Bool) → Bool
  | lit i b, x => x i == b
  | const b, _ => b
  | and l r, x => l.eval x && r.eval x
  | or l r, x => l.eval x || r.eval x

@[simp] theorem eval_lit (i : Fin n) (b : Bool) (x : Fin n → Bool) :
    (lit i b).eval x = (x i == b) := rfl

@[simp] theorem eval_const (b : Bool) (x : Fin n → Bool) : (const b : Formula n).eval x = b := rfl

@[simp] theorem eval_and (l r : Formula n) (x : Fin n → Bool) :
    (and l r).eval x = (l.eval x && r.eval x) := rfl

@[simp] theorem eval_or (l r : Formula n) (x : Fin n → Bool) :
    (or l r).eval x = (l.eval x || r.eval x) := rfl

/-- The depth: the longest root-to-leaf path. -/
def depth : Formula n → Nat
  | lit _ _ => 0
  | const _ => 0
  | and l r => max l.depth r.depth + 1
  | or l r => max l.depth r.depth + 1

/-- The number of leaves, counting literals and constants. -/
def leaves : Formula n → Nat
  | lit _ _ => 1
  | const _ => 1
  | and l r => l.leaves + r.leaves
  | or l r => l.leaves + r.leaves

theorem one_le_leaves : ∀ F : Formula n, 1 ≤ F.leaves
  | lit _ _ => le_rfl
  | const _ => le_rfl
  | and l r => by simp only [leaves]; have := one_le_leaves l; omega
  | or l r => by simp only [leaves]; have := one_le_leaves l; omega

/-- The De Morgan dual, computing the negation with the same shape. -/
def neg : Formula n → Formula n
  | lit i b => lit i (!b)
  | const b => const (!b)
  | and l r => or l.neg r.neg
  | or l r => and l.neg r.neg

@[simp] theorem eval_neg : ∀ (F : Formula n) (x : Fin n → Bool), F.neg.eval x = !F.eval x
  | lit i b, x => by
    simp only [neg, eval]
    cases x i <;> cases b <;> rfl
  | const b, _ => rfl
  | and l r, x => by simp [neg, eval_neg l, eval_neg r]
  | or l r, x => by simp [neg, eval_neg l, eval_neg r]

@[simp] theorem depth_neg : ∀ F : Formula n, F.neg.depth = F.depth
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by simp [neg, depth, depth_neg l, depth_neg r]
  | or l r => by simp [neg, depth, depth_neg l, depth_neg r]

@[simp] theorem leaves_neg : ∀ F : Formula n, F.neg.leaves = F.leaves
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by simp [neg, leaves, leaves_neg l, leaves_neg r]
  | or l r => by simp [neg, leaves, leaves_neg l, leaves_neg r]

/-- A formula computes `f` when it agrees with `f` everywhere. -/
def Computes (F : Formula n) (f : Cslib.BooleanFunction n) : Prop :=
  ∀ x, F.eval x = f x

end Formula

/-! ### Protocols -/

/-- A deterministic two-party protocol whose leaves name a coordinate. Each
internal node is owned by Alice or Bob and branches on the owner's input. -/
inductive Protocol (n : Nat)
  /-- Output a coordinate. -/
  | answer (index : Fin n)
  /-- Alice branches on her input; `true` selects the right child. -/
  | alice (choose : (Fin n → Bool) → Bool) (left right : Protocol n)
  /-- Bob branches on his input; `true` selects the right child. -/
  | bob (choose : (Fin n → Bool) → Bool) (left right : Protocol n)

namespace Protocol

variable {n : Nat}

/-- The coordinate output on inputs `x` for Alice and `y` for Bob. -/
def run : Protocol n → (Fin n → Bool) → (Fin n → Bool) → Fin n
  | answer i, _, _ => i
  | alice c l r, x, y => if c x then r.run x y else l.run x y
  | bob c l r, x, y => if c y then r.run x y else l.run x y

/-- The depth: the longest root-to-leaf path. -/
def depth : Protocol n → Nat
  | answer _ => 0
  | alice _ l r => max l.depth r.depth + 1
  | bob _ l r => max l.depth r.depth + 1

/-- The number of leaves. -/
def leaves : Protocol n → Nat
  | answer _ => 1
  | alice _ l r => l.leaves + r.leaves
  | bob _ l r => l.leaves + r.leaves

/-- The protocol solves the game on the rectangle `A × B`: on inputs from
`A` for Alice and `B` for Bob, the output coordinate distinguishes them. -/
def Solves (P : Protocol n) (A B : (Fin n → Bool) → Prop) : Prop :=
  ∀ x y, A x → B y → x (P.run x y) ≠ y (P.run x y)

/-- The protocol solves the Karchmer–Wigderson game of `f`. -/
def SolvesKW (P : Protocol n) (f : Cslib.BooleanFunction n) : Prop :=
  P.Solves (fun x => f x = true) (fun y => f y = false)

end Protocol

/-! ### From formulas to protocols -/

namespace Formula

variable {n : Nat}

/-- The protocol of a formula: Bob resolves conjunctions, Alice resolves
disjunctions, literals name their coordinate. A constant leaf, which can only
be reached on an empty rectangle, answers the default coordinate `i₀`. -/
def toProtocol (i₀ : Fin n) : Formula n → Protocol n
  | lit i _ => .answer i
  | const _ => .answer i₀
  | and l r => .bob (fun y => l.eval y) (l.toProtocol i₀) (r.toProtocol i₀)
  | or l r => .alice (fun x => !l.eval x) (l.toProtocol i₀) (r.toProtocol i₀)

theorem toProtocol_solves (i₀ : Fin n) :
    ∀ F : Formula n, (F.toProtocol i₀).SolvesKW F.eval
  | lit i b => by
    intro x y hx hy
    simp only [toProtocol, Protocol.run, eval_lit] at *
    intro heq
    rw [heq] at hx
    exact Bool.noConfusion (hx.symm.trans hy)
  | const b => by
    intro x y hx hy
    simp only [eval_const] at hx hy
    rw [hx] at hy
    exact Bool.noConfusion hy
  | and l r => by
    intro x y hx hy
    simp only [toProtocol, Protocol.run, eval_and, Bool.and_eq_true] at *
    by_cases hl : l.eval y = true
    · have hr : r.eval y = false := by cases h : r.eval y <;> simp_all
      simp only [hl]
      exact toProtocol_solves i₀ r x y hx.2 hr
    · simp only [hl]
      exact toProtocol_solves i₀ l x y hx.1 (by simpa using hl)
  | or l r => by
    intro x y hx hy
    simp only [toProtocol, Protocol.run, eval_or, Bool.or_eq_false_iff] at *
    by_cases hl : l.eval x = true
    · simp only [hl, Bool.not_true]
      exact toProtocol_solves i₀ l x y hl hy.1
    · have hr : r.eval x = true := by cases h : r.eval x <;> simp_all
      simp only [hl, Bool.not_false]
      exact toProtocol_solves i₀ r x y hr hy.2

@[simp] theorem depth_toProtocol (i₀ : Fin n) : ∀ F : Formula n, (F.toProtocol i₀).depth = F.depth
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by simp [toProtocol, Protocol.depth, depth, depth_toProtocol i₀ l, depth_toProtocol i₀ r]
  | or l r => by simp [toProtocol, Protocol.depth, depth, depth_toProtocol i₀ l, depth_toProtocol i₀ r]

@[simp] theorem leaves_toProtocol (i₀ : Fin n) :
    ∀ F : Formula n, (F.toProtocol i₀).leaves = F.leaves
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by
    simp [toProtocol, Protocol.leaves, leaves, leaves_toProtocol i₀ l, leaves_toProtocol i₀ r]
  | or l r => by
    simp [toProtocol, Protocol.leaves, leaves, leaves_toProtocol i₀ l, leaves_toProtocol i₀ r]

end Formula

/-! ### From protocols to formulas -/

namespace Protocol

variable {n : Nat}

/-- The formula of a protocol, relative to the rectangle `A × B` of inputs
reaching the current node: OR at Alice's nodes, AND at Bob's nodes, and at a
leaf naming `i` the literal that is `1` on `A` and `0` on `B`. -/
noncomputable def toFormula :
    Protocol n → ((Fin n → Bool) → Prop) → ((Fin n → Bool) → Prop) → Formula n
  | answer i, A, B =>
      if ∃ y, B y then
        (if ∃ x, A x ∧ x i = true then .lit i true
          else if ∃ x, A x then .lit i false else .const false)
      else .const true
  | alice c l r, A, B =>
      .or (l.toFormula (fun x => A x ∧ c x = false) B) (r.toFormula (fun x => A x ∧ c x = true) B)
  | bob c l r, A, B =>
      .and (l.toFormula A fun y => B y ∧ c y = false) (r.toFormula A fun y => B y ∧ c y = true)

/-- The formula of a protocol solving the game on `A × B` is `1` on `A` and `0` on `B`. -/
theorem toFormula_spec :
    ∀ (P : Protocol n) (A B : (Fin n → Bool) → Prop), P.Solves A B →
      (∀ x, A x → (P.toFormula A B).eval x = true) ∧ (∀ y, B y → (P.toFormula A B).eval y = false)
  | answer i, A, B, h => by
    simp only [toFormula]
    by_cases hB : ∃ y, B y
    · obtain ⟨y, hy⟩ := hB
      simp only [show ∃ y, B y from ⟨y, hy⟩, ↓reduceIte]
      by_cases hA1 : ∃ x, A x ∧ x i = true
      · obtain ⟨x₀, hx₀, hx₀i⟩ := hA1
        simp only [show ∃ x, A x ∧ x i = true from ⟨x₀, hx₀, hx₀i⟩, ↓reduceIte]
        have h₀ := h x₀ y hx₀ hy
        simp only [run] at h₀
        refine ⟨fun x hx => ?_, fun y' hy' => ?_⟩
        · have h₁ := h x y hx hy
          simp only [run] at h₁
          simp only [Formula.eval_lit]
          cases hxi : x i <;> cases hyi : y i <;> simp_all
        · have h₁ := h x₀ y' hx₀ hy'
          simp only [run] at h₁
          simp only [Formula.eval_lit]
          cases hyi : y' i <;> simp_all
      · simp only [hA1, ↓reduceIte]
        by_cases hA : ∃ x, A x
        · obtain ⟨x₀, hx₀⟩ := hA
          simp only [show ∃ x, A x from ⟨x₀, hx₀⟩, ↓reduceIte]
          have hx₀i : x₀ i = false := by
            cases hx : x₀ i
            · rfl
            · exact absurd ⟨x₀, hx₀, hx⟩ hA1
          refine ⟨fun x hx => ?_, fun y' hy' => ?_⟩
          · have hxi : x i = false := by
              cases hxx : x i
              · rfl
              · exact absurd ⟨x, hx, hxx⟩ hA1
            simp [Formula.eval_lit, hxi]
          · have h₁ := h x₀ y' hx₀ hy'
            simp only [run] at h₁
            simp only [Formula.eval_lit]
            cases hyi : y' i <;> simp_all
        · simp only [hA, ↓reduceIte]
          exact ⟨fun x hx => absurd ⟨x, hx⟩ hA, fun _ _ => rfl⟩
    · simp only [hB, ↓reduceIte]
      exact ⟨fun _ _ => rfl, fun y hy => absurd ⟨y, hy⟩ hB⟩
  | alice c l r, A, B, h => by
    have hl := toFormula_spec l (fun x => A x ∧ c x = false) B (by
      intro x y hx hy
      have := h x y hx.1 hy
      simpa only [run, hx.2, Bool.false_eq_true, ↓reduceIte] using this)
    have hr := toFormula_spec r (fun x => A x ∧ c x = true) B (by
      intro x y hx hy
      have := h x y hx.1 hy
      simpa only [run, hx.2, ↓reduceIte] using this)
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · simp only [toFormula, Formula.eval_or, Bool.or_eq_true]
      cases hc : c x
      · exact Or.inl (hl.1 x ⟨hx, hc⟩)
      · exact Or.inr (hr.1 x ⟨hx, hc⟩)
    · simp only [toFormula, Formula.eval_or, hl.2 y hy, hr.2 y hy, Bool.or_self]
  | bob c l r, A, B, h => by
    have hl := toFormula_spec l A (fun y => B y ∧ c y = false) (by
      intro x y hx hy
      have := h x y hx hy.1
      simpa only [run, hy.2, Bool.false_eq_true, ↓reduceIte] using this)
    have hr := toFormula_spec r A (fun y => B y ∧ c y = true) (by
      intro x y hx hy
      have := h x y hx hy.1
      simpa only [run, hy.2, ↓reduceIte] using this)
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · simp only [toFormula, Formula.eval_and, hl.1 x hx, hr.1 x hx, Bool.and_self]
    · simp only [toFormula, Formula.eval_and, Bool.and_eq_false_iff]
      cases hc : c y
      · exact Or.inl (hl.2 y ⟨hy, hc⟩)
      · exact Or.inr (hr.2 y ⟨hy, hc⟩)

@[simp] theorem depth_toFormula :
    ∀ (P : Protocol n) (A B : (Fin n → Bool) → Prop), (P.toFormula A B).depth = P.depth
  | answer _, _, _ => by
    simp only [toFormula]
    split_ifs <;> rfl
  | alice _ l r, A, B => by
    simp [toFormula, Formula.depth, depth, depth_toFormula l, depth_toFormula r]
  | bob _ l r, A, B => by
    simp [toFormula, Formula.depth, depth, depth_toFormula l, depth_toFormula r]

@[simp] theorem leaves_toFormula :
    ∀ (P : Protocol n) (A B : (Fin n → Bool) → Prop), (P.toFormula A B).leaves = P.leaves
  | answer _, _, _ => by
    simp only [toFormula]
    split_ifs <;> rfl
  | alice _ l r, A, B => by
    simp [toFormula, Formula.leaves, leaves, leaves_toFormula l, leaves_toFormula r]
  | bob _ l r, A, B => by
    simp [toFormula, Formula.leaves, leaves, leaves_toFormula l, leaves_toFormula r]

/-- A protocol for the game of `f` yields a formula for `f` of the same shape. -/
theorem exists_formula_of_solvesKW {P : Protocol n} {f : Cslib.BooleanFunction n}
    (h : P.SolvesKW f) :
    ∃ F : Formula n, F.Computes f ∧ F.depth = P.depth ∧ F.leaves = P.leaves := by
  refine ⟨P.toFormula (fun x => f x = true) (fun y => f y = false), ?_, depth_toFormula _ _ _,
    leaves_toFormula _ _ _⟩
  obtain ⟨h₁, h₀⟩ := toFormula_spec P _ _ h
  intro x
  cases hx : f x
  · exact h₀ x hx
  · exact h₁ x hx

end Protocol

/-! ### The Karchmer–Wigderson theorem -/

variable {n : Nat}

/-- A formula for `f` yields a protocol for its game of the same shape. -/
theorem Formula.exists_protocol_of_computes (i₀ : Fin n) {F : Formula n}
    {f : Cslib.BooleanFunction n} (h : F.Computes f) :
    ∃ P : Protocol n, P.SolvesKW f ∧ P.depth = F.depth ∧ P.leaves = F.leaves := by
  refine ⟨F.toProtocol i₀, ?_, Formula.depth_toProtocol i₀ F, Formula.leaves_toProtocol i₀ F⟩
  have := F.toProtocol_solves i₀
  rwa [show F.eval = f from funext h] at this

/-- The minimum depth of a formula computing `f`. -/
noncomputable def formulaDepth (f : Cslib.BooleanFunction n) : ℕ∞ :=
  ⨅ F : {F : Formula n // F.Computes f}, (F.1.depth : ℕ∞)

/-- The minimum number of leaves of a formula computing `f`. -/
noncomputable def formulaSize (f : Cslib.BooleanFunction n) : ℕ∞ :=
  ⨅ F : {F : Formula n // F.Computes f}, (F.1.leaves : ℕ∞)

/-- The minimum depth of a protocol for the game of `f`. -/
noncomputable def protocolDepth (f : Cslib.BooleanFunction n) : ℕ∞ :=
  ⨅ P : {P : Protocol n // P.SolvesKW f}, (P.1.depth : ℕ∞)

/-- The minimum number of leaves of a protocol for the game of `f`. -/
noncomputable def protocolSize (f : Cslib.BooleanFunction n) : ℕ∞ :=
  ⨅ P : {P : Protocol n // P.SolvesKW f}, (P.1.leaves : ℕ∞)

theorem formulaDepth_le {F : Formula n} {f : Cslib.BooleanFunction n} (h : F.Computes f) :
    formulaDepth f ≤ F.depth :=
  iInf_le (fun F : {F : Formula n // F.Computes f} => (F.1.depth : ℕ∞)) ⟨F, h⟩

theorem formulaSize_le {F : Formula n} {f : Cslib.BooleanFunction n} (h : F.Computes f) :
    formulaSize f ≤ F.leaves :=
  iInf_le (fun F : {F : Formula n // F.Computes f} => (F.1.leaves : ℕ∞)) ⟨F, h⟩

theorem protocolDepth_le {P : Protocol n} {f : Cslib.BooleanFunction n} (h : P.SolvesKW f) :
    protocolDepth f ≤ P.depth :=
  iInf_le (fun P : {P : Protocol n // P.SolvesKW f} => (P.1.depth : ℕ∞)) ⟨P, h⟩

theorem protocolSize_le {P : Protocol n} {f : Cslib.BooleanFunction n} (h : P.SolvesKW f) :
    protocolSize f ≤ P.leaves :=
  iInf_le (fun P : {P : Protocol n // P.SolvesKW f} => (P.1.leaves : ℕ∞)) ⟨P, h⟩

/-- **Karchmer–Wigderson, depth.** For `n ≥ 1`, the minimum formula depth of `f`
is the minimum depth of a protocol for its game. -/
theorem formulaDepth_eq_protocolDepth [NeZero n] (f : Cslib.BooleanFunction n) :
    formulaDepth f = protocolDepth f := by
  apply le_antisymm
  · apply le_iInf
    rintro ⟨P, hP⟩
    obtain ⟨F, hF, hd, _⟩ := Protocol.exists_formula_of_solvesKW hP
    exact (formulaDepth_le hF).trans (by rw [hd])
  · apply le_iInf
    rintro ⟨F, hF⟩
    obtain ⟨P, hP, hd, _⟩ := Formula.exists_protocol_of_computes (0 : Fin n) hF
    exact (protocolDepth_le hP).trans (by rw [hd])

/-- **Karchmer–Wigderson, size.** For `n ≥ 1`, the minimum leaf size of a formula
for `f` is the minimum number of leaves of a protocol for its game. -/
theorem formulaSize_eq_protocolSize [NeZero n] (f : Cslib.BooleanFunction n) :
    formulaSize f = protocolSize f := by
  apply le_antisymm
  · apply le_iInf
    rintro ⟨P, hP⟩
    obtain ⟨F, hF, _, hl⟩ := Protocol.exists_formula_of_solvesKW hP
    exact (formulaSize_le hF).trans (by rw [hl])
  · apply le_iInf
    rintro ⟨F, hF⟩
    obtain ⟨P, hP, _, hl⟩ := Formula.exists_protocol_of_computes (0 : Fin n) hF
    exact (protocolSize_le hP).trans (by rw [hl])

end KW
end Algebraic
