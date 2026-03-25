import Complexitylib.Models.TuringMachine
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Pairing and relation predicates

This file defines a simple injective pairing `pair : List Bool → List Bool → List Bool`
used to encode `(x, y)` as a single binary string for verification by a TM, along with
the shared predicates `PolyBalanced` and `pairLang` used by FNP, FNL, and other
search-problem classes.
-/

/-- Encode a pair of binary strings as a single binary string.
    Each bit of `x` is doubled (`false ↦ [false, false]`, `true ↦ [true, true]`),
    followed by the separator `[false, true]`, followed by `y` verbatim.
    This encoding is injective and computable in linear time. -/
def pair (x y : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ y

@[simp]
theorem pair_nil_eq (y : List Bool) :
    pair [] y = false :: true :: y := by
  simp [pair]

@[simp]
theorem pair_cons_eq (b : Bool) (x y : List Bool) :
    pair (b :: x) y = b :: b :: pair x y := by
  simp [pair, List.append_assoc]

/-- Decode a paired binary string back into two components.
    Left inverse of `pair`: `unpair (pair x y) = (x, y)`.
    Returns `([], [])` for strings not in the image of `pair`. -/
def unpair : List Bool → List Bool × List Bool
  | false :: false :: rest =>
    let (x, y) := unpair rest
    (false :: x, y)
  | true :: true :: rest =>
    let (x, y) := unpair rest
    (true :: x, y)
  | false :: true :: rest => ([], rest)
  | _ => ([], [])

/-- `unpair` is a left inverse of `pair`. -/
@[simp]
theorem unpair_pair (x y : List Bool) : unpair (pair x y) = (x, y) := by
  induction x with
  | nil => rfl
  | cons b x' ih =>
    rw [pair_cons_eq]
    cases b <;> simp only [unpair, ih]

/-- `pair` is injective: if `pair x₁ y₁ = pair x₂ y₂` then `x₁ = x₂` and `y₁ = y₂`. -/
theorem pair_injective {x₁ x₂ : List Bool} {y₁ y₂ : List Bool}
    (h : pair x₁ y₁ = pair x₂ y₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  induction x₁ generalizing x₂ with
  | nil =>
    rw [pair_nil_eq] at h
    cases x₂ with
    | nil =>
      rw [pair_nil_eq] at h
      exact ⟨rfl, (List.cons.inj (List.cons.inj h).2).2⟩
    | cons b x₂' =>
      rw [pair_cons_eq] at h
      have h1 := (List.cons.inj h).1           -- false = b
      have h2 := (List.cons.inj (List.cons.inj h).2).1  -- true = b
      exact absurd (h1.trans h2.symm) Bool.false_ne_true
  | cons b₁ x₁' ih =>
    rw [pair_cons_eq] at h
    cases x₂ with
    | nil =>
      rw [pair_nil_eq] at h
      have h1 := (List.cons.inj h).1           -- b₁ = false
      have h2 := (List.cons.inj (List.cons.inj h).2).1  -- b₁ = true
      exact absurd (h1.symm.trans h2) Bool.false_ne_true
    | cons b₂ x₂' =>
      rw [pair_cons_eq] at h
      have hb := (List.cons.inj h).1           -- b₁ = b₂
      have htail := (List.cons.inj (List.cons.inj h).2).2  -- pair x₁' y₁ = pair x₂' y₂
      have ⟨hx, hy⟩ := ih htail
      subst hb; subst hx
      exact ⟨rfl, hy⟩

/-- A binary relation is **polynomially balanced** if witness length is bounded
    by a polynomial in the input length. This is the standard "short witness"
    condition used in the definitions of NP, FNP, FNL, etc. -/
def PolyBalanced (R : List Bool → List Bool → Prop) : Prop :=
  ∃ p : Polynomial ℕ, ∀ x y, R x y → y.length ≤ p.eval x.length

/-- The **pair language** (verification language) of a binary relation `R`:
    the set of encoded pairs `pair(x, y)` such that `R x y` holds. -/
def pairLang (R : List Bool → List Bool → Prop) : Language :=
  {z | ∃ x y, z = pair x y ∧ R x y}
