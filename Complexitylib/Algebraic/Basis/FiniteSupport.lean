/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Finset.NAry

/-!
# Finite-support semantics

`FiniteSupport M` is the idempotent support carrier used by monotone
arithmetic interpretations.  Addition unions supports, while multiplication
takes all pairwise products.  No algebraic laws on `M` are imposed here: the
arithmetic circuit syntax only needs total binary operations, and concrete
applications can add monoid or exponent-vector structure as needed.
-/

@[expose] public section

namespace Algebraic

/-- A semantic value represented only by its finite set of monomials. -/
structure FiniteSupport (M : Type u) where
  /-- Monomials present with nonzero coefficient. -/
  monomials : Finset M
  deriving DecidableEq

namespace FiniteSupport

/-- The support consisting of one monomial. -/
def singleton
    (monomial : M) : FiniteSupport M :=
  ⟨{monomial}⟩

/-- The empty support. -/
def empty (M : Type u) : FiniteSupport M :=
  ⟨∅⟩

instance [DecidableEq M] : Add (FiniteSupport M) where
  add left right := ⟨left.monomials ∪ right.monomials⟩

instance [DecidableEq M] [Mul M] : Mul (FiniteSupport M) where
  mul left right :=
    ⟨left.monomials.image₂ (· * ·) right.monomials⟩

@[simp] theorem monomials_singleton
    (monomial : M) :
    (singleton monomial).monomials = {monomial} := rfl

@[simp] theorem monomials_empty :
    (empty M).monomials = ∅ := rfl

@[simp] theorem monomials_add
    [DecidableEq M]
    (left right : FiniteSupport M) :
    (left + right).monomials = left.monomials ∪ right.monomials := rfl

theorem mem_add
    [DecidableEq M]
    (monomial : M)
    (left right : FiniteSupport M) :
    monomial ∈ (left + right).monomials ↔
      monomial ∈ left.monomials ∨ monomial ∈ right.monomials := by
  simp

@[simp] theorem monomials_mul
    [DecidableEq M]
    [Mul M]
    (left right : FiniteSupport M) :
    (left * right).monomials =
      left.monomials.image₂ (· * ·) right.monomials := rfl

theorem mem_mul
    [DecidableEq M]
    [Mul M]
    (monomial : M)
    (left right : FiniteSupport M) :
    monomial ∈ (left * right).monomials ↔
      ∃ leftMonomial ∈ left.monomials,
        ∃ rightMonomial ∈ right.monomials,
          leftMonomial * rightMonomial = monomial := by
  simp

/-- Pairwise multiplication produces at most the Cartesian-product number of
monomials. -/
theorem card_mul_le
    [DecidableEq M]
    [Mul M]
    (left right : FiniteSupport M) :
    (left * right).monomials.card ≤
      left.monomials.card * right.monomials.card := by
  exact Finset.card_image₂_le _ _ _

end FiniteSupport
end Algebraic
