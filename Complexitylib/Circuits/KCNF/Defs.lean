/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.NormalForm.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Powerset

/-!
# Clause sets, subcubes, isolation and the PPZ decoder -- definitions

A *clause set* over `N` variables is a finite set of clauses, each a finite set of literals
(`ClauseSet N`). It is the set-based form of `Complexity.CNF`, used by the
satisfiability-coding lemma of Paturi, Pudlák and Zane and by the sparsification lemma of
Impagliazzo, Paturi and Zane. `CNF.toClauseSet` converts a CNF, preserving its semantics
(`CNF.eval`) and not increasing its width.

## Main definitions

* `ClauseSet.Sat`, `ClauseSet.solutions`: satisfaction and the solution set.
* `ClauseSet.occurrences`, `ClauseSet.neighbors`: the number of clauses mentioning a variable,
  and the neighbours of a variable in the co-occurrence graph (two distinct variables are
  adjacent when some clause mentions both).
* `BitString.flipOn x T`: the point `x ⊕ e_T`, flipping the coordinates in `T`.
* `ContainsSubcube S d`: `S` contains a subcube `{a ⊕ e_T : T ⊆ J}` with `|J| = d`.
* `isolatedDirections S x`: the directions `i` with `x ⊕ e_i ∉ S`.
* `ClauseSet.forced ψ σ x`: for an order `σ` of the variables (a permutation: variable `v` is
  placed at position `σ v`), the variables at which the first rule of the PPZ decoder fires on
  input `x`: some clause has a literal on `v`, and all its other literals are on variables placed
  before `v` and are false under `x`.
* `ClauseSet.decode ψ σ y`: the PPZ decoder. It processes the variables in the order `σ`; at `v`,
  if the first rule fires on the values already decoded, it sets `v` to satisfy a forcing
  literal, and otherwise it copies `y v`.
-/

@[expose] public section

namespace Complexity

open Finset

variable {N : ℕ}

/-- Literals over `N` variables are pairs of a variable and a polarity. -/
def Literal.equivProd : Literal N ≃ Fin N × Bool where
  toFun l := (l.var, l.polarity)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (Literal N) := Fintype.ofEquiv _ Literal.equivProd.symm

/-- There are `2 N` literals over `N` variables. -/
theorem Literal.card_literal : Fintype.card (Literal N) = 2 * N := by
  rw [Fintype.card_congr Literal.equivProd, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, mul_comm]

/-- A *clause set* over `N` variables: a finite set of clauses, each a finite set of literals.
A clause is satisfied when one of its literals is true; a clause set when all its clauses
are. -/
abbrev ClauseSet (N : ℕ) := Finset (Finset (Literal N))

namespace ClauseSet

/-- `x` satisfies every clause of `ψ`. -/
def Sat (ψ : ClauseSet N) (x : BitString N) : Prop :=
  ∀ C ∈ ψ, ∃ l ∈ C, l.eval x = true

instance (ψ : ClauseSet N) : DecidablePred ψ.Sat := fun _ => by
  unfold Sat; infer_instance

/-- The solution set of a clause set. -/
def solutions (ψ : ClauseSet N) : Finset (BitString N) :=
  univ.filter ψ.Sat

/-- The number of clauses of `ψ` that mention the variable `v`. -/
def occurrences (ψ : ClauseSet N) (v : Fin N) : ℕ :=
  (ψ.filter fun C => ∃ l ∈ C, l.var = v).card

/-- The neighbours of `u` in the co-occurrence graph of `ψ`: the variables `w ≠ u` such that some
clause of `ψ` mentions both `u` and `w`. -/
def neighbors (ψ : ClauseSet N) (u : Fin N) : Finset (Fin N) :=
  univ.filter fun w => w ≠ u ∧ ∃ C ∈ ψ, (∃ l ∈ C, l.var = u) ∧ ∃ l ∈ C, l.var = w

end ClauseSet

/-- The clause set of a CNF: each clause becomes the set of its literals. -/
def CNF.toClauseSet (φ : CNF N) : ClauseSet N :=
  (φ.clauses.map List.toFinset).toFinset

/-- `x ⊕ e_T`: flip the coordinates of `x` in `T`. -/
def BitString.flipOn (x : BitString N) (T : Finset (Fin N)) : BitString N :=
  fun i => if i ∈ T then !x i else x i

/-- `S` contains a subcube of dimension `d`: some base point `a` and some set `J` of `d`
coordinates have `a ⊕ e_T ∈ S` for every `T ⊆ J`. -/
def ContainsSubcube (S : Set (BitString N)) (d : ℕ) : Prop :=
  ∃ (a : BitString N) (J : Finset (Fin N)), J.card = d ∧ ∀ T ⊆ J, a.flipOn T ∈ S

/-- The *isolated directions* of `x` in `S`: the coordinates `i` with `x ⊕ e_i ∉ S`. -/
def isolatedDirections (S : Finset (BitString N)) (x : BitString N) : Finset (Fin N) :=
  univ.filter fun i => x.flipOn {i} ∉ S

namespace ClauseSet

/-- The variables *forced* on input `x` for the order `σ`: those at which the first rule of the
decoder fires when the earlier variables carry the values of `x`. -/
def forced (ψ : ClauseSet N) (σ : Equiv.Perm (Fin N)) (x : BitString N) : Finset (Fin N) :=
  univ.filter fun v => ∃ C ∈ ψ, ∃ l ∈ C, l.var = v ∧
    ∀ l' ∈ C, l' ≠ l → σ l'.var < σ v ∧ l'.eval x = false

/-- The value the decoder gives to `v` on the partial assignment `z` with default bit `b`: the
polarity of a forcing literal if the first rule fires (`true` if some forcing literal is
positive), and `b` otherwise. -/
def decodeValue (ψ : ClauseSet N) (σ : Equiv.Perm (Fin N)) (z : BitString N) (v : Fin N)
    (b : Bool) : Bool :=
  if ∃ C ∈ ψ, ∃ l ∈ C, l.var = v ∧ ∀ l' ∈ C, l' ≠ l → σ l'.var < σ v ∧ l'.eval z = false then
    decide (∃ C ∈ ψ, ∃ l ∈ C, l.var = v ∧ l.polarity = true ∧
      ∀ l' ∈ C, l' ≠ l → σ l'.var < σ v ∧ l'.eval z = false)
  else b

/-- The decoder after processing the first `p` positions of `σ`: positions `< p` carry decoded
values and the others still carry the input `y`. -/
def decodeUpTo (ψ : ClauseSet N) (σ : Equiv.Perm (Fin N)) (y : BitString N) :
    ℕ → BitString N
  | 0 => y
  | p + 1 =>
    if h : p < N then
      Function.update (decodeUpTo ψ σ y p) (σ.symm ⟨p, h⟩)
        (decodeValue ψ σ (decodeUpTo ψ σ y p) (σ.symm ⟨p, h⟩) (y (σ.symm ⟨p, h⟩)))
    else decodeUpTo ψ σ y p

/-- The PPZ decoder for the order `σ`, run on the input `y`. -/
def decode (ψ : ClauseSet N) (σ : Equiv.Perm (Fin N)) (y : BitString N) : BitString N :=
  decodeUpTo ψ σ y N

end ClauseSet

end Complexity
