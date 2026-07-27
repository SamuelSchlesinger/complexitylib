/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Barrington
public import Complexitylib.Circuits.BarringtonS5
public import Complexitylib.Circuits.BarringtonBridge
public import Complexitylib.Circuits.Formula
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Barrington's theorem (representation form)

Assembling the three preceding modules — the abstract move-set
(`Circuits/Barrington.lean`), the `S₅` cycle algebra
(`Circuits/BarringtonS5.lean`), and the width-`5` bridge
(`Circuits/BarringtonBridge.lean`) — this module proves the semantic core of
Barrington's theorem by structural recursion on Boolean formulas: **every Boolean
formula is computed by a width-`5` permutation branching program**, in the sense
that the program evaluates to a fixed nonidentity permutation of `S₅` exactly when
the formula is true and to the identity otherwise.

The recursion follows the connectives directly:
`var`/`tru`/`fls` are the base cases; `neg` flips the target cycle to its inverse;
`conj` is the target-free `AND` gate `BP.Computes_and5`; and `disj` is De Morgan
composed of `AND` and negation. Each step preserves representation through a
genuine `5`-cycle, which is what the commutator-trick `AND` requires.

The length bookkeeping lives in `Circuits/BarringtonLength.lean`, where
length-preserving pointwise conjugation and compact negation sharpen this
semantic recursion to the textbook `4^d` bound. The nonuniform family lift and
converse live in `BarringtonFamily.lean` and `BarringtonConverse.lean`.

## Main results

- `Complexity.Computes_formula` — every formula is representable through any
  chosen `5`-cycle target.
- `Complexity.barrington_representation` — Barrington's theorem, representation
  form: a width-`5` program and a nonidentity `σ ∈ S₅` with `eval = σ ↔ φ` true.
- `Complexity.barrington_boolean` — the Boolean-decision form: a width-`5` program
  and a query point `x` whose orbit under the program's value decides `φ`.
-/

@[expose] public section

open scoped commutatorElement
open Equiv

set_option maxRecDepth 100000

namespace Complexity

/-- **Formula representability.** For every Boolean formula `φ` and every target
    `5`-cycle `c` of `S₅`, there is a width-`5` permutation branching program that
    represents `φ` through `c` — evaluating to `c` when `φ` is true and to the
    identity otherwise. Proved by structural recursion on `φ` using the bridged
    Barrington moves. -/
theorem Computes_formula (φ : BoolFormula) :
    ∀ (c : Perm (Fin 5)), c.IsCycle → orderOf c = 5 →
      ∃ r : BP 5, BP.Computes c r (fun α => BoolFormula.eval α φ) := by
  induction φ with
  | var i => intro c hcc hco; exact ⟨_, BP.Computes_var c i⟩
  | tru => intro c hcc hco; exact ⟨_, BP.Computes_true c⟩
  | fls => intro c hcc hco; exact ⟨_, BP.Computes_false c⟩
  | neg φ ih =>
    intro c hcc hco
    have hci : c⁻¹.IsCycle := hcc.inv
    have hoi : orderOf c⁻¹ = 5 := by rw [orderOf_inv]; exact hco
    obtain ⟨p, hp⟩ := ih c⁻¹ hci hoi
    have h := BP.Computes_not hp
    rw [inv_inv] at h
    exact ⟨_, h⟩
  | conj φ ψ ihφ ihψ =>
    intro c hcc hco
    obtain ⟨p, hp⟩ := ihφ c hcc hco
    obtain ⟨q, hq⟩ := ihψ c hcc hco
    exact BP.Computes_and5 hp hcc hco hq hcc hco hcc hco
  | disj φ ψ ihφ ihψ =>
    intro c hcc hco
    have hci : c⁻¹.IsCycle := hcc.inv
    have hoi : orderOf c⁻¹ = 5 := by rw [orderOf_inv]; exact hco
    obtain ⟨p, hp⟩ := ihφ c hcc hco
    obtain ⟨q, hq⟩ := ihψ c hcc hco
    obtain ⟨s, hs⟩ :=
      BP.Computes_and5 (BP.Computes_not hp) hci hoi (BP.Computes_not hq) hci hoi hci hoi
    have h := BP.Computes_not hs
    rw [inv_inv] at h
    have hfun : (fun α => !((!BoolFormula.eval α φ) && (!BoolFormula.eval α ψ)))
              = (fun α => BoolFormula.eval α φ || BoolFormula.eval α ψ) := by
      funext α; simp [Bool.not_and, Bool.not_not]
    rw [hfun] at h
    exact ⟨_, h⟩

/-- **Barrington's theorem (representation form).** Every Boolean formula `φ` is
    computed by a width-`5` permutation branching program: there is a program `r`
    and a nonidentity permutation `σ ∈ S₅` such that `r` evaluates to `σ` exactly
    when `φ` is true and to the identity otherwise. (The concrete witness cycle is
    `finRotate 5`.) -/
theorem barrington_representation (φ : BoolFormula) :
    ∃ (r : BP 5) (σ : Perm (Fin 5)), σ ≠ 1 ∧
      ∀ α, BP.eval α r = if BoolFormula.eval α φ then σ else 1 := by
  obtain ⟨hc, ho⟩ := isCycle_orderOf_five_of_pow (g := finRotate 5) (by decide) (by decide)
  obtain ⟨r, hr⟩ := Computes_formula φ (finRotate 5) hc ho
  refine ⟨r, finRotate 5, ?_, fun α => hr α⟩
  rw [Ne, ← orderOf_eq_one_iff, ho]; norm_num

/-- **Barrington's theorem (Boolean-decision form).** Every Boolean formula `φ` is
    decided by a width-`5` permutation branching program: there is a program `r`
    and a query point `x ∈ Fin 5` such that the program's value moves `x` exactly
    when `φ` is true. Reading `(BP.eval α r) x ≠ x` therefore computes `φ`,
    turning the permutation-valued representation into a genuine Boolean output.
    (The point `x` is any point the representing cycle `σ` moves; `σ ≠ 1`
    guarantees one exists.) -/
theorem barrington_boolean (φ : BoolFormula) :
    ∃ (r : BP 5) (x : Fin 5), ∀ α, ((BP.eval α r) x ≠ x ↔ BoolFormula.eval α φ = true) := by
  obtain ⟨r, σ, hσ1, hr⟩ := barrington_representation φ
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hσ1 (Equiv.ext h)
  refine ⟨r, x, fun α => ?_⟩
  rw [hr α]
  cases hev : BoolFormula.eval α φ
  · simp
  · simp [hx]

end Complexity
