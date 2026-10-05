/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Ledger.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Aggregate gates

An operation of arity `k` *aggregates* in a commutative monoid `T` when its value is read off a
product of contributions of its arguments: `f x = ψ (∏ i, φ i (x i))`. Unbounded AND, OR, and
parity aggregate in a monoid with two elements, and counting modulo `m` aggregates in `ZMod m`.

If every special gate of a program aggregates in `T`, the special gates have a ledger in the
monoid `T ^ k` of functions from the `k` special gates to `T`
(`Frontier.exists_ledger_of_aggregates`): the contribution of a wire to a special gate is the
product of its contributions to the slots of that gate that read it. So `k` aggregate gates cost
`k log |T|` in the frontier lower bound.

## Main definitions

* `Frontier.Aggregates f T`: the operation `f` aggregates in `T`.

## Main results

* `Frontier.exists_ledger_of_aggregates`: aggregate gates have a ledger.
* `Frontier.aggregates_and`, `aggregates_or`, `aggregates_xor`, `aggregates_countMod`: examples.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits

universe v

variable {U : Type*}

/-- An operation of arity `k` *aggregates* in a commutative monoid `T` when its value is read
off a product of contributions of its arguments. -/
def Aggregates {k : ℕ} (f : (Fin k → U) → U) (T : Type) [CommMonoid T] : Prop :=
  ∃ (φ : Fin k → U → T) (ψ : T → U), ∀ x, f x = ψ (∏ i, φ i (x i))

/-- **Aggregate gates have a ledger.** If every special gate of a program aggregates in `T`,
the special gates have a ledger in the monoid of functions from the special gates to `T`. -/
theorem exists_ledger_of_aggregates [Nonempty U] {σ : Signature.{v}} {n s : ℕ}
    (p : Program σ n s) (I : Interpretation σ U) (special : ℕ → Prop) (T : Type) [CommMonoid T]
    (h : ∀ g : Fin s, special g → Aggregates (I (p.lines g).op) T) :
    Nonempty (Ledger p I special ({g : Fin s // special g} → T)) := by
  classical
  choose φ ψ hφψ using h
  refine ⟨{
    -- A wire contributes to a special gate the product of its contributions to the slots of
    -- that gate that read it.
    contribution := fun w u g => ∏ a with (p.lines g).wires a = w, φ g g.2 a u
    -- The special gate numbered `k` reads off its own coordinate; the other naturals are never
    -- consulted.
    readout := fun m k =>
      if hk : k < s then
        if hs : special k then ψ ⟨k, hk⟩ hs (m ⟨⟨k, hk⟩, hs⟩) else Classical.arbitrary U
      else Classical.arbitrary U
    readout_prod := fun v g hg => ?_ }⟩
  rw [dite_eq_left g.isLt, dite_eq_left hg, Finset.prod_apply, hφψ g hg]
  refine congrArg (ψ g hg) ?_
  -- Group the slots of `g` by the wire they read.
  rw [← Finset.prod_fiberwise Finset.univ (p.lines g).wires]
  refine Finset.prod_congr rfl fun w _ => Finset.prod_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.1 ha).2]

/-- Unbounded AND aggregates in `ZMod 2` under multiplication. -/
theorem aggregates_and (k : ℕ) :
    Aggregates (U := Bool) (k := k) (fun x => decide (∀ i, x i = true)) (ZMod 2) :=
  -- A true argument contributes `1` and a false one `0`: the product is `1` when all are true.
  ⟨fun _ b => if b then 1 else 0, fun t => decide (t = 1), fun x => by simp⟩

/-- Unbounded OR aggregates in `ZMod 2` under multiplication. -/
theorem aggregates_or (k : ℕ) :
    Aggregates (U := Bool) (k := k) (fun x => decide (∃ i, x i = true)) (ZMod 2) :=
  -- A true argument contributes `0` and a false one `1`: the product is `1` when none is true.
  ⟨fun _ b => if b then 0 else 1, fun t => decide (t ≠ 1), fun x => by simp⟩

/-- Unbounded parity aggregates in `ZMod 2` under addition. -/
theorem aggregates_xor (k : ℕ) :
    Aggregates (U := Bool) (k := k)
      (fun x => decide ((∑ i, if x i then (1 : ZMod 2) else 0) = 1)) (Multiplicative (ZMod 2)) :=
  -- A true argument contributes `1` to the sum, a false one `0`.
  ⟨fun _ b => .ofAdd (if b then 1 else 0), fun t => decide (t.toAdd = 1), fun x => by
    simp only [toAdd_prod, toAdd_ofAdd]⟩

/-- Unbounded counting modulo `m` aggregates in `ZMod m` under addition: here the gate tests
whether the number of true arguments lies in a set `R` of residues. -/
theorem aggregates_countMod (k m : ℕ) (R : Set (ZMod m)) [DecidablePred (· ∈ R)] :
    Aggregates (U := Bool) (k := k)
      (fun x => decide ((∑ i, if x i then (1 : ZMod m) else 0) ∈ R)) (Multiplicative (ZMod m)) :=
  -- A true argument contributes `1` to the sum, a false one `0`.
  ⟨fun _ b => .ofAdd (if b then 1 else 0), fun t => decide (t.toAdd ∈ R), fun x => by
    simp only [toAdd_prod, toAdd_ofAdd]⟩

end Complexity.Frontier
