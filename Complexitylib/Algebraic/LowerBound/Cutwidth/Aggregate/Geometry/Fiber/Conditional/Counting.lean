/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Conjunction.Basic

/-!
# Literal counts on a large conjunction majority fiber

Within the product of three-state majority pairs, forcing `d` distinct signed
coordinates retains at most `(2/3)^d` of all inputs. This applies to any remaining
conjunction, without an independence assumption about its output.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional

open Entropy Joint
open scoped BigOperators Classical

/-- Fixing selected coordinates inside the majority event incurs a two-thirds cost per bit. -/
theorem three_pow_mul_card_le_of_forces {E V : Type*} [Fintype E] [Fintype V]
    (edge : E → SignedEdge V) (disjoint : Function.Injective (endpoint edge))
    (S : Finset V) (bits : V → Bool) (P : (V → Bool) → Prop) [DecidablePred P]
    (forces : ∀ x, P x → ∀ v ∈ S, x v = bits v) :
    3 ^ S.card *
      (Finset.univ.filter fun x : {x // x ∈ majorityInputs edge} => P x.val).card ≤
      2 ^ S.card * (majorityInputs edge).card := by
  let mask (v : V) : Bool := decide (v ∈ S)
  have count := Internal.constrained_count edge disjoint mask bits
  have selected : (∑ v, if mask v then 1 else 0) = S.card := by simp [mask]
  rw [selected] at count
  let liftInput : {x : {x // x ∈ majorityInputs edge} // P x.val} →
      {x : V → Bool // (∀ e, (edge e).eval x = false) ∧
        ∀ v, mask v = true → x v = bits v} := fun x =>
    ⟨x.val.val, (mem_majorityInputs edge _).mp x.val.property,
      fun v hv => forces x.val.val x.property v (by simpa [mask] using hv)⟩
  have injective : Function.Injective liftInput := by
    intro x y same
    apply Subtype.ext
    apply Subtype.ext
    have point := congrArg Subtype.val same
    exact point
  have smaller := Fintype.card_le_of_injective liftInput injective
  rw [← Fintype.card_subtype]
  exact le_trans (Nat.mul_le_mul_left _ smaller) count

/-- Any `d` distinct literals in a conjunction retain at most a `(2/3)^d` fraction. -/
theorem three_pow_mul_card_evalLiterals_le {E V : Type*} [Fintype E] [Fintype V]
    [DecidableEq V] (edge : E → SignedEdge V)
    (disjoint : Function.Injective (endpoint edge)) {L : Finset (V × Bool)}
    {d : ℕ} (many : d ≤ (literalVars L).card) :
    3 ^ d * (Finset.univ.filter fun x : {x // x ∈ majorityInputs edge} =>
      evalLiterals L x.val = true).card ≤ 2 ^ d * (majorityInputs edge).card := by
  obtain ⟨S, contained, size⟩ := Finset.exists_subset_card_eq many
  choose sign present using fun v : S => mem_literalVars.mp (contained v.property)
  let bits (v : V) : Bool := if hv : v ∈ S then sign ⟨v, hv⟩ else false
  have forced (x : V → Bool) (hx : evalLiterals L x = true) (v : V) (hv : v ∈ S) :
      x v = bits v := by
    have all : ∀ p ∈ L, x p.1 = p.2 := by
      simpa only [evalLiterals, decide_eq_true_eq] using hx
    simpa only [bits, dite_eq_left hv] using all (v, sign ⟨v, hv⟩) (present ⟨v, hv⟩)
  simpa only [size] using three_pow_mul_card_le_of_forces edge disjoint S bits
    (fun x => evalLiterals L x = true) forced

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional
