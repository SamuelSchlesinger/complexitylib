/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Defs
public import Mathlib.Computability.NFA
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Tactic

/-!
# One-way liveness

OpenAI's relation-product language from *An Exponential Two-Way Deterministic
State Lower Bound for One-Way Liveness* (25 September 2026).
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Model.lean

A letter is a binary relation on `Fin h`. A word is Live when the product of
its relations is nonempty, equivalently when it has a path through all layers.
The alphabet is finite, but its size depends on `h`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

/-- Binary relations, with multiplication following the order of a path. -/
@[ext] structure BRel (H : Type*) where
  /-- Whether a pair of endpoints belongs to the relation. -/
  holds : H → H → Prop
namespace BRel
variable {H : Type*}
instance : One (BRel H) := ⟨⟨Eq⟩⟩
instance : Mul (BRel H) := ⟨fun a b => ⟨fun x z => ∃ y, a.holds x y ∧ b.holds y z⟩⟩
instance : Zero (BRel H) := ⟨⟨fun _ _ => False⟩⟩
@[simp] theorem one_holds (x y : H) : (1 : BRel H).holds x y ↔ x = y := Iff.rfl
@[simp] theorem mul_holds (a b : BRel H) (x z : H) :
    (a * b).holds x z ↔ ∃ y, a.holds x y ∧ b.holds y z := Iff.rfl
@[simp] theorem zero_holds (x y : H) : ¬ (0 : BRel H).holds x y := id
instance : Monoid (BRel H) where
  mul_assoc a b c := by
    ext x z
    change (∃ y, (∃ w, a.holds x w ∧ b.holds w y) ∧ c.holds y z) ↔
      ∃ w, a.holds x w ∧ ∃ y, b.holds w y ∧ c.holds y z
    aesop
  one_mul a := by ext x z; change (∃ y, x = y ∧ a.holds y z) ↔ a.holds x z; simp
  mul_one a := by ext x z; change (∃ y, a.holds x y ∧ y = z) ↔ a.holds x z; simp

/-- The identity relation restricted to a set. -/
def restrictedId (F : Set H) : BRel H := ⟨fun x y => x = y ∧ x ∈ F⟩
/-- The product of the relations has at least one pair of related endpoints. -/
def Live (w : List (BRel H)) : Prop := ∃ x y, w.prod.holds x y
instance [Finite H] : Finite (BRel H) := Finite.of_injective BRel.holds (fun _ _ h => BRel.ext h)

end BRel

/-- The finite alphabet of all binary relations on `h` points. -/
abbrev Alphabet (h : ℕ) := BRel (Fin h)
/-- Words whose relation product is nonempty. -/
def oneWayLiveness (h : ℕ) : Set (List (Alphabet h)) := {w | BRel.Live w}

/-- The ordinary Mathlib NFA for one-way liveness, with `h` states and every
state both initial and accepting. The endmarker model uses three additional states. -/
def livenessNFA (h : ℕ) : NFA (Alphabet h) (Fin h) where
  step q R := {r | R.holds q r}
  start := Set.univ
  accept := Set.univ

end Complexity.FiniteAutomaton
