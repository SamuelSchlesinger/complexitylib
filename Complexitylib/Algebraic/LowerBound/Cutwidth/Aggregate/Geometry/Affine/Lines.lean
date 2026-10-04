/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Basic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Defs

/-!
# Affine behavior of actual signed circuit lines

Affine operations preserve affine inputs. If all internal predecessors are constant,
at most one direct primary variable suffices to make any line affine. A falsified
literal makes a conjunction line constant.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open scoped Classical

variable {n g : Nat} {S : AffineFlat n}

/-- Parity of any finite family of affine Boolean functions is affine. -/
theorem affineOn_xorSum {r : Nat} (fs : Fin r → (Fin n → Bool) → Bool)
    (h : ∀ i, AffineOn S (fs i)) : AffineOn S (fun x => xorSum (fun i => fs i x)) := by
  induction r with
  | zero => exact affineOn_const false
  | succ r ih =>
    change AffineOn S (fun x => fs 0 x ^^ xorSum (fun i => fs i.succ x))
    exact (h 0).xor (ih (fun i => fs i.succ) (fun i => h i.succ))

/-- An actual affine gate preserves affine input functions at every fan-in. -/
theorem affineOn_affineOp {r : Nat} (bias : Bool) (coefficient : Fin r → Bool)
    (fs : Fin r → (Fin n → Bool) → Bool) (h : ∀ i, AffineOn S (fs i)) :
    AffineOn S (fun x => interpretation (.affine r bias coefficient) (fun i => fs i x)) :=
  (affineOn_const bias).xor (affineOn_xorSum _ (fun i => (h i).unary (fun b => coefficient i && b)))

/-- Depending on one primary coordinate makes a Boolean function affine on the flat. -/
theorem affineOn_of_depends_coordinate {f : (Fin n → Bool) → Bool} (i : Fin n)
    (depends : ∀ x ∈ S.carrier, ∀ y ∈ S.carrier, x i = y i → f x = f y) :
    AffineOn S f := by
  classical
  let u (b : Bool) := if h : ∃ x ∈ S.carrier, x i = b then f (Classical.choose h) else false
  have same (x : Fin n → Bool) (hx : x ∈ S.carrier) : u (x i) = f x := by
    have ex : ∃ y ∈ S.carrier, y i = x i := ⟨x, hx, rfl⟩
    simp only [u, ex, dite_true]
    exact depends _ (Classical.choose_spec ex).1 x hx (Classical.choose_spec ex).2
  exact ((affineOn_coordinate i).unary u).congr same

/-- Dependence on at most one coordinate suffices, including the empty support case. -/
theorem affineOn_of_depends_small {f : (Fin n → Bool) → Bool} (U : Finset (Fin n))
    (small : U.card ≤ 1)
    (depends : ∀ x ∈ S.carrier, ∀ y ∈ S.carrier,
      (∀ i ∈ U, x i = y i) → f x = f y) : AffineOn S f := by
  classical
  by_cases empty : U = ∅
  · obtain ⟨a, ha⟩ := S.nonempty
    apply ConstantOn.affine
    exact ⟨f a, fun x hx => depends x hx a ha (by simp [empty])⟩
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    apply affineOn_of_depends_coordinate i
    intro x hx y hy same
    apply depends x hx y hy
    intro j hj
    have : j = i := Finset.card_le_one.mp small j hj i hi
    simpa only [this] using same

/-- The function computed by appending this actual line to the program. -/
def lineFunction (p : Program signature n g) (line : Line signature n g) :
    (Fin n → Bool) → Bool := fun x => line.eval interpretation x (p.eval interpretation x)

/-- Affine gate outputs and original input coordinates cover every actual wire. -/
theorem affineOn_wire (p : Program signature n g)
    (affine : ∀ i, AffineOn S (p.gateFunction interpretation i)) (wire : Wire n g) :
    AffineOn S (p.wireFunction interpretation wire) := by
  cases wire with
  | input i => exact affineOn_coordinate i
  | gate i => exact affine i

/-- A line whose input slots are all constant has constant output. -/
theorem constantOn_line_of_slots (p : Program signature n g) (line : Line signature n g)
    (constant : ∀ slot, ConstantOn S (p.wireFunction interpretation (line.wires slot))) :
    ConstantOn S (lineFunction p line) := by
  obtain ⟨a, ha⟩ := S.nonempty
  refine ⟨lineFunction p line a, fun x hx => ?_⟩
  apply congrArg (interpretation line.op)
  funext slot
  obtain ⟨b, hb⟩ := constant slot
  exact (hb x hx).trans (hb a ha).symm

/-- Once internal predecessors are constant, one primary variable suffices for affineness. -/
theorem affineOn_line_of_small_primary (p : Program signature n g)
    (line : Line signature n g) (small : (primaryInputs line).card ≤ 1)
    (constant : ∀ slot i, line.wires slot = .gate i →
      ConstantOn S (p.gateFunction interpretation i)) : AffineOn S (lineFunction p line) := by
  apply affineOn_of_depends_small (primaryInputs line) small
  intro x hx y hy same
  apply congrArg (interpretation line.op)
  funext slot
  cases hw : line.wires slot with
  | input i =>
      simpa only [Function.comp_apply, hw, Wire.elim] using
        same i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨slot, hw⟩⟩)
  | gate i =>
      obtain ⟨b, hb⟩ := constant slot i hw
      simpa only [Function.comp_apply, hw, Wire.elim, Program.gateFunction_apply] using
        (hb x hx).trans (hb y hy).symm

/-- A controlling input value forces the signed conjunction's output. -/
theorem constantOn_conjunction (p : Program signature n g) {r : Nat}
    (polarity : Fin r → Bool) (negated : Bool) (wires : Fin r → Wire n g) (slot : Fin r)
    (value : ∀ x ∈ S.carrier, p.wireFunction interpretation (wires slot) x = !(polarity slot)) :
    ConstantOn S (lineFunction p ⟨.conjunction r polarity negated, wires⟩) := by
  refine ⟨negated, fun x hx => ?_⟩
  have no : ¬ ∀ i, p.wireFunction interpretation (wires i) x = polarity i := by
    intro all
    have := (value x hx).symm.trans (all slot)
    cases polarity slot <;> simp at this
  change (negated ^^ decide (∀ i, p.wireFunction interpretation (wires i) x = polarity i)) = negated
  simp [no]

end Algebraic.Aggregate.Geometry
