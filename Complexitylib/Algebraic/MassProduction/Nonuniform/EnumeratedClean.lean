/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.CollisionTail

/-!
# From point conflicts to disjoint recovery sets

Finite point slots represent each request's recovery set; invalid slots are
discarded. If the valid slots of one request enumerate distinct points,
absence of all point conflicts is exactly the scheduler's `Clean` property.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.EnumeratedClean

variable {Point : Type*} [DecidableEq Point]

/-- The valid point slots of one recovery set. -/
def pointSet (valid : Fin slots → Bool) (points : Fin slots → Point) : Finset Point :=
  (Finset.univ.filter (fun slot => valid slot = true)).image points

/-- Membership is witnessed by a valid point slot. -/
theorem mem_pointSet_iff (valid : Fin slots → Bool) (points : Fin slots → Point) (point : Point) :
    point ∈ pointSet valid points ↔ ∃ slot, valid slot = true ∧ points slot = point := by
  simp [pointSet]

/-- A valid slot conflicts with another valid record or an occupied point. -/
def Conflict (valid : Fin requests → Fin slots → Bool)
    (points : Fin requests → Fin slots → Point) (occupied : Finset Point)
    (request : Fin requests) (slot : Fin slots) : Prop :=
  valid request slot = true ∧
    ((∃ otherRequest otherSlot, (otherRequest, otherSlot) ≠ (request, slot) ∧
      valid otherRequest otherSlot = true ∧ points otherRequest otherSlot = points request slot) ∨
      points request slot ∈ occupied)

/-- Under valid-slot injectivity, pointwise conflict absence is exactly
disjointness from occupancy and from every other request's recovery set. -/
theorem noConflict_iff_clean
    (valid : Fin requests → Fin slots → Bool)
    (points : Fin requests → Fin slots → Point) (occupied : Finset Point)
    (withinRequest : ∀ request left right, valid request left = true → valid request right = true →
      points request left = points request right → left = right)
    (request : Fin requests) :
    (∀ slot, ¬ Conflict valid points occupied request slot) ↔
      Clean (fun request (_ : Unit) => pointSet (valid request) (points request))
        occupied (fun _ => ()) request := by
  constructor
  · intro noConflict
    constructor
    · apply Finset.disjoint_left.mpr
      intro point inRequest inOccupied
      obtain ⟨slot, validSlot, samePoint⟩ :=
        (mem_pointSet_iff (valid request) (points request) point).mp inRequest
      exact noConflict slot ⟨validSlot, Or.inr (samePoint ▸ inOccupied)⟩
    · intro otherRequest different
      apply Finset.disjoint_left.mpr
      intro point inRequest inOther
      obtain ⟨slot, validSlot, samePoint⟩ :=
        (mem_pointSet_iff (valid request) (points request) point).mp inRequest
      obtain ⟨otherSlot, validOther, sameOther⟩ :=
        (mem_pointSet_iff (valid otherRequest) (points otherRequest) point).mp inOther
      exact noConflict slot ⟨validSlot, Or.inl
        ⟨otherRequest, otherSlot, fun equal => different (congrArg Prod.fst equal),
          validOther, sameOther.trans samePoint.symm⟩⟩
  · intro clean slot conflict
    obtain ⟨validSlot, collision | inOccupied⟩ := conflict
    · obtain ⟨otherRequest, otherSlot, different, validOther, samePoint⟩ := collision
      by_cases sameRequest : otherRequest = request
      · subst otherRequest
        have sameSlot := withinRequest request otherSlot slot validOther validSlot samePoint
        exact different (congrArg (fun slot => (request, slot)) sameSlot)
      · have inRequest : points request slot ∈ pointSet (valid request) (points request) :=
          (mem_pointSet_iff _ _ _).mpr ⟨slot, validSlot, rfl⟩
        have inOther : points request slot ∈ pointSet (valid otherRequest) (points otherRequest) :=
          (mem_pointSet_iff _ _ _).mpr ⟨otherSlot, validOther, samePoint⟩
        exact Finset.disjoint_left.mp (clean.2 otherRequest sameRequest) inRequest inOther
    · have inRequest : points request slot ∈ pointSet (valid request) (points request) :=
        (mem_pointSet_iff _ _ _).mpr ⟨slot, validSlot, rfl⟩
      exact Finset.disjoint_left.mp clean.1 inRequest inOccupied

end Algebraic.MassProduction.Nonuniform.EnumeratedClean
