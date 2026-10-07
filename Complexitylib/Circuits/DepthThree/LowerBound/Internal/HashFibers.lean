/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HashTriangular
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Basic

/-!
# Unrestricted depth-three lower bound: hash fibers

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/HashFibers.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace BinaryHash

noncomputable section

variable {d r : ℕ}

/-- Identify a nonempty hash fiber with the corresponding kernel fiber. -/
def hashF2FiberEquiv (w : Data d) (hw : w ≠ 0) (a : Output r) :
    {u : Seed d r // hashF2 u w = a} ≃ (Nonpivot (r := r) w hw → F2) where
  toFun u := (triangularEquiv (r := r) w hw u.1).2
  invFun b := ⟨(triangularEquiv (r := r) w hw).symm (a, b), by
    rw [← triangularEquiv_fst w hw]
    exact congrArg Prod.fst
      ((triangularEquiv (r := r) w hw).apply_symm_apply (a, b))⟩
  left_inv u := by
    apply Subtype.ext
    apply (triangularEquiv (r := r) w hw).injective
    change (triangularEquiv (r := r) w hw)
      ((triangularEquiv (r := r) w hw).symm
        (a, (triangularEquiv (r := r) w hw u.1).2)) =
      triangularEquiv (r := r) w hw u.1
    rw [Equiv.apply_symm_apply]
    exact Prod.ext ((triangularEquiv_fst w hw u.1).trans u.2).symm rfl
  right_inv b := by
    change ((triangularEquiv (r := r) w hw)
      ((triangularEquiv (r := r) w hw).symm (a, b))).2 = b
    rw [Equiv.apply_symm_apply]

theorem hashF2_fiber_card (w : Data d) (hw : w ≠ 0) (a : Output r) :
    Fintype.card {u : Seed d r // hashF2 u w = a} = 2 ^ (d - 1) := by
  classical
  calc
    Fintype.card {u : Seed d r // hashF2 u w = a} =
        Fintype.card (Nonpivot (r := r) w hw → F2) :=
      Fintype.card_congr (hashF2FiberEquiv w hw a)
    _ = 2 ^ (d - 1) := by
      change Fintype.card (Nonpivot (r := r) w hw → ZMod 2) = 2 ^ (d - 1)
      rw [Fintype.card_fun, ZMod.card, card_nonpivot (r := r) w hw]

theorem hashF2_surjective (w : Data d) (hw : w ≠ 0) :
    Function.Surjective (fun u : Seed d r => hashF2 u w) := by
  intro a
  let u : {u : Seed d r // hashF2 u w = a} :=
    (hashF2FiberEquiv w hw a).symm (fun _ => 0)
  exact ⟨u.1, u.2⟩

/-- Identify hash collisions with kernel solutions by translation. -/
def hashF2CollisionEquiv (x y : Data d) :
    {u : Seed d r // hashF2 u x = hashF2 u y} ≃
      {u : Seed d r // hashF2 u (x - y) = 0} :=
  Equiv.subtypeEquivRight fun u => by
    rw [hashF2_sub_data, sub_eq_zero]

theorem hashF2_collision_card (x y : Data d) (hxy : x ≠ y) :
    Fintype.card {u : Seed d r // hashF2 u x = hashF2 u y} = 2 ^ (d - 1) := by
  calc
    Fintype.card {u : Seed d r // hashF2 u x = hashF2 u y} =
        Fintype.card {u : Seed d r // hashF2 u (x - y) = 0} :=
      Fintype.card_congr (hashF2CollisionEquiv (r := r) x y)
    _ = 2 ^ (d - 1) :=
      hashF2_fiber_card (x - y) (sub_ne_zero.mpr hxy) 0

end

end BinaryHash
end DepthThreeLowerBound

end Complexity
