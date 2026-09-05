/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.RegularGraph
public import Mathlib.Data.ZMod.Basic

/-!
# The Margulis generators

The Margulis–Gabber–Galil graph on `ZMod m × ZMod m` is eight-regular: a vertex
`(x, y)` is joined to the images of eight explicit affine maps. The maps come in
four inverse pairs, which is what makes the rotation map an involution — the
edge leaving by generator `i` arrives by its partner.

This module sets up the generators and that pairing. The spectral bound is
elsewhere.

## Main definitions

- `Complexity.margGen` — the eight generators
- `Complexity.margPair` — the pairing of a generator with its inverse
- `Complexity.margEquiv` — `Fin (m * m)` as `ZMod m × ZMod m`
- `Complexity.margRot` — the resulting rotation map

## Main results

- `Complexity.margGen_pair` — partnered generators undo each other
- `Complexity.margRot_involutive` — the rotation map is an involution
-/

@[expose] public section

namespace Complexity

variable {m : ℕ}

/-- The eight Margulis generators of `ZMod m × ZMod m`. -/
def margGen (i : Fin 8) (v : ZMod m × ZMod m) : ZMod m × ZMod m :=
  ![(v.1 + v.2, v.2), (v.1 - v.2, v.2),
    (v.1, v.2 + v.1), (v.1, v.2 - v.1),
    (v.1 + v.2 + 1, v.2), (v.1 - v.2 - 1, v.2),
    (v.1, v.2 + v.1 + 1), (v.1, v.2 - v.1 - 1)] i

/-- The generator that undoes a given one. -/
def margPair (i : Fin 8) : Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6] i

@[simp] theorem margPair_pair (i : Fin 8) : margPair (margPair i) = i := by
  fin_cases i <;> rfl

/-- **Partnered generators undo each other.** -/
theorem margGen_pair (i : Fin 8) (v : ZMod m × ZMod m) :
    margGen (margPair i) (margGen i v) = v := by
  fin_cases i <;> simp [margGen, margPair, Prod.ext_iff] <;> ring

/-! ### The rotation map -/

/-- `Fin (m * m)` viewed as the group `ZMod m × ZMod m`. -/
def margEquiv (m : ℕ) [NeZero m] : Fin (m * m) ≃ ZMod m × ZMod m :=
  finProdFinEquiv.symm.trans ((ZMod.finEquiv m).toEquiv.prodCongr (ZMod.finEquiv m).toEquiv)

/-- The Margulis rotation map: leave by generator `i`, arrive by its partner.
On the empty vertex set (`m = 0`) it is the identity. -/
def margRot (m : ℕ) (p : Fin (m * m) × Fin 8) : Fin (m * m) × Fin 8 :=
  if h : m = 0 then p else
    haveI : NeZero m := ⟨h⟩
    ((margEquiv m).symm (margGen p.2 (margEquiv m p.1)), margPair p.2)

/-- **The Margulis rotation map is an involution.** -/
theorem margRot_involutive (m : ℕ) : Function.Involutive (margRot m) := by
  intro p
  by_cases h : m = 0
  · simp [margRot, h]
  · have : NeZero m := ⟨h⟩
    simp only [margRot, dite_eq_right h, Equiv.apply_symm_apply, margGen_pair, margPair_pair,
      Equiv.symm_apply_apply]

end Complexity
