/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.XOR.Restriction.Defs
public import Complexitylib.Circuits.XOR.Restriction.Internal

/-!
# Parity under finite restrictions

`Schnorr.xorOn support` is parity on an explicit finite set of coordinates.
Fixing one coordinate to zero erases it from the support, while flipping any
supported coordinate complements the result.

The main lower bound says that every finite-arity decision tree computing
parity on `support` has depth at least `support.card`. This is the parity-side
contradiction needed after a switching argument leaves many variables free.
-/

@[expose] public section

namespace Complexity
namespace Schnorr

@[simp] theorem xorOn_empty (input : BitString N) :
    xorOn ∅ input = false :=
  xorOn_empty_internal input

/-- Insert one fresh parity coordinate. -/
theorem xorOn_insert (support : Finset (Fin N))
    (index : Fin N) (hindex : index ∉ support)
    (input : BitString N) :
    xorOn (insert index support) input =
      xorOp (input index) (xorOn support input) :=
  xorOn_insert_internal support index hindex input

/-- Updating a coordinate outside the support does not change parity. -/
theorem xorOn_update_of_not_mem
    (support : Finset (Fin N)) (index : Fin N)
    (hindex : index ∉ support) (value : Bool)
    (input : BitString N) :
    xorOn support (Function.update input index value) =
      xorOn support input :=
  xorOn_update_of_not_mem_internal support index hindex value input

/-- Fixing one coordinate to zero erases it from the parity support. -/
theorem xorOn_update_false_eq_erase
    (support : Finset (Fin N)) (index : Fin N)
    (input : BitString N) :
    xorOn support (Function.update input index false) =
      xorOn (support.erase index) input :=
  xorOn_update_false_eq_erase_internal support index input

/-- Flipping any supported coordinate complements parity. -/
theorem xorOn_flip
    (support : Finset (Fin N)) (index : Fin N)
    (hindex : index ∈ support) (input : BitString N) :
    xorOn support (Function.update input index (!input index)) =
    !(xorOn support input) :=
  xorOn_flip_internal support index hindex input

/-- Parity on the full finite support is the library's existing recursive
`xorBool` function. -/
theorem xorOn_univ_eq_xorBool (input : BitString N) :
    xorOn Finset.univ input = xorBool N input :=
  xorOn_univ_eq_xorBool_internal input

/-- Restricting parity separates into the parity of the fixed coordinates and
the parity of the surviving free coordinates. -/
theorem xorOn_applyTo
    (support : Finset (Fin N))
    (restriction : Restriction.On N)
    (input : BitString N) :
    xorOn support (restriction.applyTo input) =
      xorOp
        (xorOn support
          (restriction.applyTo fun _ => false))
        (xorOn (support.filter fun index =>
          restriction index = none) input) :=
  xorOn_applyTo_internal support restriction input

/-- Full parity under a restriction is parity on exactly the free variables,
possibly complemented by the fixed coordinates. -/
theorem xorBool_applyTo
    (restriction : Restriction.On N)
    (input : BitString N) :
    xorBool N (restriction.applyTo input) =
      xorOp
        (xorBool N
          (restriction.applyTo fun _ => false))
        (xorOn restriction.freeVariables input) :=
  xorBool_applyTo_internal restriction input

/-- A decision tree computing parity on `support` must query to depth at least
the number of supported coordinates. -/
theorem card_support_le_depth
    (tree : DecisionTree.On N) (support : Finset (Fin N))
    (computes : ∀ input, tree.eval input = xorOn support input) :
    support.card ≤ tree.depth :=
  card_support_le_depth_internal tree support computes

/-- Complementing parity by a fixed offset does not reduce its decision-tree
depth. -/
theorem card_support_le_depth_offset
    (tree : DecisionTree.On N)
    (support : Finset (Fin N)) (offset : Bool)
    (computes : ∀ input,
      tree.eval input =
        xorOp offset (xorOn support input)) :
    support.card ≤ tree.depth :=
  card_support_le_depth_offset_internal
    tree support offset computes

/-- Any decision tree computing full parity after a restriction must query at
least the number of coordinates that the restriction leaves free. -/
theorem freeVariables_card_le_depth_of_restricted_xor
    (tree : DecisionTree.On N)
    (restriction : Restriction.On N)
    (computes : ∀ input,
      tree.eval input =
        xorBool N (restriction.applyTo input)) :
    restriction.freeVariables.card ≤ tree.depth :=
  freeVariables_card_le_depth_of_restricted_xor_internal
    tree restriction computes

end Schnorr
end Complexity
