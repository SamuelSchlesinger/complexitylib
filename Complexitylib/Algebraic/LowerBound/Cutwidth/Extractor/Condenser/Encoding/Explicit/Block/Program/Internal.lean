/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit
import Complexitylib.Classes.P.Range
import Complexitylib.Tactic.PolyTime
import Mathlib.Data.List.OfFn

/-!
# Fixed-width correctness and uniformity of one block-condensation level

The exact runtime length is independent of the source bits. Fixed-width
slicing recovers every encoded input block, including blocks of width zero.
Polynomial-time range concatenation then composes the existing uniform
scheduled condenser without fixing the block count or numerical parameters.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity Complexity.BitPolynomial

theorem explicitBlockCondenserBits_length (n k e u : Nat) (blocks seed count : List Bool) :
    (explicitBlockCondenserBits n k e u blocks seed count).length = count.length *
      (condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) *
        sparseFieldBits u (explicitCondenserBudget n k e)) := by
  simp [explicitBlockCondenserBits, explicitCondenserBits_length]

private theorem coefficientBlock_flatten_ofFn (t width : Nat) (blocks : Fin t → List Bool)
    (length : ∀ i, (blocks i).length = width) (i : Fin t) :
    coefficientBlock (List.ofFn blocks).flatten width i.val = blocks i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [coefficientBlock, Fin.val_zero, Nat.zero_mul, List.drop_zero,
        List.ofFn_succ, List.flatten_cons]
      exact List.take_left' (length 0)
    · simp only [coefficientBlock, Fin.val_succ, Nat.add_mul, Nat.one_mul,
        List.ofFn_succ, List.flatten_cons]
      rw [Nat.add_comm (j.val * width) width, ← length 0, List.drop_length_add_append]
      simpa only [coefficientBlock, ← length 0] using
        ih (fun j => blocks j.succ) (fun j => length j.succ) j

theorem explicitBlockCondenserBits_ofFn (n k e u : Nat) {t : Nat}
    (blocks : Fin t → Fin n → Bool) (seed count : List Bool) (size : count.length = t) :
    explicitBlockCondenserBits n k e u
        (List.ofFn (fun i => List.ofFn (blocks i))).flatten seed count =
      (List.ofFn (fun i => explicitCondenserBits n k e u (List.ofFn (blocks i)) seed)).flatten := by
  rw [explicitBlockCondenserBits, size, List.flatMap_def]
  apply congrArg List.flatten
  apply List.ext_getElem (by simp)
  intro j hj _
  have bound : j < t := by simpa using hj
  simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
    congrArg (fun bits => explicitCondenserBits n k e u bits seed)
      (coefficientBlock_flatten_ofFn t n (fun i => List.ofFn (blocks i))
        (fun _ => List.length_ofFn) ⟨j, bound⟩)

theorem explicitBlockCondenserBits_mem_FP {n k e u : List Bool → Nat}
    {blocks seed count : List Bool → List Bool}
    (hn : UnaryFn n) (hk : UnaryFn k) (he : UnaryFn e) (hu : UnaryFn u)
    (hblocks : blocks ∈ FP) (hseed : seed ∈ FP) (hcount : count ∈ FP) :
    (fun z => explicitBlockCondenserBits (n z) (k z) (e z) (u z)
      (blocks z) (seed z) (count z)) ∈ FP := by
  have entry : (fun w => explicitCondenserBits
      (n (pairFst w)) (k (pairFst w)) (e (pairFst w)) (u (pairFst w))
      (coefficientBlock (blocks (pairFst w)) (n (pairFst w)) (pairSnd w).length)
      (seed (pairFst w))) ∈ FP := by
    dsimp only [coefficientBlock]
    polytime
  refine mem_FP_of_eq (flatMap_range_mem_FP entry hcount) fun z => ?_
  simp only [explicitBlockCondenserBits, pairFst_pair, pairSnd_pair, List.length_replicate]

end Algebraic.Cutwidth.Extractor.Internal
