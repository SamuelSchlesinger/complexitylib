/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Level.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Internal.Tuples
import Mathlib.Data.List.OfFn

/-!
# Identifying runtime block output with the deterministic statistical level

Serialization of the pair-splitting equivalence lists each pair's first
coordinate immediately before its second. The two Boolean halves of each
scheduled condenser output reconstruct its entire runtime word. Combining
these identities with fixed-width input correctness identifies the complete
one-level program with `condenseSplitMap`.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem flatten_ofFn_splitBlockEquiv {α β : Type*} (encode : α → List β)
    {t : Nat} (pairs : Fin t → α × α) :
    (List.ofFn fun i => encode (splitBlockEquiv α t pairs i)).flatten =
      (List.ofFn fun i => encode (pairs i).1 ++ encode (pairs i).2).flatten := by
  rw [List.ofFn_mul', List.flatten_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  have coordinate (j : Fin 2) (a : Fin (2 * t)) (index : a.val = 2 * i.val + j.val) :
      splitBlockEquiv α t pairs a = (finTwoArrowEquiv α).symm (pairs i) j := by
    have same : a = splitBlockIndexEquiv t (i, j) := by
      apply Fin.ext
      rw [index, splitBlockIndexEquiv_val, Nat.add_comm]
    rw [same, splitBlockEquiv_apply]
  simp only [Function.comp_apply, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  rw [coordinate 0 _ rfl, coordinate 1 _ rfl]
  rfl

private theorem explicitCondenserPair_reassemble (n k e u : Nat) (x : Fin n → Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    List.ofFn (explicitCondenserPair n k e u x seed).1 ++
      List.ofFn (explicitCondenserPair n k e u x seed).2 =
        explicitCondenserBits n k e u (List.ofFn x)
          (BinaryFieldCodec.encode (sparseFieldExponent u (explicitCondenserBudget n k e))
            seed) := by
  let h := explicitCondenserHalfWidth n k e u
  let bits := explicitCondenserBits n k e u (List.ofFn x)
    (BinaryFieldCodec.encode (sparseFieldExponent u (explicitCondenserBudget n k e)) seed)
  have length : bits.length = h + h := by
    rw [show bits.length = _ from explicitCondenserBits_length n k e u _ _]
    exact (explicitCondenserHalfWidth_double n k e u).symm
  rw [← List.ofFn_fin_append]
  change List.ofFn ((Fin.appendEquiv h h)
    ((Fin.appendEquiv h h).symm (fun i => bits[i.val]?.getD false))) = bits
  rw [Equiv.apply_symm_apply]
  apply List.ext_getElem (by simpa using length.symm)
  intro i _ hi
  simp [hi]

theorem explicitBlockCondenserBits_eq_condenseSplitMap (n k e u : Nat) {t : Nat}
    (blocks : Fin t → Fin n → Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e))))
    (count : List Bool) (size : count.length = t) :
    explicitBlockCondenserBits n k e u
        (List.ofFn (fun i => List.ofFn (blocks i))).flatten
        (BinaryFieldCodec.encode (sparseFieldExponent u (explicitCondenserBudget n k e))
          seed) count =
      (List.ofFn fun i => List.ofFn
        (condenseSplitMap (explicitCondenserPair n k e u) t blocks seed i)).flatten := by
  rw [explicitBlockCondenserBits_ofFn n k e u blocks _ count size]
  unfold condenseSplitMap
  rw [flatten_ofFn_splitBlockEquiv]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact (explicitCondenserPair_reassemble n k e u (blocks i) seed).symm

end Algebraic.Cutwidth.Extractor.Internal
