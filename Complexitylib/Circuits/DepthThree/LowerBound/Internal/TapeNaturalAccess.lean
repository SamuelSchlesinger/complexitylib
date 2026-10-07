/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeStoreRepresentation
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitConvolutionUpdates

/-!
# Unrestricted depth-three lower bound: tape natural access

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeNaturalAccess.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeNaturalAccess

open TapeMultiProgram TapeUnary

theorem take_length (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (xs.take i).length = i := List.length_take_of_le hi.le

theorem split (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    xs = xs.take i ++ xs.getD i false :: xs.drop (i + 1) := by
  rw [List.getD_eq_getElem _ _ hi, ← List.drop_eq_getElem_cons hi,
    List.take_append_drop]

theorem xorListAt_eq_split (xs : List Bool) (i : ℕ) (hi : i < xs.length)
    (v : Bool) :
    xorListAt xs i v =
      xs.take i ++ Bool.xor (xs.getD i false) v :: xs.drop (i + 1) := by
  calc
    xorListAt xs i v = xorListAt
        (xs.take i ++ xs.getD i false :: xs.drop (i + 1)) (xs.take i).length v := by
      rw [take_length xs i hi, ← split xs i hi]
    _ = _ := xorListAt_split _ _ _ _

theorem read (index array : TapeRegister) (hne : index ≠ array)
    (σ : TapeStore) (i : ℕ) (hi : σ index = List.replicate i true)
    (hib : i < (σ array).length) :
    RunsIn (TapeArray.code index array id).step
      (cfg TapeArray.State.start (storeTapes σ))
      (cfg (TapeArray.State.done ((σ array).getD i false)) (storeTapes σ))
      (2 * i + 4) := by
  have h := TapeProductTerm.read_at hne (storeTapes σ)
    ((σ array).take i) ((σ array).drop (i + 1)) ((σ array).getD i false)
    (by simp only [storeTapes_apply, hi, counterTape, take_length _ _ hib])
    (congrArg wordTape (split _ _ hib))
  simpa only [take_length _ _ hib] using h

theorem xorAt (index array : TapeRegister) (hne : index ≠ array)
    (σ : TapeStore) (i : ℕ) (v : Bool) (hi : σ index = List.replicate i true)
    (hib : i < (σ array).length) :
    RunsIn (TapeArray.code index array (fun old => Bool.xor old v)).step
      (cfg TapeArray.State.start (storeTapes σ))
      (cfg (TapeArray.State.done ((σ array).getD i false))
        (storeTapes (Function.update σ array (xorListAt (σ array) i v))))
      (2 * i + 4) := by
  have h := TapeProductTerm.modify_at hne (fun old => Bool.xor old v) (storeTapes σ)
    ((σ array).take i) ((σ array).drop (i + 1)) ((σ array).getD i false)
    (by simp only [storeTapes_apply, hi, counterTape, take_length _ _ hib])
    (congrArg wordTape (split _ _ hib))
  simpa only [take_length _ _ hib, storeTapes_update, xorListAt_eq_split _ _ hib] using h

theorem productTerm (ia a ib b ic c : TapeRegister)
    (hia : ia ≠ a) (hib : ib ≠ b) (hic : ic ≠ c)
    (σ : TapeStore) (i j k : ℕ)
    (hi : σ ia = List.replicate i true)
    (hj : σ ib = List.replicate j true)
    (hk : σ ic = List.replicate k true)
    (hAi : i < (σ a).length) (hBj : j < (σ b).length) (hCk : k < (σ c).length) :
    RunsIn (TapeProductTerm.program ia a ib b ic c).step
      (cfg TapeProductTerm.start (storeTapes σ))
      (cfg (TapeProductTerm.done ((σ a).getD i false) ((σ b).getD j false)
          ((σ c).getD k false))
        (storeTapes (Function.update σ c
          (xorListAt (σ c) k ((σ a).getD i false && (σ b).getD j false)))))
      (2 * (i + j + k) + 14) := by
  have h := TapeProductTerm.runs_product_term ia a ib b ic c hia hib hic (storeTapes σ)
    ((σ a).take i) ((σ a).drop (i + 1))
    ((σ b).take j) ((σ b).drop (j + 1))
    ((σ c).take k) ((σ c).drop (k + 1))
    ((σ a).getD i false) ((σ b).getD j false) ((σ c).getD k false)
    (by simp only [storeTapes_apply, hi, counterTape, take_length _ _ hAi])
    (congrArg wordTape (split _ _ hAi))
    (by simp only [storeTapes_apply, hj, counterTape, take_length _ _ hBj])
    (congrArg wordTape (split _ _ hBj))
    (by simp only [storeTapes_apply, hk, counterTape, take_length _ _ hCk])
    (congrArg wordTape (split _ _ hCk))
  simpa only [take_length _ _ hAi, take_length _ _ hBj, take_length _ _ hCk,
    storeTapes_update, xorListAt_eq_split _ _ hCk] using h

end TapeNaturalAccess
end DepthThreeLowerBound

end Complexity
