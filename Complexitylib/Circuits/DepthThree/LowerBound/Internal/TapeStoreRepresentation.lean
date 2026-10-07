/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeErase
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeFill
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeProductTerm

/-!
# Unrestricted depth-three lower bound: tape store representation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeStoreRepresentation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

namespace DepthThreeLowerBound

open TapeMultiProgram TapeCopy TapeUnary TapeArithmetic TapeRouting

/-- Represent every register's bit list by a boundary-marked tape. -/
def storeTapes (σ : TapeStore) : TapeTapes := fun r => wordTape (σ r)

@[simp] theorem storeTapes_apply (σ : TapeStore) (r : TapeRegister) :
    storeTapes σ r = wordTape (σ r) := rfl

theorem storeTapes_update (σ : TapeStore) (r : TapeRegister) (bits : List Bool) :
    storeTapes (Function.update σ r bits) = Function.update (storeTapes σ) r (wordTape bits) := by
  funext s
  by_cases h : s = r
  · subst s
    simp [storeTapes]
  · simp [storeTapes, Function.update, h]

theorem onPair_eq_updates {α : Type uDepth1} {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeRegister → α) (S D : α) :
    onPair src dst T S D = Function.update (Function.update T src S) dst D := by
  funext r
  by_cases hs : r = src
  · subst r
    simp [onPair, Function.update, hne]
  · by_cases hd : r = dst
    · subst r
      simp [onPair, Function.update, Ne.symm hne]
    · simp [onPair, Function.update, hs, hd]

namespace TapeStoreRuns

theorem copy {src dst : TapeRegister} (hne : src ≠ dst) (σ : TapeStore)
    (hempty : σ dst = []) :
    RunsIn (TapeCopy.code src dst).step
      (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes (Function.update σ dst (σ src))))
      (2 * (σ src).length + 4) := by
  have h := TapeCopy.runs_copy hne (storeTapes σ) (σ src)
  have hi : onPair src dst (storeTapes σ) (wordTape (σ src)) (wordTape []) = storeTapes σ :=
    TapeProductTerm.onPair_eq_self rfl (by simp [hempty])
  have ho : onPair src dst (storeTapes σ) (wordTape (σ src)) (wordTape (σ src)) =
      storeTapes (Function.update σ dst (σ src)) := by
    rw [← update_onPair_dst hne (storeTapes σ) (wordTape (σ src)) (wordTape []), hi,
      storeTapes_update]
  simpa only [hi, ho] using h

theorem erase (r : TapeRegister) (σ : TapeStore) :
    RunsIn (TapeErase.code r).step
      (cfg TapeErase.State.start (storeTapes σ))
      (cfg TapeErase.State.done (storeTapes (Function.update σ r [])))
      (2 * (σ r).length + 5) := by
  have h := TapeErase.runs_erase r (storeTapes σ) (σ r)
  simpa only [← storeTapes_update, Function.update_eq_self] using h

theorem push (r : TapeRegister) (b : Bool) (σ : TapeStore) :
    RunsIn (TapeFill.pushProgram r b).step
      (cfg IncState.start (storeTapes σ))
      (cfg IncState.done (storeTapes (Function.update σ r (b :: σ r)))) 2 := by
  simpa only [storeTapes_update] using TapeFill.runs_push r b (storeTapes σ) (σ r) rfl

theorem add {counter destination : TapeRegister} (hne : counter ≠ destination)
    (σ : TapeStore) (n m : ℕ)
    (hc : σ counter = List.replicate n true)
    (hd : σ destination = List.replicate m true) :
    RunsIn (addProgram counter destination).step
      (cfg addStart (storeTapes σ))
      (cfg addDone (storeTapes
        (Function.update (Function.update σ counter []) destination (List.replicate (m + n) true))))
      (8 * n + 3) := by
  have h := runs_add hne (storeTapes σ) n m
  have hi : onPair counter destination (storeTapes σ) (counterTape n) (counterTape m) =
      storeTapes σ := TapeProductTerm.onPair_eq_self (by simp [hc, counterTape])
        (by simp [hd, counterTape])
  have ho : onPair counter destination (storeTapes σ) (counterTape 0) (counterTape (m + n)) =
      storeTapes (Function.update (Function.update σ counter []) destination (List.replicate (m +
        n) true)) := by
    rw [onPair_eq_updates hne]
    simp only [storeTapes_update, counterTape, List.replicate_zero]
  simpa only [hi, ho] using h

theorem fill {counter destination : TapeRegister} (hne : counter ≠ destination)
    (b : Bool) (σ : TapeStore) (n : ℕ) (hc : σ counter = List.replicate n true) :
    RunsIn (TapeFill.fillProgram counter destination b).step
      (cfg TapeFill.fillStart (storeTapes σ))
      (cfg TapeFill.fillDone (storeTapes (Function.update (Function.update σ counter [])
        destination (List.replicate n b ++ σ destination))))
      (8 * n + 3) := by
  have h := TapeFill.runs_fill hne b (storeTapes σ) n (σ destination)
  have hi : onPair counter destination (storeTapes σ) (counterTape n)
      (wordTape (σ destination)) = storeTapes σ :=
    TapeProductTerm.onPair_eq_self (by simp [hc, counterTape]) rfl
  have ho : onPair counter destination (storeTapes σ) (counterTape 0)
      (wordTape (List.replicate n b ++ σ destination)) =
      storeTapes (Function.update (Function.update σ counter []) destination
        (List.replicate n b ++ σ destination)) := by
    rw [onPair_eq_updates hne]
    simp only [storeTapes_update, counterTape, List.replicate_zero]
  simpa only [hi, ho] using h

end TapeStoreRuns
end DepthThreeLowerBound

end Complexity
