/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeCopyAdd

/-!
# Unrestricted depth-three lower bound: tape remainder setup

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeRemainderSetup.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeRemainderSetup

open TapeMultiProgram TapeRouting TapeRegister

/-- Tape-store contents at the prepared stage of the remainder setup routine. -/
def preparedStore (σ : TapeStore) (r s : ℕ) : TapeStore :=
  Function.update (Function.update (Function.update σ
    indexB (List.replicate (s + r) true)) indexC (List.replicate s true))
    loop1 (List.replicate r true)

/-- Clear the three index registers in the tape store. -/
def clearIndices (σ : TapeStore) : TapeStore :=
  Function.update (Function.update (Function.update σ indexA []) indexB []) indexC []

@[simp] theorem preparedStore_indexB (σ : TapeStore) (r s : ℕ) :
    preparedStore σ r s indexB = List.replicate (s + r) true := by
  simp [preparedStore, indexB, indexC, loop1]

@[simp] theorem preparedStore_indexC (σ : TapeStore) (r s : ℕ) :
    preparedStore σ r s indexC = List.replicate s true := by
  simp [preparedStore, indexC, loop1]

@[simp] theorem preparedStore_loop1 (σ : TapeStore) (r s : ℕ) :
    preparedStore σ r s loop1 = List.replicate r true := by
  simp [preparedStore]

theorem preparedStore_other (σ : TapeStore) (r s : ℕ) (q : TapeRegister)
    (hB : q ≠ indexB) (hC : q ≠ indexC) (hL : q ≠ loop1) :
    preparedStore σ r s q = σ q := by
  simp [preparedStore, Function.update, hB, hC, hL]

@[simp] theorem clearIndices_indexA (σ : TapeStore) : clearIndices σ indexA = [] := by
  simp [clearIndices, indexA, indexB, indexC]

@[simp] theorem clearIndices_indexB (σ : TapeStore) : clearIndices σ indexB = [] := by
  simp [clearIndices, indexB, indexC]

@[simp] theorem clearIndices_indexC (σ : TapeStore) : clearIndices σ indexC = [] := by
  simp [clearIndices]

theorem clearIndices_other (σ : TapeStore) (q : TapeRegister)
    (hA : q ≠ indexA) (hB : q ≠ indexB) (hC : q ≠ indexC) :
    clearIndices σ q = σ q := by
  simp [clearIndices, Function.update, hA, hB, hC]

/-- Control states for the setup stage of the remainder setup routine. -/
abbrev SetupState := TapeCopy.State ⊕ (TapeCopy.State ⊕
  (TapeCopyAdd.State ⊕ TapeCopy.State))

/-- Transition function for the setup stage of the remainder setup routine. -/
def setupProgram : TapeMultiProgram SetupState :=
  joinCode (TapeCopy.code loop0 indexB)
    (joinCode (TapeCopy.code loop0 indexC)
      (joinCode (TapeCopyAdd.program ringDegree scratchA indexB)
        (TapeCopy.code ringDegree loop1) (fun _ => TapeCopy.State.start))
      (fun _ => .inl TapeCopyAdd.start))
    (fun _ => .inl TapeCopy.State.start)

/-- Initial control state of the setup stage of the remainder setup routine. -/
def setupStart : SetupState := .inl .start
/-- Terminal control state of the setup stage of the remainder setup routine. -/
def setupDone : SetupState := .inr (.inr (.inr .done))

@[simp] theorem setupProgram_done (h : TapeHeads) :
    setupProgram setupDone h = none := rfl

theorem runs_setup (σ : TapeStore) (r s : ℕ)
    (hLoop0 : σ loop0 = List.replicate s true)
    (hDegree : σ ringDegree = List.replicate r true)
    (hLoop1 : σ loop1 = []) (_hA : σ indexA = [])
    (hB : σ indexB = []) (hC : σ indexC = []) (hScratch : σ scratchA = []) :
    RunsIn setupProgram.step (cfg setupStart (storeTapes σ))
      (cfg setupDone (storeTapes (preparedStore σ r s))) (4 * s + 12 * r + 23) := by
  let τB := Function.update σ indexB (List.replicate s true)
  let τC := Function.update τB indexC (List.replicate s true)
  let τD := Function.update τC indexB (List.replicate (s + r) true)
  let τL := Function.update τD loop1 (List.replicate r true)
  have hfirst : RunsIn (TapeCopy.code loop0 indexB).step
      (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes τB)) (2 * s + 4) := by
    simpa only [hLoop0, List.length_replicate] using
      TapeStoreRuns.copy (show loop0 ≠ indexB by decide) σ hB
  have hLoop0B : τB loop0 = List.replicate s true := by
    simp [τB, hLoop0, loop0, indexB]
  have hsecond : RunsIn (TapeCopy.code loop0 indexC).step
      (cfg TapeCopy.State.start (storeTapes τB))
      (cfg TapeCopy.State.done (storeTapes τC)) (2 * s + 4) := by
    have h := TapeStoreRuns.copy (show loop0 ≠ indexC by decide) τB
      (by simp [τB, hC, indexB, indexC])
    simpa only [hLoop0B, List.length_replicate] using h
  have hthird : RunsIn (TapeCopyAdd.program ringDegree scratchA indexB).step
      (cfg TapeCopyAdd.start (storeTapes τC))
      (cfg TapeCopyAdd.done (storeTapes τD)) (10 * r + 8) := by
    exact TapeCopyAdd.runs_add (by decide) (by decide) τC r s
      (by simp [τC, τB, hDegree, ringDegree, indexB, indexC])
      (by simp [τC, τB, indexB, indexC])
      (by simp [τC, τB, hScratch, scratchA, indexB, indexC])
  have hDegreeD : τD ringDegree = List.replicate r true := by
    simp [τD, τC, τB, hDegree, ringDegree, indexB, indexC]
  have hfourth : RunsIn (TapeCopy.code ringDegree loop1).step
      (cfg TapeCopy.State.start (storeTapes τD))
      (cfg TapeCopy.State.done (storeTapes τL)) (2 * r + 4) := by
    have h := TapeStoreRuns.copy (show ringDegree ≠ loop1 by decide) τD
      (by simp [τD, τC, τB, hLoop1, loop1, indexB, indexC])
    simpa only [hDegreeD, List.length_replicate] using h
  have hlast := join_runs (TapeCopyAdd.program ringDegree scratchA indexB)
    (TapeCopy.code ringDegree loop1) (fun _ => TapeCopy.State.start)
    hthird rfl hfourth
  have hrest := join_runs (TapeCopy.code loop0 indexC)
    (joinCode (TapeCopyAdd.program ringDegree scratchA indexB)
      (TapeCopy.code ringDegree loop1) (fun _ => TapeCopy.State.start))
    (fun _ => Sum.inl TapeCopyAdd.start) hsecond rfl hlast
  have hall := join_runs (TapeCopy.code loop0 indexB)
    (joinCode (TapeCopy.code loop0 indexC)
      (joinCode (TapeCopyAdd.program ringDegree scratchA indexB)
        (TapeCopy.code ringDegree loop1) (fun _ => TapeCopy.State.start))
      (fun _ => Sum.inl TapeCopyAdd.start))
    (fun _ => Sum.inl TapeCopy.State.start) hfirst rfl hrest
  have houtput : τL = preparedStore σ r s := by
    funext q
    by_cases hL : q = loop1
    · subst q
      simp [τL, preparedStore]
    · by_cases hC' : q = indexC
      · subst q
        simp [τL, τD, τC, τB, preparedStore, loop1, indexB, indexC]
      · by_cases hB' : q = indexB
        · subst q
          simp [τL, τD, τC, τB, preparedStore, loop1, indexB, indexC]
        · simp [τL, τD, τC, τB, preparedStore, Function.update, hL, hC', hB']
  have htime : (2 * s + 4) + 1 +
      ((2 * s + 4) + 1 + ((10 * r + 8) + 1 + (2 * r + 4))) =
      4 * s + 12 * r + 23 := by omega
  simpa only [setupProgram, setupStart, setupDone, houtput, htime] using hall

/-- Control states for the cleanup stage of the remainder setup routine. -/
abbrev CleanupState := TapeErase.State ⊕ (TapeErase.State ⊕ TapeErase.State)

/-- Transition function for the cleanup stage of the remainder setup routine. -/
def cleanupProgram : TapeMultiProgram CleanupState :=
  joinCode (TapeErase.code indexA)
    (joinCode (TapeErase.code indexB) (TapeErase.code indexC)
      (fun _ => TapeErase.State.start))
    (fun _ => .inl TapeErase.State.start)

/-- Initial control state of the cleanup stage of the remainder setup routine. -/
def cleanupStart : CleanupState := .inl .start
/-- Terminal control state of the cleanup stage of the remainder setup routine. -/
def cleanupDone : CleanupState := .inr (.inr .done)

@[simp] theorem cleanupProgram_done (h : TapeHeads) :
    cleanupProgram cleanupDone h = none := rfl

theorem runs_cleanup (σ : TapeStore) (r s : ℕ)
    (hA : σ indexA = List.replicate r true)
    (hB : σ indexB = List.replicate (s + r) true)
    (hC : σ indexC = List.replicate (s + r) true) :
    RunsIn cleanupProgram.step (cfg cleanupStart (storeTapes σ))
      (cfg cleanupDone (storeTapes (clearIndices σ))) (4 * s + 6 * r + 17) := by
  let τA := Function.update σ indexA []
  let τB := Function.update τA indexB []
  have hfirst : RunsIn (TapeErase.code indexA).step
      (cfg TapeErase.State.start (storeTapes σ))
      (cfg TapeErase.State.done (storeTapes τA)) (2 * r + 5) := by
    simpa only [hA, List.length_replicate] using TapeStoreRuns.erase indexA σ
  have hB' : τA indexB = List.replicate (s + r) true := by
    simp [τA, hB, indexA, indexB]
  have hsecond : RunsIn (TapeErase.code indexB).step
      (cfg TapeErase.State.start (storeTapes τA))
      (cfg TapeErase.State.done (storeTapes τB)) (2 * (s + r) + 5) := by
    simpa only [hB', List.length_replicate] using TapeStoreRuns.erase indexB τA
  have hC' : τB indexC = List.replicate (s + r) true := by
    simp [τB, τA, hC, indexA, indexB, indexC]
  have hthird : RunsIn (TapeErase.code indexC).step
      (cfg TapeErase.State.start (storeTapes τB))
      (cfg TapeErase.State.done (storeTapes (clearIndices σ))) (2 * (s + r) + 5) := by
    have hclear : Function.update τB indexC [] = clearIndices σ := rfl
    simpa only [hC', List.length_replicate, hclear] using TapeStoreRuns.erase indexC τB
  have hrest := join_runs (TapeErase.code indexB) (TapeErase.code indexC)
    (fun _ => TapeErase.State.start) hsecond rfl hthird
  have hall := join_runs (TapeErase.code indexA)
    (joinCode (TapeErase.code indexB) (TapeErase.code indexC)
      (fun _ => TapeErase.State.start))
    (fun _ => Sum.inl TapeErase.State.start) hfirst rfl hrest
  have htime : (2 * r + 5) + 1 +
      ((2 * (s + r) + 5) + 1 + (2 * (s + r) + 5)) =
      4 * s + 6 * r + 17 := by omega
  simpa only [cleanupProgram, cleanupStart, cleanupDone, htime] using hall

end TapeRemainderSetup
end DepthThreeLowerBound

end Complexity
