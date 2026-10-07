/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeStoreRepresentation

/-!
# Unrestricted depth-three lower bound: tape convolution step

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeConvolutionStep.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeConvolutionStep

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

/-- Control states for the setup stage of the convolution step routine. -/
abbrev SetupState := TapeCopy.State ⊕ TapeCopy.State
/-- Control states for the sum stage of the convolution step routine. -/
abbrev SumState := SetupState ⊕ AddState
/-- Control states for the term stage of the convolution step routine. -/
abbrev TermState := SumState ⊕ TapeProductTerm.State
/-- Control states for the clear stage of the convolution step routine. -/
abbrev ClearState := TermState ⊕ TapeErase.State
/-- Control states of the convolution step routine. -/
abbrev State := ClearState ⊕ IncState

/-- Copy the current row and column indices into temporary counters. -/
def copyIndices : TapeMultiProgram SetupState :=
  joinCode (TapeCopy.code indexA indexC) (TapeCopy.code indexB scratchA)
    (fun _ => TapeCopy.State.start)

/-- Add the copied indices to locate the output coefficient. -/
def sumIndices : TapeMultiProgram SumState :=
  joinCode copyIndices (addProgram scratchA indexC) (fun _ => addStart)

/-- Accumulate the selected input-bit product into its output coefficient. -/
def term : TapeMultiProgram TermState :=
  joinCode sumIndices
    (TapeProductTerm.program indexA hashBits indexB accumBits indexC productBits)
    (fun _ => TapeProductTerm.start)

/-- Clear the temporary output index after accumulating a convolution term. -/
def clear : TapeMultiProgram ClearState :=
  joinCode term (TapeErase.code indexC) (fun _ => TapeErase.State.start)

/-- Transition function of the convolution step routine. -/
def program : TapeMultiProgram State :=
  joinCode clear (incProgram indexB) (fun _ => IncState.start)

/-- Initial control state of the convolution step routine. -/
def start : State := .inl (.inl (.inl (.inl (.inl TapeCopy.State.start))))
/-- Terminal control state of the convolution step routine. -/
def done : State := .inr IncState.done

/-- Tape-store contents at the result stage of the convolution step routine. -/
def resultStore (σ : TapeStore) (j : ℕ) (out : List Bool) : TapeStore :=
  Function.update (Function.update σ productBits out) indexB (List.replicate (j + 1) true)

theorem runs_step (σ : TapeStore) (pa sa pb sb pc sc : List Bool) (a b old : Bool)
    (hi : σ indexA = List.replicate pa.length true)
    (hj : σ indexB = List.replicate pb.length true)
    (hk : σ indexC = []) (hs : σ scratchA = [])
    (ha : σ hashBits = pa ++ a :: sa) (hb : σ accumBits = pb ++ b :: sb)
    (hc : σ productBits = pc ++ old :: sc) (hlen : pc.length = pa.length + pb.length) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (resultStore σ pb.length
        (pc ++ Bool.xor old (a && b) :: sc))))
      (8 * pa.length + 16 * pb.length + 37) := by
  let σ₁ := Function.update σ indexC (σ indexA)
  let σ₂ := Function.update σ₁ scratchA (σ₁ indexB)
  let σ₃ := Function.update (Function.update σ₂ scratchA []) indexC
    (List.replicate (pa.length + pb.length) true)
  let σ₄ := Function.update σ₃ productBits (pc ++ Bool.xor old (a && b) :: sc)
  let σ₅ := Function.update σ₄ indexC []
  let σ₆ := Function.update σ₅ indexB (List.replicate (pb.length + 1) true)
  have hcopyA := TapeStoreRuns.copy (by decide : indexA ≠ indexC) σ hk
  have hcopyB := TapeStoreRuns.copy (by decide : indexB ≠ scratchA) σ₁ (by
    simp [σ₁, hs, indexC, scratchA])
  have hsetup := join_runs (TapeCopy.code indexA indexC) (TapeCopy.code indexB scratchA)
    (fun _ => TapeCopy.State.start) hcopyA rfl hcopyB
  have hadd := TapeStoreRuns.add (by decide : scratchA ≠ indexC) σ₂ pb.length pa.length
    (by simp [σ₂, σ₁, hj, indexB, indexC])
    (by simp [σ₂, σ₁, hi, scratchA, indexC])
  have hsum := join_runs copyIndices (addProgram scratchA indexC)
    (fun _ => addStart) hsetup rfl hadd
  have hprod := TapeProductTerm.runs_product_term
    indexA hashBits indexB accumBits indexC productBits
    (by decide) (by decide) (by decide) (storeTapes σ₃)
    pa sa pb sb pc sc a b old
    (by simp [σ₃, σ₂, σ₁, hi, counterTape, indexA, indexB, indexC, scratchA])
    (by simp [σ₃, σ₂, σ₁, ha, hashBits, indexC, scratchA])
    (by simp [σ₃, σ₂, σ₁, hj, counterTape, indexA, indexB, indexC, scratchA])
    (by simp [σ₃, σ₂, σ₁, hb, accumBits, indexC, scratchA])
    (by simp [σ₃, counterTape, hlen])
    (by simp [σ₃, σ₂, σ₁, hc, productBits, indexC, scratchA])
  have hprod' : RunsIn
      (TapeProductTerm.program indexA hashBits indexB accumBits indexC productBits).step
      (cfg TapeProductTerm.start (storeTapes σ₃))
      (cfg (TapeProductTerm.done a b old) (storeTapes σ₄))
      (2 * (pa.length + pb.length + pc.length) + 14) := by
    simpa only [σ₄, storeTapes_update] using hprod
  have hterm := join_runs sumIndices
    (TapeProductTerm.program indexA hashBits indexB accumBits indexC productBits)
    (fun _ => TapeProductTerm.start) hsum rfl hprod'
  have herase := TapeStoreRuns.erase indexC σ₄
  have hclear := join_runs term (TapeErase.code indexC)
    (fun _ => TapeErase.State.start) hterm rfl herase
  have hinc := increment indexB (storeTapes σ₅) pb.length (by
    simp [σ₅, σ₄, σ₃, σ₂, σ₁, counterTape, hj, indexB, indexC, scratchA, productBits])
  have hinc' : RunsIn (incProgram indexB).step (cfg IncState.start (storeTapes σ₅))
      (cfg IncState.done (storeTapes σ₆)) 2 := by
    simpa only [σ₆, storeTapes_update, counterTape] using hinc
  have hall := join_runs clear (incProgram indexB) (fun _ => IncState.start) hclear rfl hinc'
  have hstore : σ₆ = resultStore σ pb.length (pc ++ Bool.xor old (a && b) :: sc) := by
    funext r
    by_cases hp : r = productBits
    · subst r
      simp [σ₆, σ₅, σ₄, resultStore, indexB, indexC, productBits]
    · by_cases hj' : r = indexB
      · subst r
        simp [σ₆, resultStore]
      · by_cases hk' : r = indexC
        · subst r
          simp [σ₆, σ₅, resultStore, hk, indexB, indexC, productBits]
        · by_cases hs' : r = scratchA
          · subst r
            simp [σ₆, σ₅, σ₄, σ₃, resultStore, hs, indexB, indexC, scratchA, productBits]
          · simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, resultStore, hp, hj', hk', hs']
  have hlenA : (σ indexA).length = pa.length := by simp [hi]
  have hlenB : (σ₁ indexB).length = pb.length := by simp [σ₁, hj, indexB, indexC]
  have hlenK : (σ₄ indexC).length = pa.length + pb.length := by
    simp [σ₄, σ₃, productBits, indexC]
  have htime : (((2 * pa.length + 4 + 1 + (2 * pb.length + 4)) + 1 +
      (8 * pb.length + 3)) + 1 + (2 * (pa.length + pb.length + pc.length) + 14)) +
      1 + (2 * (pa.length + pb.length) + 5) + 1 + 2 =
        8 * pa.length + 16 * pb.length + 37 := by omega
  simpa only [program, start, done, hstore, hlenA, hlenB, hlenK, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeConvolutionStep
end DepthThreeLowerBound

end Complexity
