/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeConvolutionRow

/-!
# Unrestricted depth-three lower bound: tape convolution rows

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeConvolutionRows.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeConvolutionRows

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

/-- Control states for the read stage of the convolution rows routine. -/
abbrev ReadState := TapeCopy.State ⊕ TapeConvolutionRow.State
/-- Control states for the clear stage of the convolution rows routine. -/
abbrev ClearState := ReadState ⊕ TapeErase.State
/-- Control states for the body stage of the convolution rows routine. -/
abbrev BodyState := ClearState ⊕ IncState

/-- Transition function for the read stage of the convolution rows routine. -/
def readProgram : TapeMultiProgram ReadState :=
  joinCode (TapeCopy.code ringDegree loop1) TapeConvolutionRow.program
    (fun _ => TapeConvolutionRow.start)

/-- Transition function for the clear stage of the convolution rows routine. -/
def clearProgram : TapeMultiProgram ClearState :=
  joinCode readProgram (TapeErase.code indexB) (fun _ => TapeErase.State.start)

/-- Transition function for the body stage of the convolution rows routine. -/
def bodyProgram : TapeMultiProgram BodyState :=
  joinCode clearProgram (incProgram indexA) (fun _ => IncState.start)

/-- Initial control state of the body stage of the convolution rows routine. -/
def bodyStart : BodyState := .inl (.inl (.inl TapeCopy.State.start))
/-- Terminal control state of the body stage of the convolution rows routine. -/
def bodyDone : BodyState := .inr IncState.done

/-- Update the convolution output and advance the row index. -/
def bodyResult (σ : TapeStore) (i : ℕ) (out : List Bool) : TapeStore :=
  Function.update (Function.update σ productBits out) indexA (List.replicate (i + 1) true)

theorem runs_body (σ : TapeStore) (a b out : List Bool) (i : ℕ)
    (hA : σ hashBits = a) (hB : σ accumBits = b)
    (hI : σ indexA = List.replicate i true) (hJ : σ indexB = [])
    (hCount : σ ringDegree = List.replicate b.length true) (hLoop : σ loop1 = [])
    (hK : σ indexC = []) (hS : σ scratchA = []) (hOut : σ productBits = out)
    (hi : i < a.length) (hsize : a.length + b.length ≤ out.length) :
    RunsIn bodyProgram.step (cfg bodyStart (storeTapes σ))
      (cfg bodyDone (storeTapes (bodyResult σ i
        (convolutionUpdateRow a b i (List.range' 0 b.length) out))))
      (b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 17) := by
  let out' := convolutionUpdateRow a b i (List.range' 0 b.length) out
  let ρ := TapeConvolutionRow.frame σ 0 b.length out'
  have hcopy := TapeStoreRuns.copy (by decide : ringDegree ≠ loop1) σ hLoop
  have hrow := TapeConvolutionRow.runs_row σ a b i 0 b.length out
    hA hB hI hK hS hi (by omega) hsize
  have hentry : TapeConvolutionRow.frame σ b.length 0 out =
      Function.update σ loop1 (σ ringDegree) := by
    funext r
    by_cases hl : r = loop1
    · subst r
      simp [hCount]
    · by_cases hj : r = indexB
      · subst r
        simp [TapeConvolutionRow.frame, hJ, loop1, indexB]
      · by_cases hp : r = productBits
        · subst r
          simp [TapeConvolutionRow.frame, hOut, productBits, loop1, indexB]
        · simp [TapeConvolutionRow.frame, Function.update, hl, hj, hp]
  have hrow' : RunsIn TapeConvolutionRow.program.step
      (cfg TapeConvolutionRow.start (storeTapes (Function.update σ loop1 (σ ringDegree))))
      (cfg TapeConvolutionRow.done (storeTapes ρ))
      (b.length * (8 * a.length + 16 * b.length + 43) + 3) := by
    simpa only [hentry, Nat.zero_add, ρ, out'] using hrow
  have hread := join_runs (TapeCopy.code ringDegree loop1) TapeConvolutionRow.program
    (fun _ => TapeConvolutionRow.start) hcopy rfl hrow'
  have herase := TapeStoreRuns.erase indexB ρ
  have hclean : Function.update ρ indexB [] = Function.update σ productBits out' := by
    funext r
    by_cases hj : r = indexB
    · subst r
      simp [Function.update, hJ, indexB, productBits]
    · by_cases hl : r = loop1
      · subst r
        simp [ρ, Function.update, hLoop, loop1, indexB, productBits]
      · by_cases hp : r = productBits
        · subst r
          simp [ρ, Function.update, productBits, indexB]
        · simp [ρ, TapeConvolutionRow.frame, Function.update, hj, hl, hp]
  have hclear := join_runs readProgram (TapeErase.code indexB)
    (fun _ => TapeErase.State.start) hread rfl herase
  have hinc := increment indexA (storeTapes (Function.update σ productBits out')) i (by
    simp [hI, counterTape, indexA, productBits])
  have hinc' : RunsIn (incProgram indexA).step
      (cfg IncState.start (storeTapes (Function.update ρ indexB [])))
      (cfg IncState.done (storeTapes (bodyResult σ i out'))) 2 := by
    simpa only [hclean, bodyResult, storeTapes_update, counterTape] using hinc
  have hall := join_runs clearProgram (incProgram indexA) (fun _ => IncState.start)
    hclear rfl hinc'
  have hlenCopy : (σ ringDegree).length = b.length := by simp [hCount]
  have hlenErase : (ρ indexB).length = b.length := by simp [ρ]
  have htime : (2 * b.length + 4 + 1 +
      (b.length * (8 * a.length + 16 * b.length + 43) + 3)) + 1 +
      (2 * b.length + 5) + 1 + 2 =
      b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 17 := by omega
  simpa only [bodyProgram, bodyStart, bodyDone, hlenCopy, hlenErase, htime, out'] using hall

@[simp] theorem body_done (h : TapeHeads) : bodyProgram bodyDone h = none := rfl

/-- Control states of the convolution rows routine. -/
abbrev State := LoopState DecState BodyState

/-- Transition function of the convolution rows routine. -/
def program : TapeMultiProgram State :=
  loopCode (decProgram loop0) bodyProgram DecState.start bodyStart decPositive

/-- Initial control state of the convolution rows routine. -/
def start : State := loopTest DecState.start
/-- Terminal control state of the convolution rows routine. -/
def done : State := loopDone

/-- Tape-store invariant recording the loop counters and current output. -/
def frame (σ : TapeStore) (remaining row : ℕ) (out : List Bool) : TapeStore :=
  fun r => if r = loop0 then List.replicate remaining true
    else if r = indexA then List.replicate row true
    else if r = productBits then out else σ r

@[simp] theorem frame_counter (σ : TapeStore) (n i : ℕ) (out : List Bool) :
    frame σ n i out loop0 = List.replicate n true := by simp [frame]

@[simp] theorem frame_index (σ : TapeStore) (n i : ℕ) (out : List Bool) :
    frame σ n i out indexA = List.replicate i true := by simp [frame, loop0, indexA]

@[simp] theorem frame_output (σ : TapeStore) (n i : ℕ) (out : List Bool) :
    frame σ n i out productBits = out := by simp [frame, loop0, indexA, productBits]

theorem update_counter (σ : TapeStore) (n n' i : ℕ) (out : List Bool) :
    Function.update (frame σ n i out) loop0 (List.replicate n' true) = frame σ n' i out := by
  funext r
  by_cases hr : r = loop0
  · subst r
    simp
  · simp [frame, Function.update, hr]

theorem bodyResult_frame (σ : TapeStore) (n i : ℕ) (out out' : List Bool) :
    bodyResult (frame σ n i out) i out' = frame σ n (i + 1) out' := by
  funext r
  by_cases hr : r = indexA
  · subst r
    simp [bodyResult]
  · by_cases hp : r = productBits
    · subst r
      simp [bodyResult, indexA, productBits]
    · simp [bodyResult, Function.update, frame, hr, hp]

theorem runs_rows (σ : TapeStore) (a b : List Bool) (i n : ℕ) (out : List Bool)
    (hA : σ hashBits = a) (hB : σ accumBits = b)
    (hJ : σ indexB = []) (hCount : σ ringDegree = List.replicate b.length true)
    (hLoop : σ loop1 = []) (hK : σ indexC = []) (hS : σ scratchA = [])
    (hi : i + n ≤ a.length) (hsize : a.length + b.length ≤ out.length) :
    RunsIn program.step (cfg start (storeTapes (frame σ n i out)))
      (cfg done (storeTapes (frame σ 0 (i + n)
        (convolutionUpdateRows a b (List.range' i n) out))))
      (n * (b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 23) + 3) := by
  induction n generalizing i out with
  | zero =>
      have hd := decrement_empty loop0 (storeTapes (frame σ 0 i out)) (by simp [])
      have he := loop_exit (decProgram loop0) bodyProgram DecState.start bodyStart
        decPositive hd rfl rfl
      simpa only [program, start, done, List.range'_zero, convolutionUpdateRows_nil,
        Nat.add_zero, Nat.zero_mul, Nat.zero_add] using he
  | succ n ih =>
      have hi' : i < a.length := by omega
      let out' := convolutionUpdateRow a b i (List.range' 0 b.length) out
      have hd := decrement_cons loop0 (storeTapes (frame σ (n + 1) i out))
        (List.replicate n true) true (by simp [List.replicate_succ])
      have hd' : RunsIn (decProgram loop0).step
          (cfg DecState.start (storeTapes (frame σ (n + 1) i out)))
          (cfg (DecState.done true) (storeTapes (frame σ n i out))) 4 := by
        simpa only [← storeTapes_update, update_counter] using hd
      have hb := runs_body (frame σ n i out) a b out i
        (by simp [frame, hA, hashBits, loop0, indexA, productBits])
        (by simp [frame, hB, accumBits, loop0, indexA, productBits])
        (by simp) (by simp [frame, hJ, indexB, loop0, indexA, productBits])
        (by simp [frame, hCount, ringDegree, loop0, indexA, productBits])
        (by simp [frame, hLoop, loop1, loop0, indexA, productBits])
        (by simp [frame, hK, indexC, loop0, indexA, productBits])
        (by simp [frame, hS, scratchA, loop0, indexA, productBits])
        (by simp) hi' hsize
      have hb' : RunsIn bodyProgram.step
          (cfg bodyStart (storeTapes (frame σ n i out)))
          (cfg bodyDone (storeTapes (frame σ n (i + 1) out')))
          (b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 17) := by
        simpa only [bodyResult_frame, out'] using hb
      have hit := loop_iter (decProgram loop0) bodyProgram DecState.start bodyStart
        decPositive hd' rfl rfl hb' rfl
      have hrest := ih (i + 1) out' (by omega) (by simpa [out'] using hsize)
      have hall := hit.trans hrest
      have htime : 4 + 1 +
          (b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 17) + 1 +
          (n * (b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 23) + 3) =
          (n + 1) * (b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 23) + 3 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hindex : i + 1 + n = i + (n + 1) := by omega
      simpa only [program, start, done, List.range'_succ, convolutionUpdateRows_step,
        ← List.range_eq_range', htime, hindex, out'] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeConvolutionRows
end DepthThreeLowerBound

end Complexity
