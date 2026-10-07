/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeArray
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeArithmetic

/-!
# Unrestricted depth-three lower bound: tape product term

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeProductTerm.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4

namespace DepthThreeLowerBound
namespace TapeProductTerm

open TapeMultiProgram TapeCopy TapeRouting TapeArithmetic TapeUnary

theorem onPair_eq_self {src dst : TapeRegister} {T : TapeTapes}
    {S D : Turing.Tape TapeSymbol} (hS : T src = S) (hD : T dst = D) :
    onPair src dst T S D = T := by
  funext r
  by_cases hs : r = src
  · subst r
    simpa only [onPair_src] using hS.symm
  · by_cases hd : r = dst
    · subst r
      simp only [onPair, hs, ite_false, ite_true]
      exact hD.symm
    · simp [onPair, hs, hd]

theorem read_at {index array : TapeRegister} (hne : index ≠ array)
    (T : TapeTapes) («prefix» suffix : List Bool) (b : Bool)
    (hi : T index = counterTape «prefix».length)
    (ha : T array = wordTape («prefix» ++ b :: suffix)) :
    RunsIn (TapeArray.code index array id).step
      (cfg TapeArray.State.start T) (cfg (TapeArray.State.done b) T)
      (2 * «prefix».length + 4) := by
  have h := TapeArray.runs_read hne T «prefix» suffix b
  have hframe := onPair_eq_self hi ha
  dsimp only [counterTape] at hframe
  simpa only [counterTape, hframe] using h

theorem modify_at {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) («prefix» suffix : List Bool) (b : Bool)
    (hi : T index = counterTape «prefix».length)
    (ha : T array = wordTape («prefix» ++ b :: suffix)) :
    RunsIn (TapeArray.code index array f).step
      (cfg TapeArray.State.start T)
      (cfg (TapeArray.State.done b)
        (Function.update T array (wordTape («prefix» ++ f b :: suffix))))
      (2 * «prefix».length + 4) := by
  have h := TapeArray.runs_modify hne f T «prefix» suffix b
  have hframe := onPair_eq_self hi ha
  have hout : onPair index array T (counterTape «prefix».length)
      (wordTape («prefix» ++ f b :: suffix)) =
        Function.update T array (wordTape («prefix» ++ f b :: suffix)) := by
    rw [← update_onPair_dst hne T (counterTape «prefix».length)
      (wordTape («prefix» ++ b :: suffix)), hframe]
  dsimp only [counterTape] at hframe hout
  simpa only [counterTape, hframe, hout] using h

/-- Transition function for the carry stage of the product term routine. -/
def carryCode {F : Type uDepth1} {Q : Type uDepth2} (P : F → TapeMultiProgram Q) :
  TapeMultiProgram (F × Q)
  | (flag, q), h => (P flag q h).map fun out => ((flag, out.1), out.2)

theorem carry_runs {F : Type uDepth3} {Q : Type uDepth4} (P : F → TapeMultiProgram Q) (flag : F)
    {q q' : Q} {T U : TapeTapes} {n : ℕ}
    (h : RunsIn (P flag).step (cfg q T) (cfg q' U) n) :
    RunsIn (carryCode P).step (cfg (flag, q) T) (cfg (flag, q') U) n :=
  runs_map (P flag) (carryCode P) (fun q => (flag, q)) (by
    intro a heads a' writes moves he
    simp only [carryCode, he, Option.map_some]) h

/-- Read the bit returned by the array access routine. -/
def readFlag : TapeArray.State → Bool
  | .done b => b
  | _ => false

/-- Control states for the read stage of the product term routine. -/
abbrev ReadState := TapeArray.State ⊕ (Bool × TapeArray.State)
/-- Control states of the product term routine. -/
abbrev State := ReadState ⊕ ((Bool × Bool) × TapeArray.State)

/-- Transition function for the read stage of the product term routine. -/
def readProgram (i a j b : TapeRegister) : TapeMultiProgram ReadState :=
  joinCode (TapeArray.code i a id)
    (carryCode (fun _ : Bool => TapeArray.code j b id))
    (fun q => (readFlag q, TapeArray.State.start))

/-- Read the pair of bits used to compute a convolution term. -/
def termFlags : ReadState → (Bool × Bool)
  | .inr (a, q) => (a, readFlag q)
  | .inl _ => (false, false)

/-- Transition function for the update stage of the product term routine. -/
def updateProgram (k c : TapeRegister) : TapeMultiProgram ((Bool × Bool) × TapeArray.State) :=
  carryCode fun ab => TapeArray.code k c (fun old => Bool.xor old (ab.1 && ab.2))

/-- Transition function of the product term routine. -/
def program (i a j b k c : TapeRegister) : TapeMultiProgram State :=
  joinCode (readProgram i a j b) (updateProgram k c)
    (fun q => (termFlags q, TapeArray.State.start))

/-- Initial control state of the product term routine. -/
def start : State := .inl (.inl TapeArray.State.start)
/-- Terminal control state of the product term routine. -/
def done (a b old : Bool) : State := .inr ((a, b), TapeArray.State.done old)

theorem runs_product_term (i a j b k c : TapeRegister)
    (hia : i ≠ a) (hjb : j ≠ b) (hkc : k ≠ c)
    (T : TapeTapes) (pa sa pb sb pc sc : List Bool) (va vb old : Bool)
    (hi : T i = counterTape pa.length) (ha : T a = wordTape (pa ++ va :: sa))
    (hj : T j = counterTape pb.length) (hb : T b = wordTape (pb ++ vb :: sb))
    (hk : T k = counterTape pc.length) (hc : T c = wordTape (pc ++ old :: sc)) :
    RunsIn (program i a j b k c).step (cfg start T)
      (cfg (done va vb old)
        (Function.update T c (wordTape (pc ++ Bool.xor old (va && vb) :: sc))))
      (2 * (pa.length + pb.length + pc.length) + 14) := by
  have hra := read_at hia T pa sa va hi ha
  have hrb := read_at hjb T pb sb vb hj hb
  have hrb' := carry_runs (fun _ : Bool => TapeArray.code j b id) va hrb
  have hread := join_runs (TapeArray.code i a id)
    (carryCode (fun _ : Bool => TapeArray.code j b id))
    (fun q => (readFlag q, TapeArray.State.start)) hra rfl hrb'
  have hupdate := modify_at hkc (fun old => Bool.xor old (va && vb)) T pc sc old hk hc
  have hupdate' := carry_runs
    (fun ab : Bool × Bool => TapeArray.code k c (fun old => Bool.xor old (ab.1 && ab.2)))
    (va, vb) hupdate
  have hreadhalt : readProgram i a j b (.inr (va, TapeArray.State.done vb)) (heads T) = none := rfl
  have hall := join_runs (readProgram i a j b) (updateProgram k c)
    (fun q => (termFlags q, TapeArray.State.start)) hread hreadhalt hupdate'
  have htime : (2 * pa.length + 4 + 1 + (2 * pb.length + 4)) + 1 +
      (2 * pc.length + 4) = 2 * (pa.length + pb.length + pc.length) + 14 := by omega
  simpa only [program, start, done, htime] using hall

@[simp] theorem program_done (i a j b k c : TapeRegister) (va vb old : Bool) (h : TapeHeads) :
    program i a j b k c (done va vb old) h = none := rfl

end TapeProductTerm
end DepthThreeLowerBound

end Complexity
