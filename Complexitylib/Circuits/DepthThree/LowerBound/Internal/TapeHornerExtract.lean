/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeInputBlocks

/-!
# Unrestricted depth-three lower bound: tape horner extract

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeHornerExtract.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeHornerExtract

open TapeMultiProgram TapeRouting TapeRegister TapeInputBlockLoop

/-- The register allocation used by this block-transfer routine. -/
def registers : Registers where
  toFun i := match i.val with
    | 0 => coeffBits
    | 1 => loop3
    | 2 => loop4
    | 3 => loop5
    | _ => scratchB
  inj' := by decide

/-- Control states of the horner extract routine. -/
abbrev State := TapeCopy.State ⊕ TapeInputBlockLoop.State

/-- Transition function of the horner extract routine. -/
def program : TapeMultiProgram State :=
  joinCode (TapeCopy.code ringDegree loop4) (TapeInputBlockLoop.program registers)
    (fun _ => TapeInputBlockLoop.start)

/-- Initial control state of the horner extract routine. -/
def start : State := .inl TapeCopy.State.start
/-- Terminal control state of the horner extract routine. -/
def done : State := .inr TapeInputBlockLoop.done

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

theorem runs_extract (σ : TapeStore) («prefix» block suffix : List Bool) (r : ℕ)
    (hsource : σ coeffBits = «prefix» ++ block ++ suffix)
    (hcursor : σ loop3 = List.replicate («prefix».length + r) true)
    (hdegree : σ ringDegree = List.replicate r true)
    (hblock : block.length = r) (hcount : σ loop4 = [])
    (hdest : σ scratchB = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update
        (Function.update σ loop3 (List.replicate «prefix».length true)) scratchB block)))
      (r * (2 * «prefix».length + r + 19) + 8) := by
  let U := Function.update σ loop4 (List.replicate r true)
  have hc := TapeStoreRuns.copy (src := ringDegree) (dst := loop4) (by decide) σ hcount
  have hc' : RunsIn (TapeCopy.code ringDegree loop4).step
      (cfg TapeCopy.State.start (storeTapes σ)) (cfg TapeCopy.State.done (storeTapes U))
      (2 * r + 4) := by
    simpa only [hdegree, List.length_replicate] using hc
  have hb := TapeInputBlockLoop.runs_block registers σ «prefix» block suffix [] hsource
  have hi : blockStore registers σ («prefix».length + block.length) block.length [] = U := by
    funext q
    by_cases h4 : q = loop4 <;> by_cases h3 : q = loop3 <;>
      by_cases hd : q = scratchB <;>
      simp_all [blockStore, registers, count, index, destination, U, Function.update_apply,
        loop4, loop3, scratchB]
  have ho : blockStore registers σ «prefix».length 0 (block ++ []) =
      Function.update (Function.update σ loop3 (List.replicate «prefix».length true))
        scratchB block := by
    funext q
    by_cases h4 : q = loop4 <;> by_cases h3 : q = loop3 <;>
      by_cases hd : q = scratchB <;>
      simp_all [blockStore, registers, count, index, destination, Function.update_apply]
  rw [hi, ho, hblock] at hb
  have hall := join_runs (TapeCopy.code ringDegree loop4)
    (TapeInputBlockLoop.program registers) (fun _ => TapeInputBlockLoop.start) hc' rfl hb
  have ht : (2 * r + 4) + 1 + (r * (2 * «prefix».length + r + 17) + 3) =
      r * (2 * «prefix».length + r + 19) + 8 := by ring
  simpa only [program, start, done, ht] using hall

end TapeHornerExtract
end DepthThreeLowerBound

end Complexity
