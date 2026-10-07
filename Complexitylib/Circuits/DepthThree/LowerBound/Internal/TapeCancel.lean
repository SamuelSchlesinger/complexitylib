/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeCancelRow

/-!
# Unrestricted depth-three lower bound: tape cancel

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeCancel.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeCancel

open TapeMultiProgram TapeRouting TapeUnary TapeProductTerm TapeRegister

/-- Control states for the read stage of the cancel routine. -/
abbrev ReadState := TapeArray.State ⊕ (Bool × TapeCancelRow.State)
/-- Control states for the clear stage of the cancel routine. -/
abbrev ClearState := ReadState ⊕ TapeArray.State
/-- Control states of the cancel routine. -/
abbrev State := ClearState ⊕ Unit

/-- Transition function for the read stage of the cancel routine. -/
def readProgram : TapeMultiProgram ReadState :=
  joinCode (TapeArray.code indexB productBits id)
    (carryCode TapeCancelRow.program) (fun q => (readFlag q, TapeCancelRow.start))

/-- Transition function for the clear stage of the cancel routine. -/
def clearProgram : TapeMultiProgram ClearState :=
  joinCode readProgram (TapeArray.code indexC productBits (fun _ => false))
    (fun _ => TapeArray.State.start)

/-- Transition function for the halt stage of the cancel routine. -/
def haltProgram : TapeMultiProgram Unit := fun _ _ => none

/-- Transition function of the cancel routine. -/
def program : TapeMultiProgram State :=
  joinCode clearProgram haltProgram (fun _ => ())

/-- Initial control state of the cancel routine. -/
def start : State := .inl (.inl (.inl TapeArray.State.start))
/-- Terminal control state of the cancel routine. -/
def done : State := .inr ()

/-- Tape-store contents at the result stage of the cancel routine. -/
def resultStore (σ : TapeStore) (r s : ℕ) (out : List Bool) : TapeStore :=
  TapeCancelRow.frame σ 0 r s out

/-- Transition budget for the cancel routine. -/
def cost (s r : ℕ) : ℕ := r * (2 * s + 4 * r + 21) + 4 * (s + r) + 14

theorem set_eq_split (xs : List Bool) (i : ℕ) (hi : i < xs.length) (b : Bool) :
    xs.set i b = xs.take i ++ b :: xs.drop (i + 1) := by
  calc
    xs.set i b = (xs.take i ++ xs.getD i false :: xs.drop (i + 1)).set
        (xs.take i).length b := by
      rw [TapeNaturalAccess.take_length xs i hi, ← TapeNaturalAccess.split xs i hi]
    _ = _ := by simp

theorem clear_at (σ : TapeStore) (i : ℕ)
    (hi : σ indexC = List.replicate i true) (hib : i < (σ productBits).length) :
    RunsIn (TapeArray.code indexC productBits (fun _ => false)).step
      (cfg TapeArray.State.start (storeTapes σ))
      (cfg (TapeArray.State.done ((σ productBits).getD i false))
        (storeTapes (Function.update σ productBits ((σ productBits).set i false))))
      (2 * i + 4) := by
  have h := modify_at (by decide : indexC ≠ productBits) (fun _ => false) (storeTapes σ)
    ((σ productBits).take i) ((σ productBits).drop (i + 1)) ((σ productBits).getD i false)
    (by simp only [storeTapes_apply, hi, counterTape, TapeNaturalAccess.take_length _ _ hib])
    (congrArg wordTape (TapeNaturalAccess.split _ _ hib))
  simpa only [TapeNaturalAccess.take_length _ _ hib, storeTapes_update,
    set_eq_split _ _ hib] using h

theorem update_output (σ : TapeStore) (r s : ℕ) (out out' : List Bool) :
    Function.update (resultStore σ r s out) productBits out' = resultStore σ r s out' := by
  funext q
  by_cases hq : q = productBits
  · subst q
    simp [resultStore]
  · simp [resultStore, TapeCancelRow.frame, Function.update, hq]

theorem runs_cancel (σ : TapeStore) (p c : List Bool) (s : ℕ)
    (hP : σ polyBits = p) (hOut : σ productBits = c)
    (hLoop : σ loop1 = List.replicate p.length true) (hA : σ indexA = [])
    (hB : σ indexB = List.replicate (s + p.length) true)
    (hC : σ indexC = List.replicate s true) (hbound : s + p.length < c.length) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (resultStore σ p.length s (cancelByUpdates p c s))))
      (cost s p.length) := by
  let v := c.getD (s + p.length) false
  let out := modulusUpdateLoop p v s p.length c
  let ρ := resultStore σ p.length s out
  have hr := TapeNaturalAccess.read indexB productBits (by decide) σ (s + p.length) hB
    (by simpa only [hOut] using hbound)
  have hrow := TapeCancelRow.runs_row v σ p c s 0 p.length hP (by omega) hbound.le
  have hentry : TapeCancelRow.frame σ p.length 0 s c = σ := by
    funext q
    by_cases hl : q = loop1
    · subst q
      simp [hLoop]
    · by_cases ha : q = indexA
      · subst q
        simp [hA]
      · by_cases hc : q = indexC
        · subst q
          simp [hC]
        · by_cases ho : q = productBits
          · subst q
            simp [hOut]
          · simp [TapeCancelRow.frame, hl, ha, hc, ho]
  have hrow' : RunsIn (TapeCancelRow.program v).step
      (cfg TapeCancelRow.start (storeTapes σ))
      (cfg TapeCancelRow.done (storeTapes ρ))
      (p.length * (2 * s + 4 * p.length + 21) + 3) := by
    simpa only [modulusUpdateLoop_zero, Nat.zero_add, hentry, ρ, resultStore, out] using hrow
  have hcarr := carry_runs TapeCancelRow.program v hrow'
  have hread := join_runs (TapeArray.code indexB productBits id)
    (carryCode TapeCancelRow.program) (fun q => (readFlag q, TapeCancelRow.start))
    (q' := TapeArray.State.done v)
    (by simpa only [hOut] using hr) rfl hcarr
  have hclear := clear_at ρ (s + p.length) (by simp [ρ, resultStore]) (by
    simp only [ρ, resultStore, TapeCancelRow.frame_output, out, modulusUpdateLoop_length]
    exact hbound)
  have hclear' : RunsIn (TapeArray.code indexC productBits (fun _ => false)).step
      (cfg TapeArray.State.start (storeTapes ρ))
      (cfg (TapeArray.State.done (out.getD (s + p.length) false))
        (storeTapes (resultStore σ p.length s (cancelByUpdates p c s))))
      (2 * (s + p.length) + 4) := by
    have hρout : ρ productBits = out := by simp [ρ, resultStore]
    simpa only [hρout, ρ, update_output, cancelByUpdates, out, v] using hclear
  have hboth := join_runs readProgram (TapeArray.code indexC productBits (fun _ => false))
    (fun _ => TapeArray.State.start) hread rfl hclear'
  have hhalt : RunsIn haltProgram.step
      (cfg () (storeTapes (resultStore σ p.length s (cancelByUpdates p c s))))
      (cfg () (storeTapes (resultStore σ p.length s (cancelByUpdates p c s)))) 0 := RunsIn.refl _ _
  have hall := join_runs clearProgram haltProgram (fun _ => ()) hboth rfl hhalt
  have htime : ((2 * (s + p.length) + 4 + 1 +
      (p.length * (2 * s + 4 * p.length + 21) + 3)) + 1 +
      (2 * (s + p.length) + 4)) + 1 + 0 = cost s p.length := by
    unfold cost
    omega
  simpa only [State, program, start, done, htime, Nat.add_zero] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeCancel
end DepthThreeLowerBound

end Complexity
