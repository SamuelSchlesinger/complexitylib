/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeMultiProgram
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeWordRewind
public import Lean.Elab.Tactic.Omega

/-!
# Unrestricted depth-three lower bound: tape initialization

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeInitialization.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

namespace DepthThreeLowerBound

open Turing

/-- Control states for the init stage of the initialization routine. -/
inductive InitState
  | start
  | home
  | prepare
  | scan
  | rewind
  | done
  deriving DecidableEq, Inhabited

instance : Fintype InitState where
  elems := {.start, .home, .prepare, .scan, .rewind, .done}
  complete := by
    intro state
    cases state <;> simp

/-- The input and input-length registers that move during initialization. -/
def initActive (r : TapeRegister) : Prop :=
  r = TapeRegister.input ∨ r = TapeRegister.length

instance (r : TapeRegister) : Decidable (initActive r) :=
  inferInstanceAs (Decidable (r = TapeRegister.input ∨ r = TapeRegister.length))

/-- Transition function for the initialization stage of the initialization routine. -/
def initializationCode : TapeMultiProgram InitState
  | .start, h => some (.home, h, fun _ => .left)
  | .home, _ => some (.prepare, fun _ => cleanAtom .home, fun _ => .right)
  | .prepare, h => some (.scan,
      (fun r => if initActive r then h r else cleanAtom .endMark),
      (fun r => if initActive r then .stay else .left))
  | .scan, h =>
      match (h TapeRegister.input).1 with
      | .bit _ => some (.scan,
          (fun r => if r = TapeRegister.length then rawInputSymbol true else h r),
          (fun r => if initActive r then .right else .stay))
      | .blank => some (.rewind,
          (fun r => if initActive r then cleanAtom .endMark else h r),
          fun _ => .stay)
      | _ => none
  | .rewind, h =>
      if (h TapeRegister.input).1 = .home then
        some (.done, h, fun _ => .stay)
      else some (.rewind, h, fun r => if initActive r then .left else .stay)
  | .done, _ => none

/-- The raw encoded input on its designated tape, with all others blank. -/
def rawInputTapes (bits : List Bool) : TapeTapes := fun r =>
  if r = TapeRegister.input then Tape.mk₁ (encodeInput bits) else Tape.mk₁ []

/-- Boundary-marked input, its unary length, and empty workspace tapes. -/
def initializedTapes (bits : List Bool) : TapeTapes := fun r =>
  if r = TapeRegister.input then wordTape bits
  else if r = TapeRegister.length then wordTape (List.replicate bits.length true)
  else wordTape []

@[simp] theorem initializedTapes_input (bits : List Bool) :
    initializedTapes bits TapeRegister.input = wordTape bits := by
  simp [initializedTapes]

@[simp] theorem initializedTapes_length (bits : List Bool) :
    initializedTapes bits TapeRegister.length =
      wordTape (List.replicate bits.length true) := by
  simp [initializedTapes, TapeRegister.input, TapeRegister.length]

theorem initializedTapes_other (bits : List Bool) (r : TapeRegister)
    (hi : r ≠ TapeRegister.input) (hl : r ≠ TapeRegister.length) :
    initializedTapes bits r = wordTape [] := by
  simp [initializedTapes, hi, hl]

@[simp] theorem initializedTapes_head (bits : List Bool) (r : TapeRegister) :
    (initializedTapes bits r).head = cleanAtom .home := by
  simp only [initializedTapes]
  split_ifs <;> exact wordTape_head _

private theorem init_step {q q' : InitState} {T U : TapeTapes}
    {writes : TapeHeads} {moves : TapeMoves}
    (hc : initializationCode q (fun r => (T r).head) = some (q', writes, moves))
    (ht : ∀ r, (moves r).apply ((T r).write (writes r)) = U r) :
    TapeMultiProgram.step initializationCode ⟨q, T⟩ = some ⟨q', U⟩ := by
  have hu : multiTapeUpdate (⟨q, T⟩ : TapeMultiCfg InitState) q' writes moves =
      ⟨q', U⟩ := by
    change MultiTapeCfg.mk q' (fun r => (moves r).apply ((T r).write (writes r))) = _
    exact congrArg (MultiTapeCfg.mk q') (funext ht)
  change multiTapeStep initializationCode _ = _
  rw [multiTapeStep_eq_some (code := initializationCode)
    (c := (⟨q, T⟩ : TapeMultiCfg InitState)) hc, hu]

private theorem init_raw_left {Γ : Type uDepth1} [Inhabited Γ] (R : List Γ) :
    (Tape.mk₁ R).move Dir.left = Tape.mk₂ [] (default :: R) :=
  Tape.move_left_mk' (ListBlank.mk ([] : List Γ)) (ListBlank.mk R)

private theorem init_write_nil {Γ : Type uDepth2} [Inhabited Γ] (L : List Γ) (a : Γ) :
    (Tape.mk₂ L []).write a = Tape.mk₂ L [a] := rfl

/-- The intermediate tapes after writing their left boundary markers. -/
def initHomeTapes (bits : List Bool) : TapeTapes := fun r =>
  Tape.mk₂ [cleanAtom .home] (if r = TapeRegister.input then encodeInput bits else [])

/-- The tapes while scanning input bits and accumulating the unary length. -/
def initScanTapes (left right : List Bool) : TapeTapes := fun r =>
  if r = TapeRegister.input then
    Tape.mk₂ (encodeInput left ++ [cleanAtom .home]) (encodeInput right)
  else if r = TapeRegister.length then
    Tape.mk₂ (List.replicate left.length (rawInputSymbol true) ++ [cleanAtom .home]) []
  else wordTape []

/-- The tapes while returning input and length heads to their left markers. -/
def initRewindTapes (left right : List Bool) : TapeTapes := fun r =>
  if r = TapeRegister.input then
    Tape.mk₂ (encodeInput left ++ [cleanAtom .home])
      (encodeInput right ++ [cleanAtom .endMark])
  else if r = TapeRegister.length then
    Tape.mk₂ (List.replicate left.length (rawInputSymbol true) ++ [cleanAtom .home])
      (List.replicate right.length (rawInputSymbol true) ++ [cleanAtom .endMark])
  else wordTape []

private theorem initialization_start (bits : List Bool) :
    TapeMultiProgram.step initializationCode ⟨.start, rawInputTapes bits⟩ =
      some ⟨.home, fun r => (rawInputTapes bits r).move Dir.left⟩ := by
  apply init_step rfl
  intro r
  simp only [Tape.write_self, HeadMove.apply_left]

private theorem initialization_home (bits : List Bool) :
    TapeMultiProgram.step initializationCode
      ⟨.home, fun r => (rawInputTapes bits r).move Dir.left⟩ =
      some ⟨.prepare, initHomeTapes bits⟩ := by
  apply init_step rfl
  intro r
  by_cases hi : r = TapeRegister.input <;>
    simp [rawInputTapes, initHomeTapes, hi, init_raw_left,
      TapeWord.write_mk₂_cons, TapeWord.move_right_mk₂_cons]

private theorem initialization_prepare (bits : List Bool) :
    TapeMultiProgram.step initializationCode ⟨.prepare, initHomeTapes bits⟩ =
      some ⟨.scan, initScanTapes [] bits⟩ := by
  apply init_step rfl
  intro r
  by_cases hi : r = TapeRegister.input
  · subst r
    simp [initActive, initHomeTapes, initScanTapes, encodeInput]
  · by_cases hl : r = TapeRegister.length
    · subst r
      simp [initActive, initHomeTapes, initScanTapes, TapeRegister.input, TapeRegister.length]
    · simp [initActive, initHomeTapes, initScanTapes, hi, hl, init_write_nil,
        TapeWord.move_left_mk₂_cons, wordTape, encodeInput, Tape.mk₁]

private theorem initialization_scan_bit (left right : List Bool) (b : Bool) :
    TapeMultiProgram.step initializationCode ⟨.scan, initScanTapes left (b :: right)⟩ =
      some ⟨.scan, initScanTapes (b :: left) right⟩ := by
  apply init_step rfl
  intro r
  by_cases hi : r = TapeRegister.input
  · subst r
    simp [initActive, initScanTapes, encodeInput, TapeRegister.input,
      TapeRegister.length, TapeWord.move_right_mk₂_cons]
  · by_cases hl : r = TapeRegister.length
    · subst r
      simp [initActive, initScanTapes, TapeRegister.input, TapeRegister.length,
        init_write_nil, TapeWord.move_right_mk₂_cons, List.replicate_succ]
    · simp [initActive, initScanTapes, hi, hl, wordTape, Tape.mk₁,
        TapeWord.write_mk₂_cons]

private theorem initialization_scan_end (left : List Bool) :
    TapeMultiProgram.step initializationCode ⟨.scan, initScanTapes left []⟩ =
      some ⟨.rewind, initRewindTapes left []⟩ := by
  apply init_step (by rfl)
  intro r
  by_cases hi : r = TapeRegister.input
  · subst r
    simp [initActive, initScanTapes, initRewindTapes, encodeInput, init_write_nil]
  · by_cases hl : r = TapeRegister.length
    · subst r
      simp [initActive, initScanTapes, initRewindTapes, init_write_nil,
        TapeRegister.input, TapeRegister.length]
    · simp [initActive, initScanTapes, initRewindTapes, hi, hl, wordTape, Tape.mk₁,
        TapeWord.write_mk₂_cons]

private theorem initRewind_head_ne_home (left right : List Bool) :
    ((initRewindTapes left right TapeRegister.input).head).1 ≠ TapeAtom.home := by
  cases right <;> simp [initRewindTapes, encodeInput, rawInputSymbol, cleanAtom]

private theorem initialization_rewind_bit (left right : List Bool) (b : Bool) :
    TapeMultiProgram.step initializationCode ⟨.rewind, initRewindTapes (b :: left) right⟩ =
      some ⟨.rewind, initRewindTapes left (b :: right)⟩ := by
  apply init_step (writes := fun r => (initRewindTapes (b :: left) right r).head)
    (moves := fun r => if initActive r then .left else .stay) (by
      simp only [initializationCode, initRewind_head_ne_home, ↓reduceIte])
  intro r
  by_cases hi : r = TapeRegister.input
  · subst r
    simp [initActive, initRewindTapes, encodeInput, TapeWord.move_left_mk₂_cons]
  · by_cases hl : r = TapeRegister.length
    · subst r
      simp [initActive, initRewindTapes, TapeRegister.input, TapeRegister.length,
        List.replicate_succ, TapeWord.move_left_mk₂_cons]
    · simp [initActive, initRewindTapes, hi, hl, wordTape, Tape.mk₁,
        TapeWord.write_mk₂_cons]

private theorem initialization_rewind_home (right : List Bool) :
    TapeMultiProgram.step initializationCode ⟨.rewind, initRewindTapes [] right⟩ =
      some ⟨.rewind, initializedTapes right⟩ := by
  apply init_step (writes := fun r => (initRewindTapes [] right r).head)
    (moves := fun r => if initActive r then .left else .stay) (by
      simp only [initializationCode, initRewind_head_ne_home, ↓reduceIte])
  intro r
  by_cases hi : r = TapeRegister.input
  · subst r
    simp [initActive, initRewindTapes, initializedTapes, encodeInput,
      TapeWord.move_left_mk₂_cons, wordTape, Tape.mk₁]
  · by_cases hl : r = TapeRegister.length
    · subst r
      simp [initActive, initRewindTapes, initializedTapes, encodeInput,
        TapeRegister.input, TapeRegister.length, TapeWord.move_left_mk₂_cons,
        wordTape, Tape.mk₁]
    · simp [initActive, initRewindTapes, initializedTapes, hi, hl, wordTape, Tape.mk₁,
        TapeWord.write_mk₂_cons]

private theorem initialization_finish (bits : List Bool) :
    TapeMultiProgram.step initializationCode ⟨.rewind, initializedTapes bits⟩ =
      some ⟨.done, initializedTapes bits⟩ := by
  apply init_step (writes := fun r => (initializedTapes bits r).head)
    (moves := fun _ => .stay) (by simp [initializationCode])
  intro r
  simp only [Tape.write_self, HeadMove.apply_stay]

private theorem initialization_scan_runs (left right : List Bool) :
    RunsIn (TapeMultiProgram.step initializationCode)
      ⟨.scan, initScanTapes left right⟩
      ⟨.scan, initScanTapes (right.reverse ++ left) []⟩ right.length := by
  induction right generalizing left with
  | nil =>
      simpa using RunsIn.refl (TapeMultiProgram.step initializationCode)
        (⟨.scan, initScanTapes left []⟩ : TapeMultiCfg InitState)
  | cons b right ih =>
    have h := (RunsIn.single (initialization_scan_bit left right b)).trans (ih (b :: left))
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, Nat.add_comm] using h

private theorem initialization_rewind_runs (left right : List Bool) :
    RunsIn (TapeMultiProgram.step initializationCode)
      ⟨.rewind, initRewindTapes left right⟩
      ⟨.rewind, initializedTapes (left.reverse ++ right)⟩ (left.length + 1) := by
  induction left generalizing right with
  | nil => simpa using RunsIn.single (initialization_rewind_home right)
  | cons b left ih =>
    have h := (RunsIn.single (initialization_rewind_bit left right b)).trans (ih (b :: right))
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem initialization_runs (bits : List Bool) :
    RunsIn (TapeMultiProgram.step initializationCode)
      ⟨.start, rawInputTapes bits⟩ ⟨.done, initializedTapes bits⟩ (2 * bits.length + 6) := by
  have hsetup := ((RunsIn.single (initialization_start bits)).trans
    (RunsIn.single (initialization_home bits))).trans
    (RunsIn.single (initialization_prepare bits))
  have hscan := initialization_scan_runs [] bits
  simp only [List.append_nil] at hscan
  have hrewind := initialization_rewind_runs bits.reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hrewind
  have h := (((hsetup.trans hscan).trans
    (RunsIn.single (initialization_scan_end bits.reverse))).trans hrewind).trans
    (RunsIn.single (initialization_finish bits))
  exact h.mono (by omega)

@[simp] theorem initialization_done (T : TapeTapes) :
    TapeMultiProgram.step initializationCode ⟨.done, T⟩ = none := rfl

/-- The bundled finite multitape input-initialization machine. -/
def initializationMachine : FiniteMultiTapeMachine :=
  TapeMultiProgram.machine initializationCode .start (fun _ => true)

@[simp] theorem initializationMachine_init (bits : List Bool) :
    initializationMachine.init bits = ⟨.start, rawInputTapes bits⟩ := rfl

theorem initializationMachine_halts (bits : List Bool) :
    MultiTapeHaltsIn initializationMachine bits true (2 * bits.length + 6) := by
  apply (multiTapeHaltsIn_iff_runsIn _ _ _ _).2
  refine ⟨⟨.done, initializedTapes bits⟩, ?_, ?_, rfl⟩
  · exact initialization_runs bits
  · exact initialization_done _

end DepthThreeLowerBound

end Complexity
