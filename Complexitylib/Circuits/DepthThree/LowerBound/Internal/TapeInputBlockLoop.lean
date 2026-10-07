/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeReadPush
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Ring

/-!
# Unrestricted depth-three lower bound: tape input block loop

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeInputBlockLoop.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeInputBlockLoop

open TapeMultiProgram TapeCopy TapeRouting TapeUnary TapeArithmetic

/-- Register allocation for the input block loop routine. -/
abbrev Registers := Fin 5 ↪ TapeRegister

/-- The source register of the block-copy loop. -/
abbrev source (R : Registers) := R 0
/-- The source-position counter of the block-copy loop. -/
abbrev index (R : Registers) := R 1
/-- The remaining-length counter of the block-copy loop. -/
abbrev count (R : Registers) := R 2
/-- The scratch register of the block-copy loop. -/
abbrev scratch (R : Registers) := R 3
/-- The output register of the block-copy loop. -/
abbrev destination (R : Registers) := R 4

theorem register_eq (R : Registers) (i j : Fin 5) :
    R i = R j ↔ i = j := R.injective.eq_iff

theorem index_ne_source (R : Registers) : index R ≠ source R := by
  simp [index, source]

/-- Tape-store contents at the block stage of the input block loop routine. -/
def blockStore (R : Registers) (σ : TapeStore) (pos remaining : ℕ)
    (bits : List Bool) : TapeStore :=
  Function.update
    (Function.update (Function.update σ (count R) (List.replicate remaining true))
      (index R) (List.replicate pos true)) (destination R) bits

@[simp] theorem blockStore_source (R : Registers) (σ : TapeStore)
    (pos remaining : ℕ) (bits : List Bool) :
    blockStore R σ pos remaining bits (source R) = σ (source R) := by
  simp [blockStore, source, index, count, destination]

@[simp] theorem blockStore_index (R : Registers) (σ : TapeStore)
    (pos remaining : ℕ) (bits : List Bool) :
    blockStore R σ pos remaining bits (index R) = List.replicate pos true := by
  simp [blockStore, index, count, destination]

@[simp] theorem blockStore_count (R : Registers) (σ : TapeStore)
    (pos remaining : ℕ) (bits : List Bool) :
    blockStore R σ pos remaining bits (count R) = List.replicate remaining true := by
  simp [blockStore, index, count, destination]

@[simp] theorem blockStore_destination (R : Registers) (σ : TapeStore)
    (pos remaining : ℕ) (bits : List Bool) :
    blockStore R σ pos remaining bits (destination R) = bits := by
  simp [blockStore]

@[simp] theorem update_blockStore_count (R : Registers) (σ : TapeStore)
    (pos remaining remaining' : ℕ) (bits : List Bool) :
    Function.update (blockStore R σ pos remaining bits) (count R)
      (List.replicate remaining' true) = blockStore R σ pos remaining' bits := by
  funext q
  by_cases hc : q = count R <;> by_cases hi : q = index R <;>
    by_cases hd : q = destination R <;>
    simp_all [blockStore, Function.update, count, index, destination]

@[simp] theorem update_blockStore_index (R : Registers) (σ : TapeStore)
    (pos pos' remaining : ℕ) (bits : List Bool) :
    Function.update (blockStore R σ pos remaining bits) (index R)
      (List.replicate pos' true) = blockStore R σ pos' remaining bits := by
  funext q
  by_cases hc : q = count R <;> by_cases hi : q = index R <;>
    by_cases hd : q = destination R <;>
    simp_all [blockStore, Function.update, count, index, destination]

@[simp] theorem update_blockStore_destination (R : Registers) (σ : TapeStore)
    (pos remaining : ℕ) (bits bits' : List Bool) :
    Function.update (blockStore R σ pos remaining bits) (destination R) bits' =
      blockStore R σ pos remaining bits' := by
  simp only [blockStore, Function.update_idem]

/-- Control states for the body stage of the input block loop routine. -/
abbrev BodyState := DecState ⊕ TapeReadPush.State

/-- Transition function for the body stage of the input block loop routine. -/
def bodyProgram (R : Registers) : TapeMultiProgram BodyState :=
  joinCode (decProgram (index R))
    (TapeReadPush.program (index R) (source R) (destination R))
    (fun _ => TapeReadPush.start)

/-- Initial control state of the body stage of the input block loop routine. -/
def bodyStart : BodyState := .inl DecState.start
/-- Terminal control state of the body stage of the input block loop routine. -/
def bodyDone (b : Bool) : BodyState := .inr (TapeReadPush.done b)

@[simp] theorem body_done (R : Registers) (b : Bool) (h : TapeHeads) :
    bodyProgram R (bodyDone b) h = none := rfl

theorem runs_body (R : Registers) (σ : TapeStore) («prefix» suffix acc : List Bool)
    (b : Bool) (remaining : ℕ)
    (hsource : σ (source R) = «prefix» ++ b :: suffix) :
    RunsIn (bodyProgram R).step
      (cfg bodyStart (storeTapes
        (blockStore R σ («prefix».length + 1) remaining acc)))
      (cfg (bodyDone b) (storeTapes
        (blockStore R σ «prefix».length remaining (b :: acc))))
      (2 * «prefix».length + 12) := by
  have hd := decrement (index R)
    (storeTapes (blockStore R σ («prefix».length + 1) remaining acc))
    («prefix».length + 1) (by simp [counterTape])
  have hd' : RunsIn (decProgram (index R)).step
      (cfg DecState.start (storeTapes (blockStore R σ («prefix».length + 1) remaining acc)))
      (cfg (DecState.done true) (storeTapes (blockStore R σ «prefix».length remaining acc))) 4 := by
    simpa only [Nat.add_sub_cancel, Nat.zero_lt_succ, decide_true,
      counterTape, ← storeTapes_update, update_blockStore_index] using hd
  have hp := TapeReadPush.runs_store (index_ne_source R) (destination R)
    (blockStore R σ «prefix».length remaining acc) «prefix» suffix b
    (by simp) (by simpa using hsource)
  have hp' : RunsIn
      (TapeReadPush.program (index R) (source R) (destination R)).step
      (cfg TapeReadPush.start (storeTapes (blockStore R σ «prefix».length remaining acc)))
      (cfg (TapeReadPush.done b)
        (storeTapes (blockStore R σ «prefix».length remaining (b :: acc))))
      (2 * «prefix».length + 7) := by
    simpa only [blockStore_destination, update_blockStore_destination] using hp
  have hall := join_runs (decProgram (index R))
    (TapeReadPush.program (index R) (source R) (destination R))
    (fun _ => TapeReadPush.start) hd' rfl hp'
  have ht : 4 + 1 + (2 * «prefix».length + 7) = 2 * «prefix».length + 12 := by omega
  simpa only [bodyProgram, bodyStart, bodyDone, ht] using hall

/-- Control states of the input block loop routine. -/
abbrev State := LoopState DecState BodyState

/-- Transition function of the input block loop routine. -/
def program (R : Registers) : TapeMultiProgram State :=
  loopCode (decProgram (count R)) (bodyProgram R)
    DecState.start bodyStart decPositive

/-- Initial control state of the input block loop routine. -/
def start : State := loopTest DecState.start
/-- Terminal control state of the input block loop routine. -/
def done : State := loopDone

@[simp] theorem program_done (R : Registers) (h : TapeHeads) :
    program R done h = none := rfl

theorem runs_block (R : Registers) (σ : TapeStore)
    («prefix» block suffix acc : List Bool)
    (hsource : σ (source R) = «prefix» ++ block ++ suffix) :
    RunsIn (program R).step
      (cfg start (storeTapes
        (blockStore R σ («prefix».length + block.length) block.length acc)))
      (cfg done (storeTapes (blockStore R σ «prefix».length 0 (block ++ acc))))
      (block.length * (2 * «prefix».length + block.length + 17) + 3) := by
  induction block using List.reverseRecOn generalizing suffix acc with
  | nil =>
    have hd := decrement_empty (count R)
      (storeTapes (blockStore R σ «prefix».length 0 acc)) (by simp [])
    have he := loop_exit (decProgram (count R)) (bodyProgram R)
      DecState.start bodyStart decPositive hd rfl rfl
    simpa only [program, start, done, List.length_nil, List.nil_append,
      Nat.add_zero, Nat.zero_mul, Nat.zero_add] using he
  | append_singleton block b ih =>
    have hd := decrement (count R)
      (storeTapes (blockStore R σ («prefix».length + block.length + 1)
        (block.length + 1) acc)) (block.length + 1) (by simp [counterTape])
    have hd' : RunsIn (decProgram (count R)).step
        (cfg DecState.start (storeTapes (blockStore R σ
          («prefix».length + block.length + 1) (block.length + 1) acc)))
        (cfg (DecState.done true) (storeTapes (blockStore R σ
          («prefix».length + block.length + 1) block.length acc))) 4 := by
      simpa only [Nat.add_sub_cancel, Nat.zero_lt_succ, decide_true,
        counterTape, ← storeTapes_update, update_blockStore_count] using hd
    have hs : σ (source R) = («prefix» ++ block) ++ b :: suffix := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hsource
    have hb := runs_body R σ («prefix» ++ block) suffix acc b block.length hs
    simp only [List.length_append] at hb
    have hit := loop_iter (decProgram (count R)) (bodyProgram R)
      DecState.start bodyStart decPositive hd' rfl rfl hb (by simp)
    have hs' : σ (source R) = «prefix» ++ block ++ (b :: suffix) := hs
    have hrest := ih (b :: suffix) (b :: acc) hs'
    have hall := hit.trans hrest
    have ht : 4 + 1 + (2 * («prefix».length + block.length) + 12) + 1 +
        (block.length * (2 * «prefix».length + block.length + 17) + 3) =
        (block.length + 1) * (2 * «prefix».length + (block.length + 1) + 17) + 3 := by
      ring
    have hi : «prefix».length + (block.length + 1) = «prefix».length + block.length + 1 := by
      omega
    simpa only [program, start, done, List.length_append, List.length_singleton,
      List.append_assoc, List.cons_append, List.nil_append, hi, ht] using hall

end TapeInputBlockLoop
end DepthThreeLowerBound

end Complexity
