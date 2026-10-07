/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeHornerBody

/-!
# Unrestricted depth-three lower bound: tape horner loop

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeHornerLoop.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeHornerLoop

open TapeMultiProgram TapeRouting TapeRegister TapeUnary TapeArithmetic TapeHornerMultiply

/-- Control states of the horner loop routine. -/
abbrev State := LoopState DecState TapeHornerBody.State

/-- Transition function of the horner loop routine. -/
def program : TapeMultiProgram State :=
  loopCode (decProgram loop2) TapeHornerBody.program DecState.start TapeHornerBody.start
    decPositive

/-- Initial control state of the horner loop routine. -/
def start : State := loopTest DecState.start
/-- Terminal control state of the horner loop routine. -/
def done : State := loopDone

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

/-- Tape-store invariant recording the loop counters and current output. -/
def frame (σ : TapeStore) (remaining offset : ℕ) (a : List Bool) : TapeStore :=
  Function.update (Function.update (Function.update σ loop2 (List.replicate remaining true))
    loop3 (List.replicate offset true)) accumBits a

@[simp] theorem frame_count (σ : TapeStore) (k j : ℕ) (a : List Bool) :
    frame σ k j a loop2 = List.replicate k true := by
  simp [frame, loop2, loop3, accumBits]

@[simp] theorem frame_cursor (σ : TapeStore) (k j : ℕ) (a : List Bool) :
    frame σ k j a loop3 = List.replicate j true := by
  simp [frame, loop2, loop3, accumBits]

@[simp] theorem frame_accum (σ : TapeStore) (k j : ℕ) (a : List Bool) :
    frame σ k j a accumBits = a := by simp [frame]

theorem frame_workspace (σ : TapeStore) (k j r : ℕ) (a : List Bool)
    (hW : Workspace σ r) : Workspace (frame σ k j a) r := by
  rcases hW with ⟨hd, h0, h1, hi, hj, hk, hs, ho⟩
  constructor <;>
    simp_all [frame, Function.update, loop2, loop3, accumBits, ringDegree, loop0, loop1,
      indexA, indexB, indexC, scratchA, productBits]

@[simp] theorem update_frame_count (σ : TapeStore) (k k' j : ℕ) (a : List Bool) :
    Function.update (frame σ k j a) loop2 (List.replicate k' true) = frame σ k' j a := by
  funext q
  by_cases h2 : q = loop2 <;> by_cases h3 : q = loop3 <;> by_cases ha : q = accumBits <;>
    simp_all [frame, Function.update, loop2, loop3, accumBits]

@[simp] theorem update_frame_cursor (σ : TapeStore) (k j j' : ℕ) (a : List Bool) :
    Function.update (frame σ k j a) loop3 (List.replicate j' true) = frame σ k j' a := by
  funext q
  by_cases h3 : q = loop3 <;> by_cases ha : q = accumBits <;>
    simp_all [frame, Function.update, loop2, loop3, accumBits]

@[simp] theorem update_frame_accum (σ : TapeStore) (k j : ℕ) (a b : List Bool) :
    Function.update (frame σ k j a) accumBits b = frame σ k j b := by
  simp only [frame, Function.update_idem]

theorem body_cost_mono (r m n : ℕ) (hmn : m ≤ n) :
    TapeHornerBody.cost r m ≤ TapeHornerBody.cost r n := by
  have hm : r * (2 * m + r + 19) ≤ r * (2 * n + r + 19) :=
    Nat.mul_le_mul_left r (by omega)
  unfold TapeHornerBody.cost
  omega

theorem runs_loop (σ : TapeStore) (p h : List Bool) (bs : List (List Bool))
    (suffix a : List Bool) (r N : ℕ)
    (hW : Workspace σ r) (hP : σ polyBits = p) (hH : σ hashBits = h)
    (hp : p.length = r) (hh : h.length = r) (ha : a.length = r)
    (hblocks : ∀ b ∈ bs, b.length = r)
    (hsource : σ coeffBits = bs.flatten ++ suffix)
    (hN : bs.flatten.length ≤ N) (hcount : σ loop4 = []) (hbuffer : σ scratchB = []) :
    RunsIn program.step
      (cfg start (storeTapes (frame σ bs.length bs.flatten.length a)))
      (cfg done (storeTapes (frame σ 0 0 (hornerFrom r p h bs a))))
      (bs.length * (TapeHornerBody.cost r N + 6) + 3) := by
  induction bs using List.reverseRecOn generalizing suffix a with
  | nil =>
      have hd := decrement_empty loop2 (storeTapes (frame σ 0 0 a))
        (by simp [])
      have he := loop_exit (decProgram loop2) TapeHornerBody.program
        DecState.start TapeHornerBody.start decPositive hd rfl rfl
      simpa [program, start, done] using he
  | append_singleton bs b ih =>
      have hb : b.length = r := hblocks b (by simp)
      have hbs : ∀ c ∈ bs, c.length = r := fun c hc =>
        hblocks c (List.mem_append_left [b] hc)
      have hlen : (bs ++ [b]).flatten.length = bs.flatten.length + r := by
        simp [hb]
      have hsrc : σ coeffBits = bs.flatten ++ b ++ suffix := by
        simpa only [List.flatten_append, List.flatten_singleton] using hsource
      have hNb : bs.flatten.length ≤ N := by rw [hlen] at hN; omega
      have hd := decrement loop2
        (storeTapes (frame σ (bs.length + 1) (bs.flatten.length + r) a))
        (bs.length + 1) (by simp [counterTape])
      have hd' : RunsIn (decProgram loop2).step
          (cfg DecState.start (storeTapes (frame σ (bs.length + 1) (bs.flatten.length + r) a)))
          (cfg (DecState.done true) (storeTapes (frame σ bs.length (bs.flatten.length + r) a))) 4
            := by
        simpa only [Nat.add_sub_cancel, Nat.zero_lt_succ, decide_true,
          counterTape, ← storeTapes_update, update_frame_count] using hd
      have hbody := TapeHornerBody.runs_body
        (frame σ bs.length (bs.flatten.length + r) a) p h a bs.flatten b suffix r
        (frame_workspace σ _ _ r a hW)
        (by simp [frame, hP, polyBits, loop2, loop3, accumBits])
        (by simp [frame, hH, hashBits, loop2, loop3, accumBits])
        (by simp) hp hh ha hb
        (by simp [frame, hsrc, coeffBits, loop2, loop3, accumBits])
        (by simp)
        (by simp [frame, hcount, loop4, loop2, loop3, accumBits])
        (by simp [frame, hbuffer, scratchB, loop2, loop3, accumBits])
      simp only [update_frame_cursor, update_frame_accum] at hbody
      have hbody' := hbody.mono (body_cost_mono r bs.flatten.length N hNb)
      have hit := loop_iter (decProgram loop2) TapeHornerBody.program
        DecState.start TapeHornerBody.start decPositive hd' rfl rfl hbody' rfl
      have hsrc' : σ coeffBits = bs.flatten ++ (b ++ suffix) := by
        simpa only [List.append_assoc] using hsrc
      have hrest := ih (suffix := b ++ suffix) (a := hornerStep r p h b a)
        (hornerStep_length r p h b a hb) hbs hsrc' hNb
      have hall := hit.trans hrest
      have ht : (4 + 1 + TapeHornerBody.cost r N + 1) +
          (bs.length * (TapeHornerBody.cost r N + 6) + 3) =
          (bs.length + 1) * (TapeHornerBody.cost r N + 6) + 3 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [program, start, done, List.length_append, List.length_singleton, hlen,
        hornerFrom_append_singleton, ht] using hall

end TapeHornerLoop
end DepthThreeLowerBound

end Complexity
