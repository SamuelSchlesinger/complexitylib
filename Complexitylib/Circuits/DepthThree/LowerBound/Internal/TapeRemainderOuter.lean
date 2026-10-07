/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeRemainderSetup
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeCancel
public import Mathlib.Tactic.Linarith

/-!
# Unrestricted depth-three lower bound: tape remainder outer

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeRemainderOuter.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeRemainderOuter

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

/-- All scratch counters used by remainder cancellation are empty. -/
def ScratchEmpty (σ : TapeStore) : Prop :=
  σ loop1 = [] ∧ σ indexA = [] ∧ σ indexB = [] ∧ σ indexC = [] ∧ σ scratchA = []

/-- Control states for the body stage of the remainder outer routine. -/
abbrev BodyState := TapeRemainderSetup.SetupState ⊕
  (TapeCancel.State ⊕ TapeRemainderSetup.CleanupState)

/-- Transition function for the tail stage of the remainder outer routine. -/
def tailProgram : TapeMultiProgram (TapeCancel.State ⊕ TapeRemainderSetup.CleanupState) :=
  joinCode TapeCancel.program TapeRemainderSetup.cleanupProgram
    (fun _ => TapeRemainderSetup.cleanupStart)

/-- Transition function for the body stage of the remainder outer routine. -/
def bodyProgram : TapeMultiProgram BodyState :=
  joinCode TapeRemainderSetup.setupProgram tailProgram (fun _ => .inl TapeCancel.start)

/-- Initial control state of the body stage of the remainder outer routine. -/
def bodyStart : BodyState := .inl TapeRemainderSetup.setupStart
/-- Terminal control state of the body stage of the remainder outer routine. -/
def bodyDone : BodyState := .inr (.inr TapeRemainderSetup.cleanupDone)

/-- Transition budget for the remainder outer routine at its body stage. -/
def bodyCost (s r : ℕ) : ℕ :=
  (4*s + 12*r + 23) + 1 + (TapeCancel.cost s r + 1 + (4*s + 6*r + 17))

@[simp] theorem bodyProgram_done (h : TapeHeads) : bodyProgram bodyDone h = none := by
  simp [bodyProgram, bodyDone, tailProgram, joinCode,
    TapeRemainderSetup.cleanupProgram_done]

theorem cleanup_result (σ : TapeStore) (r s : ℕ) (out : List Bool)
    (hclean : ScratchEmpty σ) :
    TapeRemainderSetup.clearIndices
      (TapeCancel.resultStore (TapeRemainderSetup.preparedStore σ r s) r s out) =
      Function.update σ productBits out := by
  rcases hclean with ⟨hL, hA, hB, hC, hW⟩
  funext q
  by_cases ha : q = indexA
  · subst q
    simp [TapeRemainderSetup.clearIndices, Function.update,
      hA, indexA, indexB, indexC, productBits]
  · by_cases hb : q = indexB
    · subst q
      simp [TapeRemainderSetup.clearIndices, Function.update,
        hB, indexB, indexC, productBits]
    · by_cases hc : q = indexC
      · subst q
        simp [TapeRemainderSetup.clearIndices, Function.update,
          hC, indexC, productBits]
      · by_cases hl : q = loop1
        · subst q
          simp [TapeRemainderSetup.clearIndices, TapeCancel.resultStore,
            TapeCancelRow.frame, Function.update,
            hL, loop1, indexA, indexB, indexC, productBits]
        · by_cases hp : q = productBits
          · subst q
            simp [TapeRemainderSetup.clearIndices, TapeCancel.resultStore,
              TapeCancelRow.frame, Function.update,
              loop1, indexA, indexB, indexC, productBits]
          · simp [TapeRemainderSetup.clearIndices, TapeCancel.resultStore,
              TapeCancelRow.frame, TapeRemainderSetup.preparedStore, Function.update,
              ha, hb, hc, hl, hp]

theorem runs_body (σ : TapeStore) (p c : List Bool) (s : ℕ)
    (hP : σ polyBits = p) (hOut : σ productBits = c)
    (hDegree : σ ringDegree = List.replicate p.length true)
    (hLoop0 : σ loop0 = List.replicate s true) (hclean : ScratchEmpty σ)
    (hbound : s + p.length < c.length) :
    RunsIn bodyProgram.step (cfg bodyStart (storeTapes σ))
      (cfg bodyDone (storeTapes (Function.update σ productBits (cancelByUpdates p c s))))
      (bodyCost s p.length) := by
  rcases hclean with ⟨hL, hA, hB, hC, hW⟩
  let τ := TapeRemainderSetup.preparedStore σ p.length s
  let out := cancelByUpdates p c s
  let ρ := TapeCancel.resultStore τ p.length s out
  have hsetup := TapeRemainderSetup.runs_setup σ p.length s hLoop0 hDegree hL hA hB hC hW
  have hcancel := TapeCancel.runs_cancel τ p c s
    (by simp [τ, TapeRemainderSetup.preparedStore, hP,
      indexB, indexC, loop1, polyBits])
    (by simp [τ, TapeRemainderSetup.preparedStore, hOut,
      indexB, indexC, loop1, productBits])
    (by simp [τ, TapeRemainderSetup.preparedStore])
    (by simp [τ, TapeRemainderSetup.preparedStore, hA,
      indexB, indexC, loop1, indexA])
    (by simp [τ, TapeRemainderSetup.preparedStore, indexB, indexC, loop1])
    (by simp [τ, TapeRemainderSetup.preparedStore, indexC, loop1]) hbound
  have hcleanup := TapeRemainderSetup.runs_cleanup ρ p.length s
    (by simp [ρ, TapeCancel.resultStore])
    (by simp [ρ, TapeCancel.resultStore, TapeCancelRow.frame, τ,
      TapeRemainderSetup.preparedStore, loop1, indexA, indexB, indexC, productBits])
    (by simp [ρ, TapeCancel.resultStore])
  have hfinal : TapeRemainderSetup.clearIndices ρ = Function.update σ productBits out :=
    cleanup_result σ p.length s out ⟨hL, hA, hB, hC, hW⟩
  rw [hfinal] at hcleanup
  have htail := join_runs TapeCancel.program TapeRemainderSetup.cleanupProgram
    (fun _ => TapeRemainderSetup.cleanupStart) hcancel (TapeCancel.program_done _) hcleanup
  have hall := join_runs TapeRemainderSetup.setupProgram tailProgram
    (fun _ => .inl TapeCancel.start) hsetup
    (TapeRemainderSetup.setupProgram_done _) htail
  simpa only [bodyProgram, bodyStart, bodyDone, bodyCost, out] using hall

/-- Transition budget for the remainder outer routine at its iteration stage. -/
def iterationCost (r : ℕ) : ℕ := r * (6*r + 21) + 34*r + 62

theorem bodyCost_le (s r : ℕ) (hs : s ≤ r) :
    4 + 1 + bodyCost s r + 1 ≤ iterationCost r := by
  have hmul := Nat.mul_le_mul_left (2*r) hs
  unfold bodyCost TapeCancel.cost iterationCost
  nlinarith

/-- Control states of the remainder outer routine. -/
abbrev State := LoopState DecState BodyState

/-- Transition function of the remainder outer routine. -/
def program : TapeMultiProgram State :=
  loopCode (decProgram loop0) bodyProgram DecState.start bodyStart decPositive

/-- Initial control state of the remainder outer routine. -/
def start : State := loopTest DecState.start
/-- Terminal control state of the remainder outer routine. -/
def done : State := loopDone

/-- Tape-store invariant recording the loop counters and current output. -/
def frame (σ : TapeStore) (k : ℕ) (out : List Bool) : TapeStore :=
  fun q => if q = loop0 then List.replicate k true
    else if q = productBits then out else σ q

@[simp] theorem frame_counter (σ : TapeStore) (k : ℕ) (out : List Bool) :
    frame σ k out loop0 = List.replicate k true := by simp [frame]

@[simp] theorem frame_output (σ : TapeStore) (k : ℕ) (out : List Bool) :
    frame σ k out productBits = out := by simp [frame, loop0, productBits]

@[simp] theorem frame_poly (σ : TapeStore) (k : ℕ) (out : List Bool) :
    frame σ k out polyBits = σ polyBits := by simp [frame, loop0, productBits, polyBits]

@[simp] theorem frame_degree (σ : TapeStore) (k : ℕ) (out : List Bool) :
    frame σ k out ringDegree = σ ringDegree := by
  simp [frame, loop0, productBits, ringDegree]

theorem frame_clean (σ : TapeStore) (k : ℕ) (out : List Bool)
    (h : ScratchEmpty σ) : ScratchEmpty (frame σ k out) := by
  simpa [ScratchEmpty, frame, loop0, loop1, indexA, indexB, indexC, scratchA, productBits]
    using h

theorem update_counter (σ : TapeStore) (k k' : ℕ) (out : List Bool) :
    Function.update (frame σ k out) loop0 (List.replicate k' true) = frame σ k' out := by
  funext q
  by_cases h : q = loop0
  · subst q
    simp
  · simp [frame, Function.update, h]

theorem update_output (σ : TapeStore) (k : ℕ) (out out' : List Bool) :
    Function.update (frame σ k out) productBits out' = frame σ k out' := by
  funext q
  by_cases h : q = productBits
  · subst q
    simp
  · simp [frame, Function.update, h]

theorem runs_loop (σ : TapeStore) (p c : List Bool) (k : ℕ)
    (hP : σ polyBits = p)
    (hDegree : σ ringDegree = List.replicate p.length true)
    (hclean : ScratchEmpty σ) (hk : k ≤ p.length) (hsize : k + p.length ≤ c.length) :
    RunsIn program.step (cfg start (storeTapes (frame σ k c)))
      (cfg done (storeTapes (frame σ 0 (reduceByUpdates p k c))))
      (k * iterationCost p.length + 3) := by
  induction k generalizing c with
  | zero =>
      have hd := decrement_empty loop0 (storeTapes (frame σ 0 c)) (by simp)
      have he := loop_exit (decProgram loop0) bodyProgram DecState.start bodyStart
        decPositive hd rfl rfl
      simpa only [program, start, done, reduceByUpdates_zero, Nat.zero_mul, Nat.zero_add]
        using he
  | succ k ih =>
      let out := cancelByUpdates p c k
      have hd := decrement_cons loop0 (storeTapes (frame σ (k+1) c))
        (List.replicate k true) true (by simp [List.replicate_succ])
      have hd' : RunsIn (decProgram loop0).step
          (cfg DecState.start (storeTapes (frame σ (k+1) c)))
          (cfg (DecState.done true) (storeTapes (frame σ k c))) 4 := by
        simpa only [← storeTapes_update, update_counter] using hd
      have hb := runs_body (frame σ k c) p c k (by simpa using hP) (by simp)
        (by simpa using hDegree) (by simp) (frame_clean σ k c hclean) (by omega)
      have hb' : RunsIn bodyProgram.step (cfg bodyStart (storeTapes (frame σ k c)))
          (cfg bodyDone (storeTapes (frame σ k out))) (bodyCost k p.length) := by
        simpa only [update_output, out] using hb
      have hit := loop_iter (decProgram loop0) bodyProgram DecState.start bodyStart
        decPositive hd' rfl rfl hb' (bodyProgram_done _)
      have hit' := hit.mono (bodyCost_le k p.length (by omega))
      have hrest := ih out (by omega) (by simp only [out, cancelByUpdates_length]; omega)
      have hall := hit'.trans hrest
      have htime : iterationCost p.length + (k * iterationCost p.length + 3) =
          (k+1) * iterationCost p.length + 3 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [program, start, done, reduceByUpdates_step, out, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeRemainderOuter
end DepthThreeLowerBound

end Complexity
