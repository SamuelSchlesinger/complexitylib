/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Parked
public import Complexitylib.Models.TuringMachine.Repetition.Internal.ScheduleArithmetic
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Votes

/-!
# Outer schedule and boundary assertions for fixed-time repetition

This internal module splits the full wrapper choice string into the two setup
choices and per-trial simulation and administrative slices. It also packages
the completed-vote invariant and states the exact trial-boundary assertion used
by the outer correctness induction.

The actual outer induction is deliberately separate: this file supplies its
index algebra, choice slices, vote bookkeeping, and target predicate.

## Main results

- `NTM.repeatSetupChoices`, `repeatSimulationChoices`, `repeatAdminChoices` —
  exact choice slices
- `NTM.repeatSimulationChoices_eq_block` — compact-seed alignment
- `NTM.RepeatCompletedVotes` — completed vote-prefix invariant
- `NTM.RepeatBoundary`, `RepeatOuterClaim` — outer-induction specification
-/


@[expose] public section

namespace Complexity

namespace NTM

variable {n k T : ℕ}

/-! ### Exact full-seed slices -/

/-- Global position of setup choice `a`. -/
def repeatSetupChoiceIdx (k T : ℕ) (a : Fin 2) : Fin (repeatAtTimeSteps k T) :=
  finSumFinEquiv (Sum.inl a : Fin 2 ⊕ Fin (k * repeatAtTimeStride T))

/-- Global position of offset `s` in trial stride `j`. -/
def repeatStrideChoiceIdx (T : ℕ) (j : Fin k) (s : Fin (repeatAtTimeStride T)) :
    Fin (repeatAtTimeSteps k T) :=
  finSumFinEquiv
    (Sum.inr (finProdFinEquiv (j, s)) : Fin 2 ⊕ Fin (k * repeatAtTimeStride T))

/-- Embed a simulation offset into the beginning of a trial stride. -/
def repeatSimulationOffset (T : ℕ) (t : Fin T) : Fin (repeatAtTimeStride T) :=
  ⟨t.val, by simp only [repeatAtTimeStride]; omega⟩

/-- Embed an administrative offset after the `T` simulation choices. -/
def repeatAdminOffset (T : ℕ) (a : Fin (T + 2)) : Fin (repeatAtTimeStride T) :=
  ⟨T + a.val, by simp only [repeatAtTimeStride]; omega⟩

/-- The two leading setup choices of a full repetition seed. -/
def repeatSetupChoices (choices : Fin (repeatAtTimeSteps k T) → Bool) :
    Fin 2 → Bool :=
  fun a => choices (repeatSetupChoiceIdx k T a)

/-- All choices in trial stride `j`. -/
def repeatStrideChoices (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (j : Fin k) : Fin (repeatAtTimeStride T) → Bool :=
  fun s => choices (repeatStrideChoiceIdx T j s)

/-- The `T` source-simulation choices in trial `j`. -/
def repeatSimulationChoices (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (j : Fin k) : Fin T → Bool :=
  fun t => repeatStrideChoices choices j (repeatSimulationOffset T t)

/-- The `T + 2` rewind-and-finish choices in trial `j`. -/
def repeatAdminChoices (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (j : Fin k) : Fin (T + 2) → Bool :=
  fun a => repeatStrideChoices choices j (repeatAdminOffset T a)

/-- Setup indices retain their local numeric value. -/
@[simp] theorem repeatSetupChoiceIdx_val (k T : ℕ) (a : Fin 2) :
    (repeatSetupChoiceIdx k T a).val = a.val := by
  simp [repeatSetupChoiceIdx]

/-- A stride index has the advertised row-major global position. -/
@[simp] theorem repeatStrideChoiceIdx_val (T : ℕ) (j : Fin k)
    (s : Fin (repeatAtTimeStride T)) :
    (repeatStrideChoiceIdx T j s).val =
      2 + j.val * repeatAtTimeStride T + s.val := by
  simp [repeatStrideChoiceIdx, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm]

/-- Trial/offset coordinates inject into the full schedule. -/
theorem repeatStrideChoiceIdx_injective (T : ℕ) :
    Function.Injective
      (fun p : Fin k × Fin (repeatAtTimeStride T) => repeatStrideChoiceIdx T p.1 p.2) := by
  intro a b h
  apply Prod.ext
  · exact congrArg Prod.fst (finProdFinEquiv.injective
      (Sum.inr.inj (finSumFinEquiv.injective h)))
  · exact congrArg Prod.snd (finProdFinEquiv.injective
      (Sum.inr.inj (finSumFinEquiv.injective h)))

/-- Setup and stride positions are disjoint. -/
theorem repeatSetupChoiceIdx_ne_stride (k T : ℕ) (a : Fin 2) (j : Fin k)
    (s : Fin (repeatAtTimeStride T)) :
    repeatSetupChoiceIdx k T a ≠ repeatStrideChoiceIdx T j s := by
  intro h
  have := finSumFinEquiv.injective h
  simp at this

/-- The generic stride embedding agrees with the machine simulation index. -/
theorem repeatStrideChoiceIdx_sim (T : ℕ) (j : Fin k) (t : Fin T) :
    repeatStrideChoiceIdx T j (repeatSimulationOffset T t) = repeatChoiceIdx T j t := by
  apply Fin.ext
  rw [repeatStrideChoiceIdx_val]
  simp [repeatSimulationOffset, repeatAtTimeStride, repeatChoiceIdx]

/-- No simulation choice is an administrative choice, even across trials. -/
theorem repeatSimulationChoiceIdx_ne_admin (T : ℕ) (j l : Fin k)
    (t : Fin T) (a : Fin (T + 2)) :
    repeatChoiceIdx T j t ≠ repeatStrideChoiceIdx T l (repeatAdminOffset T a) := by
  rw [← repeatStrideChoiceIdx_sim]
  intro h
  have hp := repeatStrideChoiceIdx_injective T
    (a₁ := (j, repeatSimulationOffset T t))
    (a₂ := (l, repeatAdminOffset T a)) h
  have hoff := congrArg (fun p => p.2.val) hp
  simp only [repeatSimulationOffset, repeatAdminOffset] at hoff
  omega

/-- A trial's simulation slice is exactly its block of the compact random seed. -/
@[simp] theorem repeatSimulationChoices_eq_block
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (j : Fin k) :
    repeatSimulationChoices choices j =
      blocksEquiv k T (repeatRandomSeed k T choices) j := by
  funext t
  simp only [repeatSimulationChoices, repeatStrideChoices,
    repeatStrideChoiceIdx_sim, blocksEquiv_apply,
    repeatRandomSeed_apply_repeatChoiceIdx_internal]

/-- Pointwise form of the simulation slice. -/
@[simp] theorem repeatSimulationChoices_apply
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (j : Fin k) (t : Fin T) :
    repeatSimulationChoices choices j t = choices (repeatChoiceIdx T j t) := by
  simp [repeatSimulationChoices, repeatStrideChoices, repeatStrideChoiceIdx_sim]

/-- Pointwise form of the administrative slice. -/
@[simp] theorem repeatAdminChoices_apply
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (j : Fin k)
    (a : Fin (T + 2)) :
    repeatAdminChoices choices j a =
      choices (repeatStrideChoiceIdx T j (repeatAdminOffset T a)) := rfl

/-! ### Trace prefixes at trial boundaries -/

/-- Include a shorter trial-boundary prefix in the full repetition schedule. -/
def repeatPrefixIdx (T : ℕ) {m k : ℕ} (hm : m ≤ k) :
    Fin (repeatAtTimeSteps m T) → Fin (repeatAtTimeSteps k T) :=
  fun i => ⟨i.val, by
    apply lt_of_lt_of_le i.isLt
    simp only [repeatAtTimeSteps]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hm) 2⟩

/-- Restrict a full choice string to the boundary after `m` trials. -/
def repeatPrefixChoices (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (m : ℕ) (hm : m ≤ k) : Fin (repeatAtTimeSteps m T) → Bool :=
  fun i => choices (repeatPrefixIdx T hm i)

/-- Pointwise form of prefix restriction. -/
@[simp] theorem repeatPrefixChoices_apply
    (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (m : ℕ) (hm : m ≤ k) (i : Fin (repeatAtTimeSteps m T)) :
    repeatPrefixChoices choices m hm i = choices (repeatPrefixIdx T hm i) := rfl

/-- Restricting at the final boundary returns the full choice string. -/
theorem repeatPrefixChoices_self
    (choices : Fin (repeatAtTimeSteps k T) → Bool) :
    repeatPrefixChoices choices k (Nat.le_refl k) = choices := by
  funext i
  apply congrArg choices
  apply Fin.ext
  rfl

/-- Wrapper configuration after the exact prefix ending at trial boundary `m`. -/
def repeatBoundaryCfg (tm : NTM n) (x : List Bool)
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (m : ℕ) (hm : m ≤ k) :
    Cfg (k * (n + 1)) (RepeatQ tm k T) :=
  (repeatAtTime tm k T).trace (repeatAtTimeSteps m T)
    (repeatPrefixChoices choices m hm) ((repeatAtTime tm k T).initCfg x)

/-! ### Completed-vote and outer-boundary assertions -/

/-- Vote vector agrees with source trials below boundary `m` and is false above it. -/
def RepeatCompletedVotes (tm : NTM n) (x : List Bool)
    (seed : Fin (k * T) → Bool) (votes : Fin k → Bool) (m : ℕ) : Prop :=
  RepeatVotesThrough (repeatVotes tm x k T seed) votes m

/-- No trials completed means every stored vote is false. -/
theorem RepeatCompletedVotes.zero (tm : NTM n) (x : List Bool)
    (seed : Fin (k * T) → Bool) :
    RepeatCompletedVotes tm x seed (fun _ => false) 0 :=
  RepeatVotesThrough.zero _

/-- Recording trial `j` advances the completed-vote boundary. -/
theorem RepeatCompletedVotes.update (tm : NTM n) (x : List Bool)
    (seed : Fin (k * T) → Bool) (votes : Fin k → Bool) (j : Fin k)
    (h : RepeatCompletedVotes tm x seed votes j.val) :
    RepeatCompletedVotes tm x seed
      (Function.update votes j (repeatVotes tm x k T seed j)) (j.val + 1) := by
  exact RepeatVotesThrough.update j.isLt h

/-- At the final boundary the stored vector is the complete source vote vector. -/
theorem RepeatCompletedVotes.eq_expected (tm : NTM n) (x : List Bool)
    (seed : Fin (k * T) → Bool) (votes : Fin k → Bool)
    (h : RepeatCompletedVotes tm x seed votes k) :
    votes = repeatVotes tm x k T seed :=
  RepeatVotesThrough.eq_expected h

/-- Control state at the start of trial `j`, including the zero-time branch. -/
def repeatTrialStartState (tm : NTM n) (j : Fin k) (votes : Fin k → Bool) :
    RepeatQ tm k T :=
  if hT : 0 < T then .run j ⟨0, hT⟩ tm.qstart votes
  else .rewind j ⟨0, by omega⟩ tm.qstart votes false (fun _ => false)

/-- Target assertion after `m` completed trials. Before the final boundary the
wrapper is at the exact next-trial start with the expected vote prefix and fresh
frame; at `m = k` it has halted with the majority verdict. -/
def RepeatBoundary (tm : NTM n) (x : List Bool) (seed : Fin (k * T) → Bool)
    (m : ℕ) (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) : Prop :=
  if hm : m < k then
    let j : Fin k := ⟨m, hm⟩
    ∃ votes : Fin k → Bool,
      RepeatCompletedVotes tm x seed votes m ∧
        C.state = repeatTrialStartState tm j votes ∧
        repeatProjectCfg tm j tm.qstart C = tm.initCfg x ∧
        RepeatFrame x j C ∧ RepeatOtherParked j C
  else
    C.state = RepeatQ.halt ∧ C.output.head = 1 ∧
      C.output.cells 1 = Γ.ofBool (majority (repeatVotes tm x k T seed))

/-- Fully formulated outer-induction claim over every exact schedule prefix. -/
def RepeatOuterClaim (tm : NTM n) (x : List Bool)
    (choices : Fin (repeatAtTimeSteps k T) → Bool) : Prop :=
  ∀ (m : ℕ) (hm : m ≤ k),
    RepeatBoundary tm x (repeatRandomSeed k T choices) m
      (repeatBoundaryCfg tm x choices m hm)

/-- Extract the next-trial assertion from the outer claim before the last boundary. -/
theorem RepeatOuterClaim.next {tm : NTM n} {x : List Bool}
    {choices : Fin (repeatAtTimeSteps k T) → Bool}
    (h : RepeatOuterClaim tm x choices) (m : ℕ) (hm : m < k) :
    let j : Fin k := ⟨m, hm⟩
    ∃ votes : Fin k → Bool,
      RepeatCompletedVotes tm x (repeatRandomSeed k T choices) votes m ∧
        (repeatBoundaryCfg tm x choices m (Nat.le_of_lt hm)).state =
          repeatTrialStartState tm j votes ∧
        repeatProjectCfg tm j tm.qstart
          (repeatBoundaryCfg tm x choices m (Nat.le_of_lt hm)) = tm.initCfg x ∧
        RepeatFrame x j (repeatBoundaryCfg tm x choices m (Nat.le_of_lt hm)) ∧
        RepeatOtherParked j
          (repeatBoundaryCfg tm x choices m (Nat.le_of_lt hm)) := by
  have hb := h m (Nat.le_of_lt hm)
  rw [RepeatBoundary, dite_eq_left hm] at hb
  simpa only using hb

/-- Extract the final halted majority assertion from the outer claim. -/
theorem RepeatOuterClaim.final {tm : NTM n} {x : List Bool}
    {choices : Fin (repeatAtTimeSteps k T) → Bool}
    (h : RepeatOuterClaim tm x choices) :
    let C := repeatBoundaryCfg tm x choices k (Nat.le_refl k)
    C.state = RepeatQ.halt ∧ C.output.head = 1 ∧
      C.output.cells 1 = Γ.ofBool
        (majority (repeatVotes tm x k T (repeatRandomSeed k T choices))) := by
  simpa [RepeatBoundary] using h k (Nat.le_refl k)

end NTM

end Complexity
