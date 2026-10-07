/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeMultiRoutines
public import Lean.Elab.Tactic.Omega

/-!
# Unrestricted depth-three lower bound: tape unary compare scan

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeUnaryCompareScan.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeUnaryCompareScan

open Turing TapeMultiProgram

/-- Control states of the unary compare scan routine. -/
inductive State where
  | beginR
  | beginS
  | scan
  | advanceS
  | done (result : Ordering)
  deriving DecidableEq, Fintype, Inhabited

/-- Compare two natural numbers, returning their ordering. -/
def result (m n : ℕ) : Ordering :=
  if m < n then .lt else if m = n then .eq else .gt

@[simp] theorem result_succ (m n : ℕ) : result (m + 1) (n + 1) = result m n := by
  simp only [result, Nat.succ_lt_succ_iff, Nat.succ.injEq]

theorem result_eq_lt_iff (m n : ℕ) : result m n = .lt ↔ m < n := by
  by_cases h : m < n
  · simp [result, h]
  · by_cases he : m = n <;> simp [result, h, he]

theorem result_eq_eq_iff (m n : ℕ) : result m n = .eq ↔ m = n := by
  by_cases h : m < n
  · simp [result, h, Nat.ne_of_lt h]
  · by_cases he : m = n <;> simp [result, h, he]

theorem result_eq_gt_iff (m n : ℕ) : result m n = .gt ↔ n < m := by
  by_cases h : m < n
  · have hn : ¬n < m := Nat.not_lt_of_ge h.le
    simp [result, h, hn]
  · by_cases he : m = n
    · subst n
      simp [result]
    · have hn : n < m := lt_of_le_of_ne (Nat.le_of_not_gt h) (Ne.symm he)
      simp [result, h, he, hn]

/-- A unary tape with a specified number of bits before and after the head. -/
def unaryCursor (k n : ℕ) : Tape TapeSymbol :=
  cursorTape (List.replicate k true) (List.replicate n true)

@[simp] theorem unaryCursor_head_zero (k : ℕ) :
    (unaryCursor k 0).head = cleanAtom .endMark := rfl

@[simp] theorem unaryCursor_head_succ (k n : ℕ) :
    (unaryCursor k (n + 1)).head = rawInputSymbol true := rfl

theorem unaryCursor_right (k n : ℕ) :
    (unaryCursor k (n + 1)).move Dir.right = unaryCursor (k + 1) n := by
  unfold unaryCursor
  rw [List.replicate_succ, cursorTape_right, ← List.replicate_succ']

/-- Replace the tapes at two selected registers. -/
def pairTapes (r s : TapeRegister) (T : TapeTapes)
    (R S : Tape TapeSymbol) : TapeTapes :=
  Function.update (Function.update T r R) s S

@[simp] theorem pairTapes_r {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (R S : Tape TapeSymbol) : pairTapes r s T R S r = R := by
  simp [pairTapes, hrs]

@[simp] theorem pairTapes_s (r s : TapeRegister)
    (T : TapeTapes) (R S : Tape TapeSymbol) : pairTapes r s T R S s = S := by
  simp [pairTapes]

theorem pairTapes_other (r s : TapeRegister) (T : TapeTapes)
    (R S : Tape TapeSymbol) (j : TapeRegister) (hjr : j ≠ r) (hjs : j ≠ s) :
    pairTapes r s T R S j = T j := by
  simp [pairTapes, hjr, hjs]

theorem update_pairTapes_r {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (R S R' : Tape TapeSymbol) :
    Function.update (pairTapes r s T R S) r R' = pairTapes r s T R' S := by
  unfold pairTapes
  rw [Function.update_comm (Ne.symm hrs), Function.update_idem]

theorem update_pairTapes_s (r s : TapeRegister)
    (T : TapeTapes) (R S S' : Tape TapeSymbol) :
    Function.update (pairTapes r s T R S) s S' = pairTapes r s T R S' := by
  simp only [pairTapes, Function.update_idem]

/-- The pair of unary tapes during their synchronized comparison scan. -/
def scanTapes (r s : TapeRegister) (T : TapeTapes) (k m n : ℕ) : TapeTapes :=
  pairTapes r s T (unaryCursor k m) (unaryCursor k n)

theorem scanTapes_other (r s : TapeRegister) (T : TapeTapes) (k m n : ℕ)
    (j : TapeRegister) (hjr : j ≠ r) (hjs : j ≠ s) :
    scanTapes r s T k m n j = T j :=
  pairTapes_other r s T _ _ j hjr hjs

/-- Transition function of the unary compare scan routine. -/
def code (r s : TapeRegister) : TapeMultiProgram State
  | .beginR, h => move r .right .beginS h
  | .beginS, h => move s .right .scan h
  | .scan, h =>
      if isAtom .endMark r h then
        if isAtom .endMark s h then jump (.done .eq) h
        else jump (.done .lt) h
      else if isAtom .endMark s h then jump (.done .gt) h
      else move r .right .advanceS h
  | .advanceS, h => move s .right .scan h
  | .done _, _ => none

theorem step_scan_zero_zero {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (k : ℕ) :
    (code r s).step (cfg .scan (scanTapes r s T k 0 0)) =
      some (cfg (.done .eq) (scanTapes r s T k 0 0)) := by
  apply step_jump
  simp [code, isAtom, heads, scanTapes, hrs, cleanAtom]

theorem step_scan_zero_succ {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (k n : ℕ) :
    (code r s).step (cfg .scan (scanTapes r s T k 0 (n + 1))) =
      some (cfg (.done .lt) (scanTapes r s T k 0 (n + 1))) := by
  apply step_jump
  simp [code, isAtom, heads, scanTapes, hrs, rawInputSymbol, cleanAtom]

theorem step_scan_succ_zero {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (k m : ℕ) :
    (code r s).step (cfg .scan (scanTapes r s T k (m + 1) 0)) =
      some (cfg (.done .gt) (scanTapes r s T k (m + 1) 0)) := by
  apply step_jump
  simp [code, isAtom, heads, scanTapes, hrs, rawInputSymbol, cleanAtom]

theorem step_scan_succ_succ {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (k m n : ℕ) :
    (code r s).step (cfg .scan (scanTapes r s T k (m + 1) (n + 1))) =
      some (cfg .advanceS (pairTapes r s T
        (unaryCursor (k + 1) m) (unaryCursor k (n + 1)))) := by
  have h := step_move (code r s) State.scan State.advanceS
    (scanTapes r s T k (m + 1) (n + 1)) r HeadMove.right
    (by simp [code, isAtom, heads, scanTapes, hrs, rawInputSymbol, cleanAtom])
  simpa only [scanTapes, pairTapes_r hrs, HeadMove.apply_right,
    unaryCursor_right, update_pairTapes_r hrs] using h

theorem step_advanceS (r s : TapeRegister) (T : TapeTapes)
    (R S : Tape TapeSymbol) :
    (code r s).step (cfg .advanceS (pairTapes r s T R S)) =
      some (cfg .scan (pairTapes r s T R (S.move Dir.right))) := by
  have h := step_move (code r s) State.advanceS State.scan
    (pairTapes r s T R S) s HeadMove.right rfl
  simpa only [pairTapes_s, HeadMove.apply_right, update_pairTapes_s] using h

theorem runs_scan {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (k m n : ℕ) :
    RunsIn (code r s).step (cfg .scan (scanTapes r s T k m n))
      (cfg (.done (result m n))
        (scanTapes r s T (k + min m n) (m - min m n) (n - min m n)))
      (2 * min m n + 1) := by
  induction m generalizing k n with
  | zero =>
      cases n with
      | zero =>
          simpa [result] using RunsIn.single (step_scan_zero_zero hrs T k)
      | succ n =>
          simpa [result] using RunsIn.single (step_scan_zero_succ hrs T k n)
  | succ m ih =>
      cases n with
      | zero =>
          simpa [result] using RunsIn.single (step_scan_succ_zero hrs T k m)
      | succ n =>
          have h₁ := RunsIn.single (step_scan_succ_succ hrs T k m n)
          have h₂ : RunsIn (code r s).step
              (cfg .advanceS (pairTapes r s T
                (unaryCursor (k + 1) m) (unaryCursor k (n + 1))))
              (cfg .scan (scanTapes r s T (k + 1) m n)) 1 := by
            simpa only [unaryCursor_right, scanTapes] using
              RunsIn.single (step_advanceS r s T
                (unaryCursor (k + 1) m) (unaryCursor k (n + 1)))
          have h := (h₁.trans h₂).trans (ih (k + 1) n)
          have hbound : (1 + 1) + (2 * min m n + 1) ≤
              2 * min (m + 1) (n + 1) + 1 := by
            rw [Nat.succ_min_succ]
            omega
          simpa only [Nat.succ_min_succ, Nat.succ_sub_succ, result_succ,
            Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using h.mono hbound

theorem runs_entry {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (m n : ℕ)
    (hR : T r = wordTape (List.replicate m true))
    (hS : T s = wordTape (List.replicate n true)) :
    RunsIn (code r s).step (cfg .beginR T)
      (cfg .scan (scanTapes r s T 0 m n)) 2 := by
  let U := Function.update T r ((T r).move Dir.right)
  have h₁ := step_move (code r s) State.beginR State.beginS T r HeadMove.right rfl
  have h₂ := step_move (code r s) State.beginS State.scan U s HeadMove.right rfl
  have h₁' : (code r s).step (cfg .beginR T) = some (cfg .beginS U) := h₁
  have h₂' : (code r s).step (cfg .beginS U) =
      some (cfg .scan (scanTapes r s T 0 m n)) := by
    simpa only [U, Function.update_of_ne (Ne.symm hrs), hR, hS,
      HeadMove.apply_right, wordTape_right, scanTapes, pairTapes, unaryCursor,
      List.replicate_zero] using h₂
  exact (RunsIn.single h₁').trans (RunsIn.single h₂')

theorem runs_compare {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (m n : ℕ)
    (hR : T r = wordTape (List.replicate m true))
    (hS : T s = wordTape (List.replicate n true)) :
    RunsIn (code r s).step (cfg .beginR T)
      (cfg (.done (result m n))
        (scanTapes r s T (min m n) (m - min m n) (n - min m n)))
      (2 * min m n + 3) := by
  have h : RunsIn (code r s).step (cfg .beginR T)
      (cfg (.done (result m n))
        (scanTapes r s T (min m n) (m - min m n) (n - min m n)))
      (2 + (2 * min m n + 1)) := by
    simpa only [Nat.zero_add] using
      (runs_entry hrs T m n hR hS).trans (runs_scan hrs T 0 m n)
  exact h.mono (by omega)

theorem prefix_append_left (m n : ℕ) :
    List.replicate (min m n) true ++ List.replicate (m - min m n) true =
      List.replicate m true := by
  rw [List.replicate_append_replicate, Nat.add_sub_of_le (Nat.min_le_left m n)]

theorem prefix_append_right (m n : ℕ) :
    List.replicate (min m n) true ++ List.replicate (n - min m n) true =
      List.replicate n true := by
  rw [List.replicate_append_replicate, Nat.add_sub_of_le (Nat.min_le_right m n)]

@[simp] theorem step_done (r s : TapeRegister) (T : TapeTapes) (o : Ordering) :
    (code r s).step (cfg (.done o) T) = none := rfl

end TapeUnaryCompareScan
end DepthThreeLowerBound

end Complexity
