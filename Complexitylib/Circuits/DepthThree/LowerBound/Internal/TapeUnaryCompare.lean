/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeUnaryCompareScan
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeRewind
public import Lean.Elab.Tactic.Omega

/-!
# Unrestricted depth-three lower bound: tape unary compare

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeUnaryCompare.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

namespace DepthThreeLowerBound

open TapeMultiProgram

namespace TapeUnaryCompare

/-- Control states of the unary compare routine. -/
inductive State
  | scan (q : TapeUnaryCompareScan.State)
  | rewindR (result : Ordering)
  | rewindS (result : Ordering)
  | done (result : Ordering)
  deriving DecidableEq, Fintype, Inhabited

/-- Control states for the scan stage of the unary compare routine. -/
def scanState : TapeUnaryCompareScan.State → State
  | .done o => .rewindR o
  | q => .scan q

/-- Control states for the rewind r stage of the unary compare routine. -/
def rewindRState (o : Ordering) : TapeRewind.State → State
  | .run => .rewindR o
  | .done => .rewindS o

/-- Control states for the rewind s stage of the unary compare routine. -/
def rewindSState (o : Ordering) : TapeRewind.State → State
  | .run => .rewindS o
  | .done => .done o

/-- Map only the target control state of an optional transition instruction. -/
def mapInstruction {Q : Type uDepth1} {R : Type uDepth2} (f : Q → R)
    (instruction : Option (Q × TapeHeads × TapeMoves)) :
    Option (R × TapeHeads × TapeMoves) :=
  instruction.map fun out => (f out.1, out.2.1, out.2.2)

/-- Transition function of the unary compare routine. -/
def program (r s : TapeRegister) : TapeMultiProgram State
  | .scan q, h => mapInstruction scanState (TapeUnaryCompareScan.code r s q h)
  | .rewindR o, h => mapInstruction (rewindRState o) (TapeRewind.program r .run h)
  | .rewindS o, h => mapInstruction (rewindSState o) (TapeRewind.program s .run h)
  | .done _, _ => none

theorem scan_code (r s : TapeRegister) (q : TapeUnaryCompareScan.State)
    (h : TapeHeads) (q' : TapeUnaryCompareScan.State) (writes : TapeHeads)
    (moves : TapeMoves)
    (hc : TapeUnaryCompareScan.code r s q h = some (q', writes, moves)) :
    program r s (scanState q) h = some (scanState q', writes, moves) := by
  cases q with
  | beginR =>
      simp only [scanState, program, hc, mapInstruction, Option.map_some]
  | beginS =>
      simp only [scanState, program, hc, mapInstruction, Option.map_some]
  | scan =>
      simp only [scanState, program, hc, mapInstruction, Option.map_some]
  | advanceS =>
      simp only [scanState, program, hc, mapInstruction, Option.map_some]
  | done o => simp [TapeUnaryCompareScan.code] at hc

theorem rewindR_code (r s : TapeRegister) (o : Ordering) (q : TapeRewind.State)
    (h : TapeHeads) (q' : TapeRewind.State) (writes : TapeHeads) (moves : TapeMoves)
    (hc : TapeRewind.program r q h = some (q', writes, moves)) :
    program r s (rewindRState o q) h = some (rewindRState o q', writes, moves) := by
  cases q with
  | run =>
      simp only [rewindRState, program, hc, mapInstruction, Option.map_some]
  | done => simp [TapeRewind.program] at hc

theorem rewindS_code (r s : TapeRegister) (o : Ordering) (q : TapeRewind.State)
    (h : TapeHeads) (q' : TapeRewind.State) (writes : TapeHeads) (moves : TapeMoves)
    (hc : TapeRewind.program s q h = some (q', writes, moves)) :
    program r s (rewindSState o q) h = some (rewindSState o q', writes, moves) := by
  cases q with
  | run =>
      simp only [rewindSState, program, hc, mapInstruction, Option.map_some]
  | done => simp [TapeRewind.program] at hc

theorem runs_rewindR (r s : TapeRegister) (o : Ordering) (T : TapeTapes)
    (before after : List Bool) :
    RunsIn (program r s).step
      (cfg (.rewindR o) (Function.update T r (cursorTape before after)))
      (cfg (.rewindS o) (Function.update T r (wordTape (before ++ after))))
      (before.length + 2) := by
  simpa only [mapCfg, cfg, rewindRState] using
    runs_map (TapeRewind.program r) (program r s) (rewindRState o)
      (rewindR_code r s o) (TapeRewind.runs_cursor r T before after)

theorem runs_rewindS (r s : TapeRegister) (o : Ordering) (T : TapeTapes)
    (before after : List Bool) :
    RunsIn (program r s).step
      (cfg (.rewindS o) (Function.update T s (cursorTape before after)))
      (cfg (.done o) (Function.update T s (wordTape (before ++ after))))
      (before.length + 2) := by
  simpa only [mapCfg, cfg, rewindSState] using
    runs_map (TapeRewind.program s) (program r s) (rewindSState o)
      (rewindS_code r s o) (TapeRewind.runs_cursor s T before after)

theorem runs_compare {r s : TapeRegister} (hrs : r ≠ s) (T : TapeTapes) (m n : ℕ)
    (hR : T r = wordTape (List.replicate m true))
    (hS : T s = wordTape (List.replicate n true)) :
    RunsIn (program r s).step (cfg (.scan .beginR) T)
      (cfg (.done (TapeUnaryCompareScan.result m n)) T) (4 * min m n + 7) := by
  let k := min m n
  let o := TapeUnaryCompareScan.result m n
  let T₂ := Function.update T s (TapeUnaryCompareScan.unaryCursor k (n - k))
  have hsplitR : k + (m - k) = m := by
    have hk : k ≤ m := Nat.min_le_left m n
    omega
  have hsplitS : k + (n - k) = n := by
    have hk : k ≤ n := Nat.min_le_right m n
    omega
  have hscan : RunsIn (program r s).step (cfg (.scan .beginR) T)
      (cfg (.rewindR o) (TapeUnaryCompareScan.scanTapes r s T k (m-k) (n-k)))
      (2*k+3) := by
    simpa only [mapCfg, cfg, scanState] using
      runs_map (TapeUnaryCompareScan.code r s) (program r s) scanState
        (scan_code r s) (TapeUnaryCompareScan.runs_compare hrs T m n hR hS)
  have hstartR : Function.update T₂ r (TapeUnaryCompareScan.unaryCursor k (m-k)) =
      TapeUnaryCompareScan.scanTapes r s T k (m-k) (n-k) := by
    exact (Function.update_comm hrs _ _ T).symm
  have hendR : Function.update T₂ r
      (wordTape (List.replicate k true ++ List.replicate (m-k) true)) = T₂ := by
    apply Function.update_eq_self_iff.mpr
    simp only [List.replicate_append_replicate, hsplitR]
    simpa only [T₂, Function.update_of_ne hrs] using hR.symm
  have hrewindR := runs_rewindR r s o T₂ (List.replicate k true)
    (List.replicate (m-k) true)
  change RunsIn (program r s).step
    (cfg (.rewindR o) (Function.update T₂ r (TapeUnaryCompareScan.unaryCursor k (m-k))))
    (cfg (.rewindS o) (Function.update T₂ r
      (wordTape (List.replicate k true ++ List.replicate (m-k) true))))
    ((List.replicate k true).length + 2) at hrewindR
  rw [hstartR, hendR, List.length_replicate] at hrewindR
  have hendS : Function.update T s
      (wordTape (List.replicate k true ++ List.replicate (n-k) true)) = T := by
    apply Function.update_eq_self_iff.mpr
    simpa only [List.replicate_append_replicate, hsplitS] using hS.symm
  have hrewindS := runs_rewindS r s o T (List.replicate k true)
    (List.replicate (n-k) true)
  rw [hendS, List.length_replicate] at hrewindS
  have hrun := (hscan.trans hrewindR).trans hrewindS
  have hbound : (2*k+3+(k+2))+(k+2) = 4 * min m n + 7 := by omega
  simpa only [hbound] using hrun

theorem runs_compare_linear {r s : TapeRegister} (hrs : r ≠ s) (T : TapeTapes)
    (m n : ℕ) (hR : T r = wordTape (List.replicate m true))
    (hS : T s = wordTape (List.replicate n true)) :
    RunsIn (program r s).step (cfg (.scan .beginR) T)
      (cfg (.done (TapeUnaryCompareScan.result m n)) T) (7 * (m+n+1)) := by
  apply (runs_compare hrs T m n hR hS).mono
  have hmin := Nat.min_le_left m n
  omega

end TapeUnaryCompare
end DepthThreeLowerBound

end Complexity
