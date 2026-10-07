/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeRouting
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeUnary
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeUnaryCompare
public import Mathlib.Data.Nat.Init
public import Lean.Elab.Tactic.Omega

/-!
# Unrestricted depth-three lower bound: tape for loop

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeForLoop.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7 uDepth8 uDepth9 uDepth10 uDepth11
universe uDepth12 uDepth13 uDepth14 uDepth15

namespace DepthThreeLowerBound
namespace TapeForLoop

open TapeMultiProgram TapeRouting TapeUnary

/-- Control states for the body stage of the for loop routine. -/
abbrev BodyState (Q : Type uDepth1) := Q ⊕ IncState
/-- Control states of the for loop routine. -/
abbrev State (Q : Type uDepth2) := LoopState TapeUnaryCompare.State (BodyState Q)

/-- Transition function for the body stage of the for loop routine. -/
def bodyProgram {Q : Type uDepth3} (r : TapeRegister) (P : TapeMultiProgram Q) :
    TapeMultiProgram (BodyState Q) :=
  joinCode P (incProgram r) (fun _ => IncState.start)

/-- Initial control state of the body stage of the for loop routine. -/
def bodyStart {Q : Type uDepth4} (q : Q) : BodyState Q := .inl q

/-- Terminal control state of the body stage of the for loop routine. -/
def bodyDone {Q : Type uDepth5} : BodyState Q := .inr .done

/-- Continue the counted loop exactly when its index is less than its bound. -/
def again : TapeUnaryCompare.State → Bool
  | .done .lt => true
  | _ => false

/-- Transition function of the for loop routine. -/
def program {Q : Type uDepth6} (r s : TapeRegister) (P : TapeMultiProgram Q)
    (qStart : Q) : TapeMultiProgram (State Q) :=
  loopCode (TapeUnaryCompare.program r s) (bodyProgram r P)
    (.scan .beginR) (bodyStart qStart) again

/-- Initial control state of the for loop routine. -/
def start {Q : Type uDepth7} : State Q := loopTest (.scan .beginR)

/-- Terminal control state of the for loop routine. -/
def done {Q : Type uDepth8} : State Q := loopDone

@[simp] theorem body_done {Q : Type uDepth9} (r : TapeRegister) (P : TapeMultiProgram Q)
    (h : TapeHeads) : bodyProgram r P bodyDone h = none := rfl

@[simp] theorem program_done {Q : Type uDepth10} (r s : TapeRegister)
    (P : TapeMultiProgram Q) (qStart : Q) (h : TapeHeads) :
    program r s P qStart done h = none := rfl

theorem runs_body {Q : Type uDepth11} (r : TapeRegister) (P : TapeMultiProgram Q)
    (qStart qDone : Q) (T U : TapeTapes) (j B : ℕ)
    (hU : U r = counterTape (j + 1))
    (hbody : RunsIn P.step (cfg qStart T)
      (cfg qDone (Function.update U r (counterTape j))) B)
    (hhalt : P qDone (heads (Function.update U r (counterTape j))) = none) :
    RunsIn (bodyProgram r P).step (cfg (bodyStart qStart) T)
      (cfg bodyDone U) (B + 3) := by
  have hi := increment r (Function.update U r (counterTape j)) j
    (Function.update_self _ _ _)
  have hu : Function.update (Function.update U r (counterTape j)) r
      (counterTape (j + 1)) = U := by
    rw [Function.update_idem]
    exact Function.update_eq_self_iff.mpr hU.symm
  rw [hu] at hi
  have h := join_runs P (incProgram r) (fun _ => IncState.start) hbody hhalt hi
  simpa only [bodyProgram, bodyStart, bodyDone, Nat.add_assoc] using h

theorem runs_iteration {Q : Type uDepth12} {r s : TapeRegister} (hrs : r ≠ s)
    (P : TapeMultiProgram Q) (qStart qDone : Q) (T U : TapeTapes) (j n B : ℕ)
    (hj : j < n) (hR : T r = counterTape j) (hS : T s = counterTape n)
    (hU : U r = counterTape (j + 1))
    (hbody : RunsIn P.step (cfg qStart T)
      (cfg qDone (Function.update U r (counterTape j))) B)
    (hhalt : P qDone (heads (Function.update U r (counterTape j))) = none) :
    RunsIn (program r s P qStart).step (cfg start T) (cfg start U)
      (B + 4 * j + 12) := by
  have ht := TapeUnaryCompare.runs_compare hrs T j n hR hS
  have ho := (TapeUnaryCompareScan.result_eq_lt_iff j n).mpr hj
  rw [Nat.min_eq_left hj.le, ho] at ht
  have hb := runs_body r P qStart qDone T U j B hU hbody hhalt
  have h := loop_iter (TapeUnaryCompare.program r s) (bodyProgram r P)
    (.scan .beginR) (bodyStart qStart) again ht rfl rfl hb rfl
  exact h.mono (by omega)

theorem runs_exit {Q : Type uDepth13} {r s : TapeRegister} (hrs : r ≠ s)
    (P : TapeMultiProgram Q) (qStart : Q) (T : TapeTapes) (n : ℕ)
    (hR : T r = counterTape n) (hS : T s = counterTape n) :
    RunsIn (program r s P qStart).step (cfg start T) (cfg done T) (4 * n + 8) := by
  have ht := TapeUnaryCompare.runs_compare hrs T n n hR hS
  have ho := (TapeUnaryCompareScan.result_eq_eq_iff n n).mpr rfl
  rw [Nat.min_self, ho] at ht
  have h := loop_exit (TapeUnaryCompare.program r s) (bodyProgram r P)
    (.scan .beginR) (bodyStart qStart) again ht rfl rfl
  exact h.mono (by omega)

theorem runs {Q : Type uDepth14} {r s : TapeRegister} (hrs : r ≠ s)
    (P : TapeMultiProgram Q) (qStart qDone : Q) (σ : ℕ → TapeTapes) (n B : ℕ)
    (hindex : ∀ j ≤ n, σ j r = counterTape j)
    (hbound : ∀ j ≤ n, σ j s = counterTape n)
    (hbody : ∀ j < n, RunsIn P.step (cfg qStart (σ j))
      (cfg qDone (Function.update (σ (j + 1)) r (counterTape j))) B)
    (hhalt : ∀ h, P qDone h = none) (i : ℕ) (hi : i ≤ n) :
    RunsIn (program r s P qStart).step (cfg start (σ i)) (cfg done (σ n))
      ((n - i) * (B + 4 * n + 12) + (4 * n + 8)) := by
  refine Nat.decreasingInduction (motive := fun j _ =>
    RunsIn (program r s P qStart).step (cfg start (σ j)) (cfg done (σ n))
      ((n - j) * (B + 4 * n + 12) + (4 * n + 8))) ?_ ?_ hi
  · intro j hj ih
    have hjn : j ≤ n := hj.le
    have hstep := runs_iteration hrs P qStart qDone (σ j) (σ (j + 1)) j n B hj
      (hindex j hjn) (hbound j hjn) (hindex (j + 1) hj)
      (hbody j hj) (hhalt _)
    have hstep' := hstep.mono (show B + 4 * j + 12 ≤ B + 4 * n + 12 by omega)
    have hall := hstep'.trans ih
    have hd : n - j = (n - (j + 1)) + 1 := by omega
    apply hall.mono
    rw [hd, Nat.add_mul, Nat.one_mul]
    omega
  · simpa only [Nat.sub_self, Nat.zero_mul, Nat.zero_add] using
      runs_exit hrs P qStart (σ n) n (hindex n (Nat.le_refl n))
        (hbound n (Nat.le_refl n))

theorem runs_zero {Q : Type uDepth15} {r s : TapeRegister} (hrs : r ≠ s)
    (P : TapeMultiProgram Q) (qStart qDone : Q) (σ : ℕ → TapeTapes) (n B : ℕ)
    (hindex : ∀ j ≤ n, σ j r = counterTape j)
    (hbound : ∀ j ≤ n, σ j s = counterTape n)
    (hbody : ∀ j < n, RunsIn P.step (cfg qStart (σ j))
      (cfg qDone (Function.update (σ (j + 1)) r (counterTape j))) B)
    (hhalt : ∀ h, P qDone h = none) :
    RunsIn (program r s P qStart).step (cfg start (σ 0)) (cfg done (σ n))
      (n * (B + 4 * n + 12) + (4 * n + 8)) := by
  simpa only [Nat.sub_zero] using
    runs hrs P qStart qDone σ n B hindex hbound hbody hhalt 0 (Nat.zero_le n)

end TapeForLoop
end DepthThreeLowerBound

end Complexity
