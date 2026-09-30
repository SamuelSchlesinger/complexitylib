/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.Bridge
public import Complexitylib.Classes.P.Pairing

/-!
# Initialized iteration with a preserved input

`initializedStep init step` keeps its state in the first component of `pair`
and its unchanged input in the second. An empty state is the initialization
sentinel: the first call on `pair [] x` installs `init x`, and later calls apply
`step x` while the state is nonempty. The step may depend on the original input.

`initializedStep_iterate` identifies the packed orbit with the ordinary orbit
of `step x`, with one extra call for initialization. Its nonemptiness hypothesis
covers exactly the states on which a step is taken; the final state may be empty.
Without that hypothesis an empty intermediate state would initialize again.

The controller uses the total projections `pairFst` and `pairSnd` on arbitrary
strings; no validity of malformed pair encodings is assumed. Its polynomial-time
closure theorem and orbit equation are shared by Savitch's and IP's space-bounded
iterations, independently of their state encodings and invariants.
-/

@[expose] public section

namespace Complexity

/-- Initialize an empty state, or take one step, preserving the input on the right. -/
def initializedStep (init : List Bool → List Bool)
    (step : List Bool → List Bool → List Bool) (z : List Bool) : List Bool :=
  pair (Cobham.selectHead (emptyFlag (pairFst z))
    (init (pairSnd z)) (step (pairSnd z) (pairFst z))) (pairSnd z)

/-- The controller's action on an encoded state and input. -/
theorem initializedStep_pair (init : List Bool → List Bool)
    (step : List Bool → List Bool → List Bool) (s x : List Bool) :
    initializedStep init step (pair s x)
      = pair (Cobham.selectHead (emptyFlag s) (init x) (step x s)) x := by
  rw [initializedStep, pairFst_pair, pairSnd_pair]

/-- The empty sentinel installs the initial state. -/
theorem initializedStep_nil (init : List Bool → List Bool)
    (step : List Bool → List Bool → List Bool) (x : List Bool) :
    initializedStep init step (pair [] x) = pair (init x) x := by
  rw [initializedStep_pair, emptyFlag_nil, Cobham.selectHead]
  simp

/-- A nonempty state takes one step instead of initializing again. -/
theorem initializedStep_step (init : List Bool → List Bool)
    (step : List Bool → List Bool → List Bool) (s x : List Bool) (hs : s ≠ []) :
    initializedStep init step (pair s x) = pair (step x s) x := by
  cases s with
  | nil => exact absurd rfl hs
  | cons b t =>
      rw [initializedStep_pair, emptyFlag_cons, Cobham.selectHead]
      simp

/-- Packing an orbit costs one initialization call. Only states on which another
step is taken must be nonempty, so the state after the last step may be empty. -/
theorem initializedStep_iterate (init : List Bool → List Bool)
    (step : List Bool → List Bool → List Bool) (x : List Bool) :
    ∀ n : ℕ, (∀ j < n, (step x)^[j] (init x) ≠ []) →
      (initializedStep init step)^[n + 1] (pair [] x)
        = pair ((step x)^[n] (init x)) x := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [Function.iterate_one, initializedStep_nil, Function.iterate_zero_apply]
  | succ n ih =>
      intro hne
      rw [Function.iterate_succ_apply', ih (fun j hj => hne j (Nat.lt_succ_of_lt hj)),
        initializedStep_step _ _ _ _ (hne n (Nat.lt_succ_self n)),
        Function.iterate_succ_apply']

/-- A polynomial-time initializer and step give a polynomial-time packed controller.
The step receives the unchanged input and current state through the pair projections. -/
theorem initializedStep_mem_FP {init : List Bool → List Bool}
    {step : List Bool → List Bool → List Bool} (hinit : init ∈ FP)
    (hstep : (fun z => step (pairSnd z) (pairFst z)) ∈ FP) :
    initializedStep init step ∈ FP :=
  mem_FP_pair
    (Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP pairFst_mem_FP)
      (mem_FP_comp pairSnd_mem_FP hinit) hstep) pairSnd_mem_FP

end Complexity
