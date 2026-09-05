/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.SingleTape.Internal.Pad
public import Complexitylib.Models.TuringMachine.SingleTape.Internal
public import Complexitylib.Models.TuringMachine.SingleTape.Internal.Sim
public import Complexitylib.Models.TuringMachine.SingleTape.Internal.Delta
public import Complexitylib.Models.TuringMachine.SingleTape.Internal.Correctness
public import Complexitylib.Asymptotics

/-!
# Multi-tape → single-tape simulation

A nondeterministic machine with `k` work tapes can be simulated by one with a
single work tape, preserving the decided language with only polynomial time
overhead (the classic `O(T²)` multi-tape-to-single-tape simulation).

This is a reusable robustness lemma:

* **Cook–Levin** (`SAT/CookLevin.lean`) uses it so the computation-tableau
  formula only has to track one work tape instead of `k`.
* **Universal machines** are far simpler to construct when they need only
  simulate a single-work-tape machine.

## Decomposition

* `singleTapeSim N : NTM 1` — the simulating machine (`SingleTape/Sim.lean`),
  for `k ≥ 1`; 0-work-tape machines are handled by padding (`Pad.lean`).
* `singleTapeSimTime T` — the `(T + n + 1)²` time overhead.
* `singleTapeSim_allPathsHaltIn`, `singleTapeSim_acceptsInTime_iff` — the two
  behavioural facts (timing + acceptance equivalence), assembled from the
  forward (`acceptsInTime_singleTapeSim_of_acceptsInTime`) and reverse
  (`halted_singleTapeSim_of_trace_qhalt`) correspondence theorems of
  `SingleTape/Correctness.lean`.
* `singleTapeSimTime_bigO` — the overhead stays polynomial.

`singleTapeSim_decidesInTime` and `exists_singleTape_decidesInTime` are assembled from these.
-/


@[expose] public section

namespace Complexity

open Complexity

namespace NTM

/-- Time overhead of the single-tape simulation: the classic quadratic blow-up
    `(T + n + 1)²`, times a per-machine constant `16·(k+1)` that absorbs the
    block width (each super-position is `3k` cells) and the four sweeps per
    simulated step. The constant is deliberately generous; only the `=O` class
    (which absorbs it) is used downstream. -/
def singleTapeSimTime (k : ℕ) (T : ℕ → ℕ) : ℕ → ℕ :=
  fun n => 16 * (k + 1) * (T n + n + 1) ^ 2

/-- The simulation's time overhead stays polynomial. -/
theorem singleTapeSimTime_bigO {k : ℕ} {T : ℕ → ℕ} {c : ℕ} (hTO : T =O (· ^ c)) :
    singleTapeSimTime k T =O (· ^ (2 * c + 2)) := by
  -- `T n + n + 1` is `O(n^(c+1))`: each summand is.
  have hsum : (fun n => T n + n + 1) =O ((· ^ (c + 1)) : ℕ → ℕ) := by
    have hT : T =O ((· ^ (c + 1)) : ℕ → ℕ) :=
      hTO.trans (BigO.pow_le_pow_right (Nat.le_succ c))
    have hn : (fun n : ℕ => n) =O ((· ^ (c + 1)) : ℕ → ℕ) := by
      simpa [pow_one] using (BigO.pow_le_pow_right (j := 1) (k := c + 1) (by omega))
    exact BigO.add (BigO.add hT hn) (BigO.const_le_pow 1 (c + 1))
  -- Squaring stays polynomial: `(n^(c+1))² = n^(2c+2)`.
  have hmul : (fun n => (T n + n + 1) * (T n + n + 1))
      =O (fun n => n ^ (c + 1) * n ^ (c + 1)) := BigO.mul hsum hsum
  have hsq : (fun n => (T n + n + 1) ^ 2) =O (fun n => (T n + n + 1) * (T n + n + 1)) :=
    BigO.of_le fun n => le_of_eq (by rw [pow_two])
  have hR : (fun n : ℕ => n ^ (c + 1) * n ^ (c + 1)) =O ((· ^ (2 * c + 2)) : ℕ → ℕ) :=
    BigO.of_le fun n => le_of_eq (by rw [← pow_add]; congr 1; omega)
  -- the `16·(k+1)` factor is a constant multiple, absorbed by `=O`
  exact BigO.const_mul_left (16 * (k + 1)) ((hsq.trans hmul).trans hR)

/-- The simulator halts on all computation paths within the overhead time bound,
    whenever `N` does: an arbitrary simulator choice stream induces an `N`-run
    (read off at the closed-form decision positions), `N` halts on it within
    `T`, and the simulator then halts right after its corresponding macro-step
    (`SingleTape.halted_singleTapeSim_of_trace_qhalt`). -/
theorem singleTapeSim_allPathsHaltIn {k : ℕ} (N : NTM k) (hk : 1 ≤ k) {T : ℕ → ℕ}
    (hN : N.AllPathsHaltIn T) :
    (singleTapeSim N).AllPathsHaltIn (singleTapeSimTime k T) := by
  intro x choices
  -- extend the finite choice function to a stream
  set ch : ℕ → Bool := fun j =>
    if h : j < singleTapeSimTime k T x.length then choices ⟨j, h⟩ else false with hch
  have hhaltN : (N.trace (T x.length)
      (fun i => SingleTape.inducedChoices k ch i.val) (N.initCfg x)).state = N.qhalt :=
    hN x _
  obtain ⟨m, hm, hhalted, -⟩ :=
    SingleTape.halted_singleTapeSim_of_trace_qhalt N hk ch x (T x.length) hhaltN
  have hle : m ≤ singleTapeSimTime k T x.length :=
    le_trans hm (SingleTape.mul_macroBound_succ_le k (T x.length) x.length)
  have hagree : ∀ i : Fin m, choices ⟨i.val, lt_of_lt_of_le i.isLt hle⟩ = ch i.val := by
    intro i
    simp only [hch]
    rw [dite_eq_left (lt_of_lt_of_le i.isLt hle)]
  rw [(singleTapeSim N).trace_mono hle hagree hhalted]
  exact hhalted

/-- The simulator accepts `x` within the overhead time bound iff `N` accepts `x`
    within its original time bound.

    The all-paths-halt hypothesis `hN` is necessary for the forward direction:
    the simulator's quadratic budget `16(k+1)(T+n+1)²` leaves room to complete
    `N`-runs *longer* than `T n`, so without `hN` the simulator could accept
    along a path whose induced `N`-run accepts only after the bound. -/
theorem singleTapeSim_acceptsInTime_iff {k : ℕ} (N : NTM k) (hk : 1 ≤ k) (T : ℕ → ℕ)
    (hN : N.AllPathsHaltIn T) (x : List Bool) :
    (singleTapeSim N).AcceptsInTime x (singleTapeSimTime k T x.length)
      ↔ N.AcceptsInTime x (T x.length) := by
  constructor
  · -- reverse flow: an accepting simulator path induces an accepting `N`-run
    rintro ⟨choices, -, hout⟩
    set ch : ℕ → Bool := fun j =>
      if h : j < singleTapeSimTime k T x.length then choices ⟨j, h⟩ else false with hch
    have hhaltN : (N.trace (T x.length)
        (fun i => SingleTape.inducedChoices k ch i.val) (N.initCfg x)).state = N.qhalt :=
      hN x _
    obtain ⟨m, hm, hhalted, hbit⟩ :=
      SingleTape.halted_singleTapeSim_of_trace_qhalt N hk ch x (T x.length) hhaltN
    have hle : m ≤ singleTapeSimTime k T x.length :=
      le_trans hm (SingleTape.mul_macroBound_succ_le k (T x.length) x.length)
    have hagree : ∀ i : Fin m, choices ⟨i.val, lt_of_lt_of_le i.isLt hle⟩ = ch i.val := by
      intro i
      simp only [hch]
      rw [dite_eq_left (lt_of_lt_of_le i.isLt hle)]
    rw [(singleTapeSim N).trace_mono hle hagree hhalted] at hout
    exact ⟨fun i => SingleTape.inducedChoices k ch i.val, hhaltN, hbit.mp hout⟩
  · -- forward flow: simulate the accepting `N`-run, then pad the time bound
    intro h
    exact NTM.AcceptsInTime.mono
      (SingleTape.mul_macroBound_succ_le k (T x.length) x.length)
      (SingleTape.acceptsInTime_singleTapeSim_of_acceptsInTime N hk x (T x.length) h)

/-- The single-tape simulator decides the same language within the overhead time
    bound. -/
theorem singleTapeSim_decidesInTime {k : ℕ} {L : Language} (N : NTM k) (hk : 1 ≤ k) {T : ℕ → ℕ}
    (hdec : N.DecidesInTime L T) :
    (singleTapeSim N).DecidesInTime L (singleTapeSimTime k T) :=
  ⟨singleTapeSim_allPathsHaltIn N hk hdec.1,
    fun x => (hdec.2 x).trans (singleTapeSim_acceptsInTime_iff N hk T hdec.1 x).symm⟩

/-- **Single-tape reduction.** If `N` (with `k` work tapes) decides `L` within a
    polynomial time bound, then some single-work-tape machine `N'` decides the
    same `L` within a polynomial time bound. For `k = 0` the machine is padded
    with a dummy work tape (`pad0`); for `k ≥ 1` it is simulated
    (`singleTapeSim`). -/
theorem exists_singleTape_decidesInTime {k : ℕ} {L : Language} (N : NTM k)
    {T : ℕ → ℕ} {c : ℕ} (hdec : N.DecidesInTime L T) (hTO : T =O (· ^ c)) :
    ∃ (N' : NTM 1) (T' : ℕ → ℕ) (c' : ℕ), N'.DecidesInTime L T' ∧ T' =O (· ^ c') := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨pad0 N, T, c, pad0_decidesInTime hdec, hTO⟩
  · exact ⟨singleTapeSim N, singleTapeSimTime k T, 2 * c + 2,
      singleTapeSim_decidesInTime N hk hdec, singleTapeSimTime_bigO hTO⟩

end NTM

end Complexity
