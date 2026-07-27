/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.SpaceTime.Defs
public import Complexitylib.Models.TuringMachine.SpaceTime.Internal.RunBound

/-!
# Time bounds from deterministic transducer space bounds

A one-way-output deterministic transducer has only finitely many execution-
relevant configurations once its input length and auxiliary-space budget are
fixed. A halting run cannot repeat one of these reduced snapshots, yielding an
explicit time bound.

## Main results

- `TM.IsTransducer.reachesIn_succ_le_transducerConfigBound` — exact halted-run bound
- `TM.IsTransducer.reachesIn_le_transducerConfigBound` — convenient weak bound
- `TM.ComputesInSpace.computesInTime_configBound` — space computation gives time
- `TM.DecidesInSpace.decidesInTime_configBound` — decision-space bound gives time
-/

@[expose] public section

namespace Complexity

namespace TM

variable {k : ℕ} {tm : TM k}

/-- A halting transducer run staying within auxiliary space `space` has one
more time index than steps, and all those indices inject into the explicit
type of reduced transducer snapshots. -/
theorem IsTransducer.reachesIn_succ_le_transducerConfigBound
    (htrans : tm.IsTransducer) {x : List Bool} {space t : ℕ}
    {c : Cfg k tm.Q}
    (hreach : tm.reachesIn t (tm.initCfg x) c)
    (hhalt : tm.halted c)
    (hspace : ∀ d, tm.reaches (tm.initCfg x) d →
      d.WithinAuxSpace x.length space) :
    t + 1 ≤ tm.transducerConfigBound x.length space :=
  htrans.reachesIn_succ_le_transducerConfigBound_internal
    hreach hhalt hspace

/-- A halting transducer run staying within auxiliary space `space` takes no
more steps than the explicit number of reduced transducer snapshots. -/
theorem IsTransducer.reachesIn_le_transducerConfigBound
    (htrans : tm.IsTransducer) {x : List Bool} {space t : ℕ}
    {c : Cfg k tm.Q}
    (hreach : tm.reachesIn t (tm.initCfg x) c)
    (hhalt : tm.halted c)
    (hspace : ∀ d, tm.reaches (tm.initCfg x) d →
      d.WithinAuxSpace x.length space) :
    t ≤ tm.transducerConfigBound x.length space := by
  have := htrans.reachesIn_succ_le_transducerConfigBound
    hreach hhalt hspace
  omega

/-- A total deterministic function transducer using space `S` computes within
the corresponding finite reduced-configuration bound. -/
theorem ComputesInSpace.computesInTime_configBound
    {f : List Bool → List Bool} {S : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f S) :
    tm.ComputesInTime f
      (fun n => tm.transducerConfigBound n (S n)) :=
  hcomp.computesInTime_configBound_internal

/-- A deterministic language decider with one-way output and auxiliary-space
bound `S` decides within the corresponding finite reduced-configuration bound. -/
theorem DecidesInSpace.decidesInTime_configBound
    {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (htrans : tm.IsTransducer) :
    tm.DecidesInTime L
      (fun n => tm.transducerConfigBound n (S n)) :=
  hdec.decidesInTime_configBound_internal htrans

end TM

end Complexity
