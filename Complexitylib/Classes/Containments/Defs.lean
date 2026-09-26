/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.ChoiceTape
public import Mathlib.Data.Nat.Log

/-!
# The configuration graph and its bounded reachability rounds

The space-bounded containments — `NL ⊆ P`, `NL ⊆ coNL`, Savitch's theorem — all read a
computation as a walk in the *configuration graph*: the nondeterministic step relation on
configurations. This file holds the three definitions those arguments share, so that theorem
statements about them can be read without opening any proof internals.

## Main definitions

- `NTM.Succ` — one nondeterministic step, as a relation on configurations
- `NTM.ReachesCfg` — its reflexive-transitive closure
- `NTM.reachSet` — the configurations reached within a fixed number of rounds of
  successor-closure, i.e. the state of a breadth-first search after that many rounds
- `NTM.ReachesCfgIn`, `NTM.ReachesCfgLe` — reachability in exactly, and in at most, a given
  number of steps; the step count is what Savitch's recursion halves
- `logWindow` — a concrete `O(log n)` search window
- `TM.spaceTimeBound` — the configuration count of a space-bounded deterministic machine, which
  bounds its running time (`PSPACE ⊆ EXP`)
-/

@[expose] public section

namespace Complexity

/-- The search window of a log-space machine. A machine's own space function is an arbitrary
`O(log n)` function, which a program cannot evaluate; this concrete bound can be computed from
the input length alone, and enlarging the window is harmless. -/
def logWindow (C D n : ℕ) : ℕ := C * Nat.log 2 n + D

namespace NTM

variable {k : ℕ}

/-- One step of the configuration graph: a non-halted configuration has the two successors its
transition functions produce. -/
def Succ (tm : NTM k) (c c' : Cfg k tm.Q) : Prop :=
  c.state ≠ tm.qhalt ∧ ∃ b, c' = tm.stepCfg b c

/-- Reachability in the configuration graph. -/
def ReachesCfg (tm : NTM k) : Cfg k tm.Q → Cfg k tm.Q → Prop :=
  Relation.ReflTransGen tm.Succ

/-- Reachability in exactly `t` steps of the configuration graph. -/
inductive ReachesCfgIn (tm : NTM k) : ℕ → Cfg k tm.Q → Cfg k tm.Q → Prop
  /-- No steps: a configuration reaches itself. -/
  | refl (c : Cfg k tm.Q) : ReachesCfgIn tm 0 c c
  /-- One step followed by a shorter walk. -/
  | head {c c' c'' : Cfg k tm.Q} {t : ℕ} (hstep : tm.Succ c c')
      (hrest : ReachesCfgIn tm t c' c'') : ReachesCfgIn tm (t + 1) c c''

/-- Reachability in at most `t` steps. Halted configurations have no successors, so a walk
cannot be padded and the bounded notion is genuinely weaker than the exact one. -/
def ReachesCfgLe (tm : NTM k) (t : ℕ) (c c' : Cfg k tm.Q) : Prop :=
  ∃ s ≤ t, tm.ReachesCfgIn s c c'

/-- The configurations reachable from `c₀` within `t` rounds of successor-closure. -/
def reachSet (tm : NTM k) (c₀ : Cfg k tm.Q) : ℕ → Set (Cfg k tm.Q)
  | 0 => {c₀}
  | t + 1 => reachSet tm c₀ t ∪ {c' | ∃ c ∈ reachSet tm c₀ t, tm.Succ c c'}

end NTM

namespace TM

variable {k : ℕ}

/-- The exponential configuration bound of a space-`f` machine: the number of states, times the
`n + f n + 2` input-head positions, times, for each of the `k` work tapes and the output tape, a
head position within the window and window contents over the four-letter alphabet. A decider
that stays within space `f` halts within this many steps
(`TM.decidesInTime_of_decidesInSpace`). -/
def spaceTimeBound (tm : TM k) (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Fintype.card tm.Q *
    ((n + f n + 2) * (((f n + 1) * 4 ^ (f n + 1)) ^ k * ((f n + 2) * 4 ^ (f n + 2))))

end TM

end Complexity
