/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.Containments.Defs
public import Complexitylib.Classes.Containments.Internal.SavitchBound
public import Complexitylib.Classes.Containments.Internal.SavitchAssemble
public import Complexitylib.Classes.Containments.PSPACESubsetNPSPACE
public import Complexitylib.Classes.NP

/-!
# `NPSPACE ⊆ PSPACE`

⚠️ Unreviewed by Bolton

Savitch's theorem, at the level of classes: `NPSPACE ⊆ PSPACE`.

The reachability predicate `Reach(u, v, 2^i)` — is `v` reachable from `u` in at most `2^i` steps —
satisfies `Reach(u, v, 2^i) ↔ ∃ m, Reach(u, m, 2^(i-1)) ∧ Reach(m, v, 2^(i-1))`. Recursing on `i`
and reusing the same space for the two subcalls costs `O(S)` bits per level and `O(S)` levels,
which in the textbook argument simulates a nondeterministic space-`S` machine deterministically in
space `O(S²)`.

This file proves only the class inclusion. The parametric bound `NSPACE(S) ⊆ DSPACE(S²)` is not
formalized: the deterministic machine below comes from iterating a polynomial-time step function
under a polynomial space window, and no `O(S²)` bound is stated or extracted from it.

## How the proof runs

Not as a machine, but as a *pure function iterated in place*, exactly as `NL ⊆ P` was done:

- `Complexity.savStep` (`Internal.SavitchStep`) is one step of Savitch's stack machine, written
  inside the polynomial-time algebra on a single bitstring — a done flag, an answer, the block
  ruler, a returning value, and a stack of frames, each frame carrying a level, two endpoints and
  the midpoint currently being tried.
- `Complexity.Sav.step` (`Internal.SavitchSem`) is the same recursion on an inductive state, where
  it can be reasoned about, and `Complexity.savStep_encSst` proves the square commutes.
  `Complexity.Sav.run_frame` is the heart: a pushed frame is popped again carrying its value
  within `Complexity.Sav.runBound` steps — by induction on the level, and inside a level by
  induction on the work the frame has left.
- `Complexity.accB_cfgCode` (`Internal.SavitchReach`) identifies the value the recursion returns
  with reachability in the configuration graph: the enumeration of midpoints is *every* string of
  the code width, and a code has exactly that width.
- `Complexity.SpaceIter.mem_PSPACE_of_iterate` supplies the machine: iterating a polynomial-time
  function on a polynomially bounded state is in `PSPACE`, however many iterations it takes. The
  iteration count is `2 ^ poly` — `Complexity.Sav.runBound_le` — which is exactly what a binary
  counter can drive.

## Main results

- `savitch_halving` — the midpoint recursion at a halved step bound
- `savitch_reaches_within_codes` — reachability is witnessed within the number of codes
- `NPSPACE_bounded_reachability` — membership is reachability within `2 ^ poly` steps
- `NPSPACE_subset_PSPACE` — **Savitch's theorem**
- `PSPACE_eq_NPSPACE` — hence the two classes coincide
-/

@[expose] public section

namespace Complexity

/-- **The recursion Savitch's machine runs.** A step bound of `2 ^ (i + 1)` is met exactly when
some midpoint configuration is reachable within `2 ^ i` steps and reaches the target within
`2 ^ i` steps. Recursing on `i` costs one stored midpoint per level and bottoms out at `i = 0`,
where the question is a single step of the configuration graph. -/
theorem savitch_halving {k : ℕ} (tm : NTM k) (i : ℕ) (c c' : Cfg k tm.Q) :
    tm.ReachesCfgLe (2 ^ (i + 1)) c c' ↔
      ∃ mid, tm.ReachesCfgLe (2 ^ i) c mid ∧ tm.ReachesCfgLe (2 ^ i) mid c' :=
  NTM.reachesCfgLe_two_pow_succ_iff tm i c c'

/-- **Reachability is witnessed within the number of configuration codes.** Any coding map that
separates the reachable configurations bounds the length of a walk that has to be searched: a
longer walk repeats a configuration and the repetition can be cut out. This is what makes the
recursion depth of `savitch_halving` finite. -/
theorem savitch_reaches_within_codes {k : ℕ} {α : Type} [Fintype α] (tm : NTM k)
    (c₀ : Cfg k tm.Q) (g : Cfg k tm.Q → α)
    (hinj : ∀ {c c' : Cfg k tm.Q}, tm.ReachesCfg c₀ c → tm.ReachesCfg c₀ c' → g c = g c' → c = c')
    {N : ℕ} (hN : Fintype.card α ≤ N) (c : Cfg k tm.Q) :
    tm.ReachesCfg c₀ c ↔ tm.ReachesCfgLe N c₀ c :=
  NTM.reachesCfg_iff_reachesCfgLe tm c₀ g hinj hN c

/-- **A language in `NPSPACE` is reachability within `2 ^ poly` steps.** This is what
`savitch_halving` is applied to: the step bound `2 ^ q(|x|)` halves `q(|x|)` times before
reaching a single step, so the recursion has polynomial depth, and each of its levels stores one
configuration of a polynomially space-bounded machine. -/
theorem NPSPACE_bounded_reachability {L : Language} (hL : L ∈ NPSPACE) :
    ∃ (k : ℕ) (tm : NTM k) (q : Polynomial ℕ),
      ∀ x : List Bool, x ∈ L ↔
        ∃ c, tm.ReachesCfgLe (2 ^ q.eval x.length) (tm.initCfg x) c ∧
          tm.halted c ∧ c.output.cells 1 = Γ.one :=
  NPSPACE_bounded_reachability_internal hL

/-- **`NPSPACE ⊆ PSPACE`** (Savitch): halving the path length recursively decides a polynomially
space-bounded nondeterministic machine deterministically in polynomial space. Only this class
inclusion is stated; the quantitative `O(S²)` space bound of Savitch's theorem is not. -/
theorem NPSPACE_subset_PSPACE : NPSPACE ⊆ PSPACE :=
  NPSPACE_subset_PSPACE_internal

/-- **`PSPACE = NPSPACE`.** Savitch's theorem settles the equality: the reverse inclusion is
immediate, since a deterministic machine is a nondeterministic one that ignores its choices. -/
theorem PSPACE_eq_NPSPACE : PSPACE = NPSPACE :=
  subset_antisymm PSPACE_subset_NPSPACE NPSPACE_subset_PSPACE

end Complexity
