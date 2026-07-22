/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexitylib.Models.RoseTreeMachine.Prog
import Complexitylib.Models.TuringMachine.Hoare.Space.Defs
import Complexitylib.Models.TuringMachine.Registers

/-!
# Compiling in-place rose tree machine programs to Turing machines — contract

This module holds the **human-auditable contract** the RTM → TM compiler
establishes: the caller-chosen tape layout and the public subroutine
specification. The proof machinery that discharges the contract lives in
`Complexitylib.Models.RoseTreeMachine.Compile.Internal`, and the final theorem
`inPlace_compilesToTM` lives in `Complexitylib.Models.RoseTreeMachine.Compile`.

## What "match" means here

The RTM cost model is faithful to Turing machines only *up to a constant
factor* — the standard notion for cross-model simulation. A compiled machine
computes the *same* binary function as the source program and its time (resp.
space) bound is *dominated by* the program's RTM time (resp. space) bound.

Two structural facts make this achievable for the `InPlace` fragment:

- **Result materialization is already paid for.** `ProgSem.size_le` shows every
  derivation charges at least the size of the value it produces, in both time
  and space, so the O(size) traversal/assembly/copy work a Turing machine must
  perform to build a `Data` result is always absorbed (up to a constant).
- **Space is charged generously.** Most `ProgSem` rules *add* the space of
  sequential sub-computations (`s₁ + s₂ + …`) where a Turing machine reuses
  space and pays only their `max`, so the RTM figure is a valid upper bound.

## Main definitions

- `RoseTreeMachine.SubroutineLayout` — a caller-chosen tape layout: a single
  injective `place` map assigning each slot (an argument, the result, or a
  scratch tape) a distinct physical tape in the caller's bank. Role accessors
  `argIdx`/`resIdx`/`scratchIdx` and their pairwise-distinctness follow from
  injectivity of `place`.
- `RoseTreeMachine.Prog.RunsAsSubroutine` — the **public subroutine contract**:
  the compiled machine, run from a `SubroutineLayout.Loaded` start, halts with
  the result on the result tape, frames every other tape (arguments preserved,
  scratch restored blank), and matches the RTM time/space bounds up to a
  constant. This is what `inPlace_compilesToTM` establishes.
-/

namespace Complexity

namespace RoseTreeMachine

open Complexity.TM

/-- The tapes a subroutine occupies, indexed uniformly by role: `m` argument
slots, one result slot, and `sc` scratch slots. A `SubroutineLayout` maps this
slot space injectively into the caller's tape bank. -/
abbrev SubroutineSlot (m sc : ℕ) := Fin m ⊕ Unit ⊕ Fin sc

/-- **A caller-chosen tape layout** for running an `m`-argument in-place RTM
program as a subroutine on a `Fin k` tape bank using `sc` scratch tapes. As with
the binary-arithmetic subroutines, the caller picks the tapes; a single
injective `place` assigns each slot (argument, result, or scratch) a distinct
physical tape, so the machine can treat them as independent registers. -/
structure SubroutineLayout (m sc k : ℕ) where
  /-- The physical tape each slot occupies. -/
  place : SubroutineSlot m sc → Fin k
  /-- Distinct slots occupy distinct tapes. -/
  place_inj : Function.Injective place

namespace SubroutineLayout

variable {m sc k : ℕ} (L : SubroutineLayout m sc k)

/-- The tape variable `j` is read from. -/
def argIdx (j : Fin m) : Fin k := L.place (.inl j)

/-- The tape the result is written to. -/
def resIdx : Fin k := L.place (.inr (.inl ()))

/-- The `l`-th auxiliary tape the machine may use. -/
def scratchIdx (l : Fin sc) : Fin k := L.place (.inr (.inr l))

/-- Distinct variables use distinct tapes. -/
theorem argIdx_inj : Function.Injective L.argIdx := fun _ _ h =>
  Sum.inl_injective (L.place_inj h)

/-- Distinct scratch slots use distinct tapes. -/
theorem scratchIdx_inj : Function.Injective L.scratchIdx := fun _ _ h =>
  Sum.inr_injective (Sum.inr_injective (L.place_inj h))

/-- No argument tape coincides with the result tape. -/
theorem arg_ne_res (j : Fin m) : L.argIdx j ≠ L.resIdx := fun h => by
  simpa using L.place_inj h

/-- No scratch tape coincides with the result tape. -/
theorem scratch_ne_res (l : Fin sc) : L.scratchIdx l ≠ L.resIdx := fun h => by
  simpa using L.place_inj h

/-- Argument tapes and scratch tapes are disjoint. -/
theorem arg_ne_scratch (j : Fin m) (l : Fin sc) : L.argIdx j ≠ L.scratchIdx l :=
  fun h => by simpa using L.place_inj h

/-- The starting tape assignment expected by a `SubroutineLayout`: environment
entry `j` sits on its argument tape as the balanced-parenthesis serialization
`Data.toBits`, and the result and scratch tapes start blank. Every layout tape
is **parked** (head at cell 1, just past the `▷` marker): a parked head is
fixed by `idleDir`, so tapes the machine does not touch stay literally
unchanged, and the convention matches the binary-arithmetic subroutines
(e.g. `clearWorkTM`). Tapes outside the layout carry no prescribed contents, but
they too must be **parked at head 1** (`Parked ∧ head ≤ 1`): parkedness makes the
machine leave them literally unchanged (a head resting past a stray `▷` could be
mutated across an idle step), and the head-1 bound keeps them inside the `b·s+b`
auxiliary-space budget from the very first configuration. Every layout tape
already sits at head 1, so this constrains only the caller's spare tapes. This
makes the "every non-result tape is preserved" frame in `RunsAsSubroutine` hold
for the whole bank, not just the layout tapes. -/
def Loaded (env : Fin m → Data) (work : Fin k → Tape) : Prop :=
  (∀ j, work (L.argIdx j) =
      (Tape.init ((env j).toBits.map Γ.ofBool)).move Dir3.right) ∧
  work L.resIdx = (Tape.init []).move Dir3.right ∧
  (∀ l, work (L.scratchIdx l) = (Tape.init []).move Dir3.right) ∧
  (∀ i, Parked (work i) ∧ (work i).head ≤ 1)

end SubroutineLayout

/-- **The public subroutine contract.** `p.RunsAsSubroutine m` says the
`m`-argument in-place program `p` compiles to a reusable Turing-machine
subroutine: there is a scratch-tape count `sc` and constants `a`, `b`
(depending only on `p`), so that for *any* caller layout `L : SubroutineLayout
m sc k` there is a machine `M : TM k` that, whenever `p` maps `env` to `result`
in RTM time `t` and space `s`, run from a `Loaded` start

* halts within `a·t + a` steps with `result.toBits` on the result tape
  (`HasOutput`),
* leaves **every other tape exactly as it started** (`∀ i ≠ resIdx`): arguments
  preserved read-only, scratch restored blank, untouched tapes untouched, and
* keeps all work heads within `b·s + b` auxiliary space.

The dedicated input and output tapes are not used by the compiler: the caller
supplies them **parked** (`Parked inp₀`, `Parked out₀`) so the machine leaves
them literally unchanged (`inp = inp₀ ∧ out = out₀`), and the input head starts
at cell 1 (`inp₀.head ≤ 1`) so it fits the `0 + space + 1` input allowance.

Inputs live on the chosen argument work tapes, *not* the dedicated input tape,
so the space charge is over `Data.toBits`; by `Data.toBits_length` it matches
the RTM `Data.size` measure up to `b`. Exposing `sc` tells the caller how many
auxiliary tapes to reserve, and the "only the result tape changes" frame makes
`M` freely composable. -/
def Prog.RunsAsSubroutine (p : Prog) (m : ℕ) : Prop :=
  ∃ sc a b : ℕ, ∀ {k : ℕ} (L : SubroutineLayout m sc k),
    ∃ M : TM k, ∀ (env : Fin m → Data) (result : Data) (t s : ℕ)
      (work₀ : Fin k → Tape) (inp₀ out₀ : Tape),
      ProgSem (List.ofFn (fun j => Value.data (env j))) p (Value.data result) t s →
      L.Loaded env work₀ →
      Parked inp₀ → inp₀.head ≤ 1 → Parked out₀ →
      M.HoareTimeSpace
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
          (work L.resIdx).HasOutput result.toBits ∧
          (∀ i, i ≠ L.resIdx → work i = work₀ i))
        (a * t + a) 0 (b * s + b)

end RoseTreeMachine

end Complexity
