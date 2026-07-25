/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexitylib.Models.RoseTreeMachine.Compile.Defs
import Complexitylib.Models.RoseTreeMachine.Compile.Internal

/-!
# Compiling in-place rose tree machine programs to Turing machines

This is the **surface** of the RTM → TM compiler: it states the single public
theorem `inPlace_compilesToTM`. The human-auditable contract it establishes
(`SubroutineLayout` / `Prog.RunsAsSubroutine`) lives in
`Complexitylib.Models.RoseTreeMachine.Compile.Defs`, and all proof machinery
lives in `Complexitylib.Models.RoseTreeMachine.Compile.Internal`.

## Main result

- `RoseTreeMachine.inPlace_compilesToTM` — **the full public compiler theorem**:
  every `InPlace` program of arity `m` compiles to a reusable tape-indexed
  subroutine (`Prog.RunsAsSubroutine m`). The caller runs it at tape indices of
  their choosing (a `SubroutineLayout`); inputs live on the chosen argument work
  tapes (not the dedicated input tape) as their `Data.toBits` serialization; the
  machine halts with `HasOutput result.toBits` on the result tape, leaves every
  other tape exactly as it started, and matches the RTM time/space bounds up to
  a constant. Because the encoding is `Data.toBits`, `Data.toBits_length` makes
  the space charge coincide exactly with the RTM `Data.size` measure.

## Scope

This is the first verified slice of the `InPlace`-RTM → TM compiler. The
compiler recursion `Compile.Internal.compilesUnder_of_inPlace` is fully
decomposed into per-constructor parts and `inPlace_compilesToTM` is wired to it;
of those parts, `compiled_empty` is proven and each remaining part is stated but
still `sorry` (it needs concrete `Data`-manipulation subroutines over the tape
serialization, tracked in `ROADMAP.md`, track N0). The final theorem below
therefore transitively depends on `sorry`, so `lake build --wfail` and the axiom
guard will report it until the parts are proved.
-/

namespace Complexity

namespace RoseTreeMachine

/-- **The full in-place RTM → Turing-machine compiler theorem.** Every
first-order (`InPlace`) rose tree machine program compiles, at any argument
arity `m`, to a reusable tape-indexed Turing-machine subroutine
(`Prog.RunsAsSubroutine`): the caller runs it at tape indices of their choosing,
inputs are serialized via `Data.toBits`, and time/space match the RTM `ProgSem`
bounds up to a constant. See `Prog.RunsAsSubroutine` for the precise contract.

The base case `empty` is discharged by `Compile.Internal.compiled_empty`; the
remaining constructors are tracked in `ROADMAP.md`, track N0. The statement is
provided now so the subroutine interface is fixed; the proof is deferred. -/
theorem inPlace_compilesToTM {m : ℕ} (p : Prog) (hp : InPlace p) :
    p.RunsAsSubroutine m :=
  compilesUnder_of_inPlace p hp

end RoseTreeMachine

end Complexity
