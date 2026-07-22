/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexitylib.Models.RoseTreeMachine.Compile.Defs
import Complexitylib.Models.RoseTreeMachine.Compile.Internal.EmptyTM

/-!
# Compiling in-place rose tree machine programs to Turing machines — internals

This module holds the **proof machinery** for the RTM → TM compiler: the
per-constructor compiler parts and the structural recursion
`compilesUnder_of_inPlace` that assembles them into the public subroutine
contract `Prog.RunsAsSubroutine`. Correctness is established by the type checker;
the human-auditable contract it discharges lives in
`Complexitylib.Models.RoseTreeMachine.Compile.Defs`, and the final theorem
`inPlace_compilesToTM` in `Complexitylib.Models.RoseTreeMachine.Compile`.

## Contents

- `RoseTreeMachine.Compiled` — a thin alias for `Prog.RunsAsSubroutine`, the
  shared codomain of the compiler recursion and the per-constructor parts.
- `RoseTreeMachine.compiled_var`, `compiled_empty`, `compiled_cons`,
  `compiled_elim`, `compiled_ifEq`, `compiled_while`, `compiled_app` — the
  **individual compiler parts**, one per `InPlace` constructor. `compiled_empty`
  is proven (it reuses `TM.emptyTM`, the parked-tape layout subroutine that
  materializes the empty node's serialization `[false, true]`); each remaining
  part is stated but still `sorry`: it needs concrete `Data`-manipulation
  subroutines over the tape serialization, tracked as future work in
  `ROADMAP.md` (track N0).
- `RoseTreeMachine.compilesUnder_of_inPlace` — **the internal recursion**: every
  `InPlace` program compiles, for any argument arity, to a subroutine satisfying
  `Prog.RunsAsSubroutine`. The assembly is complete (no `sorry`); it dispatches
  each program constructor to its individual part.

> Note: the `compiled_*` parts other than `compiled_empty` use `sorry` (and
> `compilesUnder_of_inPlace` depends on them), so `lake build --wfail` and the
> axiom guard will report them until the parts are proved.
-/

namespace Complexity

namespace RoseTreeMachine

open Complexity.TM

/-- `Compiled m p`: the first-order program `p` compiles, for argument arity
`m`, to a reusable tape-indexed Turing-machine subroutine. This is a thin alias
for the public contract `Prog.RunsAsSubroutine`; it names the shared codomain of
the compiler recursion `compilesUnder_of_inPlace` and the per-constructor
building blocks below. -/
def Compiled (m : ℕ) (p : Prog) : Prop := p.RunsAsSubroutine m

/-- **Compiler part — `empty`.** The empty constructor compiles to `TM.emptyTM`,
the parked-tape layout subroutine that clears the result tape and writes the
empty node's serialization `[false, true] = (Data.l []).toBits` onto it, leaving
every other tape literally unchanged. `ProgSem.empty` fixes the RTM cost at
`t = s = 2`, so the machine's constant time and additive space fit the
`a·t + a` / `b·s + b` budget with `a = clearWorkTimeBound 0 + 3` and `b = a + 1`. -/
theorem compiled_empty (m : ℕ) : Compiled m Prog.empty := by
  refine ⟨0, clearWorkTimeBound 0 + 1 + 2, 1 + (clearWorkTimeBound 0 + 1 + 2), ?_⟩
  intro k L
  refine ⟨emptyTM L.resIdx, ?_⟩
  intro env result t s work₀ inp₀ out₀ hsem hloaded hinpP hinpHead houtP
  obtain ⟨_, hres, _, hpark⟩ := hloaded
  cases hsem
  have htarget :
      work₀ L.resIdx = (Tape.init (([] : List Bool).map Γ.ofBool)).move Dir3.right := by
    simpa using hres
  have hinitial :
      ({ state := (emptyTM L.resIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg k (emptyTM L.resIdx).Q).WithinAuxSpace 0 1 :=
    ⟨fun i => (hpark i).2, by show inp₀.head ≤ 0 + 1 + 1; omega⟩
  have key := emptyTM_hoareTimeSpace L.resIdx [] 0 1 inp₀ work₀ out₀ htarget
    hinpP (fun i _ => (hpark i).1) houtP hinitial
  simp only [List.length_nil] at key
  refine key.consequence (fun _ _ _ h => h) ?_ (by omega) (le_refl _) (by omega)
  rintro inp work out ⟨hi, hframe, hacc, ho⟩
  exact ⟨hi, ho, by simpa using hacc, hframe⟩

/-- **Compiler part — `var i`** (statement only). Reading environment variable
`i` copies the value on argument tape `i` (for `i < m`) to the result tape, or
materializes the empty node (for `i ≥ m`, where the read falls off the
environment). Matches `ProgSem.var`. -/
theorem compiled_var (m i : ℕ) : Compiled m (Prog.var i) := by
  sorry

/-- **Compiler part — `cons h t`** (statement only). Given compiled sub-machines
for `h` and `t`, `cons` runs them on a shared tape bank and prepends the head
value to the tail list on the result tape. Matches `ProgSem.cons`
(time/space add). -/
theorem compiled_cons {m : ℕ} {h t : Prog}
    (ih_h : Compiled m h) (ih_t : Compiled m t) : Compiled m (Prog.cons h t) := by
  sorry

/-- **Compiler part — `elim v emp (fn (fn body))`** (statement only). Given
compiled sub-machines for the scrutinee `v` and the empty branch `emp` at arity
`m`, and for the cons branch `body` at arity `m + 2` (the two fresh tapes hold
the destructured head and tail), `elim` branches on whether `v` is the empty
node. Matches `ProgSem.elim_nil` / `ProgSem.elim_cons`. -/
theorem compiled_elim {m : ℕ} {v emp body : Prog}
    (ih_v : Compiled m v) (ih_emp : Compiled m emp) (ih_body : Compiled (m + 2) body) :
    Compiled m (Prog.elim v emp (.fn (.fn body))) := by
  sorry

/-- **Compiler part — `ifEq x y then_ else_`** (statement only). Given compiled
sub-machines for all four arguments at arity `m`, `ifEq` compares the values of
`x` and `y` and runs the matching branch. Matches `ProgSem.ifEq_then` /
`ProgSem.ifEq_else`. -/
theorem compiled_ifEq {m : ℕ} {x y then_ else_ : Prog}
    (ih_x : Compiled m x) (ih_y : Compiled m y)
    (ih_then : Compiled m then_) (ih_else : Compiled m else_) :
    Compiled m (Prog.ifEq x y then_ else_) := by
  sorry

/-- **Compiler part — `while_ init (fn body)`** (statement only). Given a
compiled sub-machine for `init` at arity `m` and for the loop `body` at arity
`m + 1` (the fresh tape holds the accumulator), `while_` iterates the body on the
accumulator tape until its head is empty. Matches `ProgSem.while_` /
`WhileSem` (which already uses `max` for space, exactly the loop's reuse). -/
theorem compiled_while {m : ℕ} {init body : Prog}
    (ih_init : Compiled m init) (ih_body : Compiled (m + 1) body) :
    Compiled m (Prog.while_ init (.fn body)) := by
  sorry

/-- **Compiler part — `app (fn body) arg`** (the in-place `let`; statement only).
Given a compiled sub-machine for `arg` at arity `m` and for `body` at arity
`m + 1`, `app` evaluates `arg` onto a fresh environment tape and then runs
`body`. Matches `ProgSem.app` composed with `AppSem.mk` (running `body` in
`σ ++ [v]`). Nested uses give multi-argument `let`-chains, hence arbitrary
arities. -/
theorem compiled_app {m : ℕ} {body arg : Prog}
    (ih_body : Compiled (m + 1) body) (ih_arg : Compiled m arg) :
    Compiled m (Prog.app (.fn body) arg) := by
  sorry

/-- **The internal compiler recursion.** For every argument arity `m`, every
first-order (`InPlace`) program compiles to a reusable tape-indexed Turing
machine subroutine satisfying `Prog.RunsAsSubroutine`.

The recursion structure is fully assembled here: induction on the `InPlace`
derivation dispatches each program constructor to its compiler part
(`compiled_var`, `compiled_empty`, `compiled_cons`, `compiled_elim`,
`compiled_ifEq`, `compiled_while`, `compiled_app`), threading the argument arity
so that `elim`/`while_`/`app` compile their body at the extended arity (`m + 2`,
`m + 1`, `m + 1`) that the `σ`-extension of the operational semantics uses. Only
the individual parts carry `sorry`; the assembly below is complete. -/
theorem compilesUnder_of_inPlace {m : ℕ} (p : Prog) (hp : InPlace p) :
    Compiled m p := by
  induction hp generalizing m with
  | var => exact compiled_var m _
  | empty => exact compiled_empty m
  | cons _ _ ih_h ih_t => exact compiled_cons ih_h ih_t
  | elim _ _ _ ih_v ih_emp ih_body => exact compiled_elim ih_v ih_emp ih_body
  | ifEq _ _ _ _ ih_x ih_y ih_then ih_else =>
      exact compiled_ifEq ih_x ih_y ih_then ih_else
  | while_ _ _ ih_init ih_body => exact compiled_while ih_init ih_body
  | app _ _ ih_body ih_arg => exact compiled_app ih_body ih_arg

end RoseTreeMachine

end Complexity
