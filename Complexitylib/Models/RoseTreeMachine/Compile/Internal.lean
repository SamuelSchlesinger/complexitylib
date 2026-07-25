/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexitylib.Models.RoseTreeMachine.Compile.Defs
import Complexitylib.Models.RoseTreeMachine.Compile.Internal.EmptyTM
import Complexitylib.Models.TuringMachine.Subroutines.CopyWorkOutput

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
  and `compiled_var` are proven: `compiled_empty` reuses `TM.emptyTM` (the
  parked-tape layout subroutine that materializes the empty node's serialization
  `[false, true]`), and `compiled_var` copies argument tape `i` to the result
  tape via `TM.copyWorkToWorkTM` then restores it with `TM.rewindWorkTM` (falling
  back to `TM.emptyTM` when `i ≥ m`). Each remaining part is stated but still
  `sorry`: it needs concrete `Data`-manipulation subroutines over the tape
  serialization, tracked as future work in `ROADMAP.md` (track N0).
- `RoseTreeMachine.compilesUnder_of_inPlace` — **the internal recursion**: every
  `InPlace` program compiles, for any argument arity, to a subroutine satisfying
  `Prog.RunsAsSubroutine`. The assembly is complete (no `sorry`); it dispatches
  each program constructor to its individual part.

> Note: the `compiled_*` parts other than `compiled_empty` and `compiled_var`
> use `sorry` (and `compilesUnder_of_inPlace` depends on them), so
> `lake build --wfail` and the axiom guard will report them until the parts are
> proved.
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

/-- **Compiler part — `var i`.** Reading environment variable `i` copies the
value on argument tape `i` (for `i < m`) to the result tape via
`TM.copyWorkToWorkTM`, then restores the argument tape with `TM.rewindWorkTM`;
for `i ≥ m` (where the read falls off the environment) it materializes the empty
node with `TM.emptyTM`. Matches `ProgSem.var`. The copy/rewind pair adds only
linear time and no extra space beyond the copied value, fitting the `a·t + a` /
`b·s + b` budget with `a = clearWorkTimeBound 0 + 5` and `b = a + 1`. -/
theorem compiled_var (m i : ℕ) : Compiled m (Prog.var i) := by
  refine ⟨0, clearWorkTimeBound 0 + 5, clearWorkTimeBound 0 + 6, ?_⟩
  intro k L
  by_cases hi : i < m
  · -- copy argument tape i to the result tape, then rewind the argument tape
    set src := L.argIdx ⟨i, hi⟩ with hsrc
    set dst := L.resIdx with hdst
    have hne : src ≠ dst := L.arg_ne_res ⟨i, hi⟩
    refine ⟨seqTM (copyWorkToWorkTM src dst) (rewindWorkTM src), ?_⟩
    intro env result t s work₀ inp₀ out₀ hsem hloaded hinpP hinpHead houtP
    obtain ⟨hargs, hres, hscratch, hpark⟩ := hloaded
    -- identify the result value with argument `i`
    have hval : Value.data result
        = (List.ofFn (fun j => Value.data (env j)))[i]?.getD Value.empty :=
      hsem.value_det _ _ _ ProgSem.var
    simp only [List.getElem?_ofFn, hi, dif_pos, Option.getD_some] at hval
    have hresult : result = env ⟨i, hi⟩ := by
      simpa using hval
    subst hresult
    set x := (env ⟨i, hi⟩).toBits with hx
    set source := (Tape.init (x.map Γ.ofBool)).move Dir3.right with hsource
    have hsrc_source : work₀ src = source := by rw [hsrc, hargs, hsource, hx]
    have hsource_head : source.head = 1 := by rw [hsource]; simp [Tape.move]
    have hsource_out : source.HasOutput x := by
      have := Tape.init_move_right_hasBinaryString x
      exact ⟨this.2.1, this.2.2 x.length le_rfl⟩
    have hsource_cells0 : source.cells 0 = Γ.start := by
      rw [hsource]; simp [Tape.move, Tape.init]
    have hsource_nostart : ∀ j, j ≥ 1 → source.cells j ≠ Γ.start := by
      intro j hj
      obtain ⟨p, rfl⟩ : ∃ p, j = p + 1 := ⟨j - 1, by omega⟩
      have hbs := Tape.init_move_right_hasBinaryString x
      rw [hsource]
      by_cases hp : p < x.length
      · rw [hbs.2.1 p hp]; cases (x[p]'hp) <;> simp [Γ.ofBool]
      · rw [hbs.2.2 p (by omega)]; simp
    -- copy-phase frame predicate
    set Pc : Tape → (Fin k → Tape) → Tape → Prop :=
      fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ≠ src → j ≠ dst → work j = work₀ j) with hPc
    have hcopy := copyWorkToWorkTM_hoareTime_frame_of_hasOutput src dst hne x source
      (P := Pc)
      (by
        rintro inp work out inp' work' out' ⟨hi1, hi2, hi3⟩ _ _ _ _ _ hii hoo hframe
        exact ⟨by rw [hii, hi1], by rw [hoo, hi2],
          fun j hj1 hj2 => by rw [hframe j hj1 hj2]; exact hi3 j hj1 hj2⟩)
    -- rewind-phase frame predicate
    set Pr : Tape → (Fin k → Tape) → Tape → Prop :=
      fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (work dst).HasOutput x ∧ (work src).cells = source.cells ∧
        (∀ j, j ≠ src → j ≠ dst → work j = work₀ j) with hPr
    have hrewind := rewindWorkTM_hoareTime_frame src (x.length + 1)
      (P := Pr)
      (by
        rintro inp work out inp' work' out' ⟨hi1, hi2, hi3, hi4, hi5⟩
          hcells hhead hframe hii houtc houth
        refine ⟨by rw [hii, hi1], ?_, ?_, ?_, ?_⟩
        · rw [hi2] at houtc houth; exact Tape.ext houth houtc
        · rw [hframe dst hne.symm]; exact hi3
        · rw [hcells]; exact hi4
        · intro j hj1 hj2; rw [hframe j hj1]; exact hi5 j hj1 hj2)
    -- compose
    have hcomp := seqTM_hoareTime (copyWorkToWorkTM src dst) (rewindWorkTM src)
      hcopy ?_ hrewind
    · -- convert to time-space and fit the budget
      have hsize := hsem.size_le
      rw [Value.size_data] at hsize
      obtain ⟨hst, hss⟩ := hsize
      have hxlen : x.length = (env ⟨i, hi⟩).size := by rw [hx]; exact (env ⟨i, hi⟩).toBits_length
      have hHT : (seqTM (copyWorkToWorkTM src dst) (rewindWorkTM src)).HoareTime
          (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
          (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
            (work L.resIdx).HasOutput (env ⟨i, hi⟩).toBits ∧
            (∀ j, j ≠ L.resIdx → work j = work₀ j))
          (x.length + 1 + 1 + (x.length + 1 + 2)) := by
        refine hcomp.consequence ?_ ?_ le_rfl
        · rintro inp work out ⟨rfl, rfl, rfl⟩
          exact ⟨hsrc_source, hsource_head, hsource_out,
            by rw [hdst]; exact hres, hinpP.read_ne_start, houtP.read_ne_start,
            houtP.1, fun j _ _ => ⟨(hpark j).1.read_ne_start, (hpark j).1.1⟩,
            rfl, rfl, fun _ _ _ => rfl⟩
        · rintro inp work out ⟨hhead1, hpr1, hpr2, hpr3, hpr4, hpr5⟩
          refine ⟨hpr1, hpr2, by rw [← hdst]; exact hpr3, ?_⟩
          intro j hj
          by_cases hjs : j = src
          · subst hjs
            rw [hsrc_source]
            exact Tape.ext (hhead1.trans hsource_head.symm) hpr4
          · exact hpr5 j hjs (by rw [hdst]; exact hj)
      have hHTS := hHT.toHoareTimeSpace (inputLength := 0) (initialSpace := 1)
        (by rintro inp work out ⟨rfl, rfl, rfl⟩
            exact ⟨fun j => (hpark j).2, by show inp.head ≤ 0 + 1 + 1; omega⟩)
      refine hHTS.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) ?_ (le_refl _) ?_
      · have hPt : 2 * t ≤ (clearWorkTimeBound 0 + 5) * t := by gcongr; omega
        omega
      · have hPs : 2 * s ≤ (clearWorkTimeBound 0 + 6) * s := by gcongr; omega
        omega
    · -- boundary transition: all reads ≠ start, so the transition is the identity
      rintro inp work out ⟨hc1, hc2, hc3, hc4, hc5, hpc1, hpc2, hpc3⟩
      have hwork_ns : ∀ j, (work j).read ≠ Γ.start := by
        intro j
        by_cases hjs : j = src
        · subst hjs; rw [Tape.read, hc2, hc3.2]; decide
        · by_cases hjd : j = dst
          · subst hjd; rw [hc4.read_blank]; decide
          · rw [hpc3 j hjs hjd]; exact (hpark j).1.read_ne_start
      have hinp_ns : inp.read ≠ Γ.start := by rw [hpc1]; exact hinpP.read_ne_start
      have hout_ns : out.read ≠ Γ.start := by rw [hpc2]; exact houtP.read_ne_start
      obtain ⟨hti, htw, hto⟩ :=
        phaseTransition_eq_self_of_reads_ne_start hinp_ns hwork_ns hout_ns
      rw [hti, htw, hto]
      refine ⟨by rw [hc1]; exact hsource_cells0,
        fun j hj => by rw [hc1]; exact hsource_nostart j hj, hc2.le, hinp_ns, hout_ns,
        by rw [hpc2]; exact houtP.1, ?_, hpc1, hpc2, hc4.hasOutput, hc1, hpc3⟩
      intro j hjs
      by_cases hjd : j = dst
      · subst hjd; exact ⟨by rw [hc4.read_blank]; decide, by rw [hc4.1]; omega⟩
      · rw [hpc3 j hjs hjd]; exact ⟨(hpark j).1.read_ne_start, (hpark j).1.1⟩
  · -- i ≥ m : the read falls off the environment; materialize the empty node
    refine ⟨emptyTM L.resIdx, ?_⟩
    intro env result t s work₀ inp₀ out₀ hsem hloaded hinpP hinpHead houtP
    obtain ⟨_, hres, _, hpark⟩ := hloaded
    have hval : Value.data result
        = (List.ofFn (fun j => Value.data (env j)))[i]?.getD Value.empty :=
      hsem.value_det _ _ _ ProgSem.var
    rw [List.getElem?_ofFn, dif_neg hi, Option.getD_none] at hval
    injection hval with hresult
    subst hresult
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
    rintro inp work out ⟨hi', hframe, hacc, ho⟩
    exact ⟨hi', ho, by simpa using hacc, hframe⟩

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
