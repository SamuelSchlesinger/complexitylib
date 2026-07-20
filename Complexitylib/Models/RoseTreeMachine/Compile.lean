/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexitylib.Models.RoseTreeMachine.Prog
import Complexitylib.Models.TuringMachine.Subroutines.CopyOutput
import Complexitylib.Models.TuringMachine.Hoare.Space.Defs

/-!
# Compiling in-place rose tree machine programs to Turing machines

This file constructs equivalent Turing machines for programs in the first-order
(`InPlace`) fragment of the rose tree machine (RTM) and relates their resource
consumption to the RTM `ProgSem` cost model.

## What "match" means here

The RTM cost model is faithful to Turing machines only *up to a constant
factor* — this is the same notion the RTM's own `ComputableInOTime` /
`ComputableInOSpace` already use, and it is the standard notion for
cross-model simulation. Concretely, a compiled machine computes the *same*
binary function as the source program and its time (resp. space) bound is
*dominated by* the program's RTM time (resp. space) bound.

Two structural facts make this achievable for the `InPlace` fragment:

- **Result materialization is already paid for.** `ProgSem.size_le` shows every
  derivation charges at least the size of the value it produces, in both time
  and space. So the O(size) traversal/assembly/copy work a Turing machine must
  perform to build a `Data` result is always absorbed (up to a constant) by the
  sub-costs the RTM already charges.
- **Space is charged generously.** Most `ProgSem` rules *add* the space of
  sequential sub-computations (`s₁ + s₂ + …`) where a Turing machine reuses
  space and pays only their `max`. The RTM figure is therefore a valid upper
  bound for the machine's actual space. (`WhileSem` already uses `max`, matching
  the loop's space reuse exactly.)

## Main definitions

- `RoseTreeMachine.SubroutineLayout` — a caller-chosen tape layout (argument
  tapes `argIdx`, result tape `resIdx`, `sc` scratch tapes `scratchIdx`, all
  pairwise distinct) for running an in-place program at tape indices of the
  caller's choosing, in the style of the binary-arithmetic subroutines.
- `RoseTreeMachine.Prog.RunsAsSubroutine` — the **public subroutine contract**:
  the compiled machine, run from a `SubroutineLayout.Loaded` start, halts with
  the result on the result tape, frames every other tape (arguments preserved,
  scratch restored blank), and matches the RTM time/space bounds up to a
  constant. This is what `inPlace_compilesToTM` establishes.
- `RoseTreeMachine.CompilesUnder` — the internal, **layout-relative** compiler
  contract: a machine implements a program for an environment layout that places
  one program argument per work tape (`slot : Fin m → Fin k`) and deposits the
  result on a chosen tape, with time/space matched to the RTM `ProgSem` bounds.
  This is where "multiple inputs map to tapes" lives.
- `RoseTreeMachine.LoadedStart` — the multi-tape analogue of `Cfg.init`: the
  starting configuration for `CompilesUnder`, with each argument serialized onto
  its designated tape via `Data.toBits`.
- `RoseTreeMachine.emptyOutputTM` — the one-state machine that halts immediately
  with empty output.

## Main results

- `RoseTreeMachine.inPlace_compilesToTM` — **the full public compiler theorem**
  (stated now; proof deferred, see *Scope*): every `InPlace` program of arity
  `m` compiles to a reusable tape-indexed subroutine
  (`Prog.RunsAsSubroutine m`). The caller runs it at tape indices of their
  choosing (a `SubroutineLayout`); inputs live on the chosen argument work tapes
  (not the dedicated input tape) as their `Data.toBits` serialization; the
  machine halts with `HasOutput result.toBits` on the result tape, leaves every
  other tape exactly as it started, and matches the RTM time/space bounds up to
  a constant. Because the encoding is `Data.toBits`,
  `Data.toBits_length` makes the space charge coincide exactly with the RTM
  `Data.size` measure.
- `RoseTreeMachine.compilesUnder_of_inPlace` — **the internal recursion**: every
  `InPlace` program compiles, for any argument arity, to a machine plus a tape
  layout satisfying `CompilesUnder`. The recursion *assembly* is complete (no
  `sorry`); it dispatches each program constructor to its individual part.
- `RoseTreeMachine.compiled_var`, `compiled_empty`, `compiled_cons`,
  `compiled_elim`, `compiled_ifEq`, `compiled_while`, `compiled_app` — the
  **individual compiler parts**, one per `InPlace` constructor, each turning
  compiled sub-programs into the compiled composite. `compiled_empty` is proven;
  the rest are stated only (the remaining `Data`-manipulation obligations).
- `RoseTreeMachine.emptyOutputTM_computesInTime` /
  `emptyOutputTM_computesInSpace` — the trivial machine computes `fun _ => []`
  in zero time and zero auxiliary space.

## Scope

This is the first verified slice of the `InPlace`-RTM → TM compiler. The
compiler recursion is now fully decomposed: `compilesUnder_of_inPlace` assembles
the per-constructor parts `compiled_var`, `compiled_empty`, `compiled_cons`,
`compiled_elim`, `compiled_ifEq`, `compiled_while`, and `compiled_app` by
induction on the `InPlace` derivation — this assembly is complete, with no
`sorry`. Of the individual parts, `compiled_empty` is proven; each remaining
part is stated but still `sorry`: it needs concrete `Data`-manipulation
subroutines over the tape serialization, tracked as future work in `ROADMAP.md`
(track N0). The framework here — the `CompilesUnder` / `LoadedStart`
layout-relative interface, the `Data.toBits` tape serialization, and the fixed
part/assembly/wrapper statements — pins down the interface those subroutines
will compose through.

> Note: the `compiled_*` parts and `inPlace_compilesToTM` use `sorry` (and
> `compilesUnder_of_inPlace` depends on the parts), so `lake build --wfail` and
> the axiom guard will report them until the parts are proved.
-/

namespace Complexity

/-- Map a read symbol to a writable symbol, sending the start marker `▷` to
blank. Used by the compiler's machines to write back a symbol they just read
without ever emitting `▷` (which is not a member of the write alphabet). -/
def Γ.toΓwId : Γ → Γw
  | .zero => .zero
  | .one => .one
  | .blank => .blank
  | .start => .blank

namespace RoseTreeMachine

open Complexity.TM

-- ════════════════════════════════════════════════════════════════════════
-- A halted configuration only reaches itself
-- ════════════════════════════════════════════════════════════════════════

/-- A configuration whose state is the halt state has no successors, so the only
configuration it reaches is itself. -/
private theorem reaches_eq_of_halted {n : ℕ} {tm : TM n} {c c' : Cfg n tm.Q}
    (hh : c.state = tm.qhalt) (h : tm.reaches c c') : c' = c := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨d, hstep, _⟩
  · exact heq.symm
  · exact absurd hstep (by
      have hnone : tm.step c = none := step_eq_none_iff_halted.mpr hh
      simp [TM.stepRel, hnone])

-- ════════════════════════════════════════════════════════════════════════
-- The trivial machine: halt immediately with empty output
-- ════════════════════════════════════════════════════════════════════════

/-- The one-state Turing machine that is halted from the start. Its output tape
is the initial (empty) tape, so it computes the constant empty-string function
in zero steps and zero auxiliary space. All transition directions are `right`,
satisfying `δ_right_of_start` and the transducer discipline vacuously (the
machine never steps). -/
def emptyOutputTM (n : ℕ) : TM n where
  Q := Unit
  qstart := ()
  qhalt := ()
  δ := fun _ _ _ _ => ((), fun _ => Γw.blank, Γw.blank, .right, fun _ => .right, .right)
  δ_right_of_start := by
    intro q iHead wHeads oHead
    exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- The initial (empty) output tape holds the empty output string. -/
private theorem hasOutput_init_nil : (Tape.init []).HasOutput ([] : List Bool) := by
  refine ⟨fun i h => absurd h (by simp), ?_⟩
  exact Tape.init_nil_cells_succ 0

/-- `emptyOutputTM` computes the constant empty-string function in zero time. -/
theorem emptyOutputTM_computesInTime (n : ℕ) :
    (emptyOutputTM n).ComputesInTime (fun _ => []) (fun _ => 0) := by
  intro x
  refine ⟨(emptyOutputTM n).initCfg x, 0, le_refl _, reachesIn.zero, rfl, ?_⟩
  exact hasOutput_init_nil

/-- `emptyOutputTM` computes the constant empty-string function in zero auxiliary
space: it is a transducer, every reachable configuration is the (halted) initial
one, and that configuration trivially respects the space bound. -/
theorem emptyOutputTM_computesInSpace (n : ℕ) :
    (emptyOutputTM n).ComputesInSpace (fun _ => []) (fun _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q iHead wHeads oHead
    simp [emptyOutputTM]
  · intro x c' hreach
    have hc' : c' = (emptyOutputTM n).initCfg x := reaches_eq_of_halted rfl hreach
    subst hc'
    refine ⟨fun i => ?_, ?_⟩
    · simp
    · simp
  · intro x
    exact ⟨(emptyOutputTM n).initCfg x, Relation.ReflTransGen.refl, rfl, hasOutput_init_nil⟩

-- ════════════════════════════════════════════════════════════════════════
-- ════════════════════════════════════════════════════════════════════════
-- The full compiler theorem (statement; proof is tracked future work)
-- ════════════════════════════════════════════════════════════════════════

/-- A *loaded start configuration* for the internal, layout-relative compiler
interface. The environment of an in-place program is a list of first-order
`Data` values `env : Fin m → Data`; a `LoadedStart` places entry `j` on the
designated work tape `slot j` (as its balanced-parenthesis serialization
`Data.toBits`) and leaves every other tape blank, with the machine in its start
state. This is the multi-tape analogue of `Cfg.init`: one work tape per program
argument, chosen by the caller through `slot`. -/
structure LoadedStart {k m : ℕ} (M : TM k) (slot : Fin m → Fin k)
    (env : Fin m → Data) (c : Cfg k M.Q) : Prop where
  /-- The machine is in its start state. -/
  state : c.state = M.qstart
  /-- The dedicated input tape is unused (blank). -/
  input : c.input = Tape.init []
  /-- The output tape starts blank. -/
  output : c.output = Tape.init []
  /-- Environment entry `j` sits on tape `slot j`, serialized via `Data.toBits`. -/
  envTape : ∀ j, c.work (slot j) = Tape.init ((env j).toBits.map Γ.ofBool)
  /-- Every non-environment work tape starts blank. -/
  cleanTape : ∀ i, (∀ j, i ≠ slot j) → c.work i = Tape.init []

/-- **The internal, layout-relative compiler contract.** `CompilesUnder M slot
res p a b` says the machine `M` implements program `p` for the environment
layout `slot` (argument `j` on work tape `slot j`) with the result deposited on
work tape `res`: for every first-order environment `env` and every RTM
derivation `ProgSem … p (.data result) t s`, starting from any `LoadedStart`,
the machine halts within `a·t + a` steps having written `result.toBits` on tape
`res`, and no reachable configuration moves any work head past cell `b·s + b`.

Because `Data.toBits` has length `Data.size` (`Data.toBits_length`), the tape
space charged here is exactly the RTM `Data.size` measure, so the space bound
`b·s + b` matches the RTM space `s` up to the constant `b`. This is the
predicate the structural recursion over `InPlace` is proved against; the public
`inPlace_compilesToTM` is the single-argument (`m = 1`) specialization wrapped
with a fixed input-tape ↦ argument-tape prologue and a result-tape ↦ output-tape
epilogue. -/
def CompilesUnder {k m : ℕ} (M : TM k) (slot : Fin m → Fin k) (res : Fin k)
    (p : Prog) (a b : ℕ) : Prop :=
  ∀ (env : Fin m → Data) (result : Data) (t s : ℕ),
    ProgSem (List.ofFn (fun j => Value.data (env j))) p (Value.data result) t s →
    ∀ c : Cfg k M.Q, LoadedStart M slot env c →
      (∃ (c' : Cfg k M.Q) (t' : ℕ), t' ≤ a * t + a ∧ M.reachesIn t' c c' ∧
        M.halted c' ∧ (c'.work res).HasOutput result.toBits) ∧
      (∀ c'', M.reaches c c'' → ∀ i, (c''.work i).head ≤ b * s + b)

/-- `Compiled m p`: the first-order program `p` compiles, for argument arity
`m`, to *some* Turing machine and tape layout satisfying the layout-relative
contract `CompilesUnder`. This is the codomain of the compiler recursion
`compilesUnder_of_inPlace`, and the shared shape of the per-constructor building
blocks below. -/
def Compiled (m : ℕ) (p : Prog) : Prop :=
  ∃ (k : ℕ) (M : TM k) (slot : Fin m → Fin k) (res : Fin k) (a b : ℕ),
    CompilesUnder M slot res p a b

/-- The empty-node writer: a 4-state machine over `m + 1` work tapes. From the
start state it steps all heads right off the left marker, then writes `0` and
`1` on the last (result) work tape, preserving all other tapes by writing back
what they read. This realizes `Prog.empty`, materializing `[false, true]` (the
`Data.toBits` of the empty node) on the result tape in three steps. -/
def emptyNodeTM (m : ℕ) : TM (m + 1) where
  Q := Fin 4
  qstart := 0
  qhalt := 3
  δ := fun q _ wHeads _ =>
    ( (if q = 0 then 1 else if q = 1 then 2 else 3),
      (fun i => if i = Fin.last m
                then (if q = 1 then Γw.zero else if q = 2 then Γw.one else Γw.blank)
                else (wHeads i).toΓwId),
      Γw.blank,
      Dir3.right,
      (fun _ => Dir3.right),
      Dir3.right )
  δ_right_of_start := by
    intro q iHead wHeads oHead
    exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- The configuration reached by one step of `emptyNodeTM` from a state `q`. -/
def emptyStepOut (m : ℕ) (cc : Cfg (m + 1) (Fin 4)) (q : Fin 4) : Cfg (m + 1) (Fin 4) :=
  { state := if q = 0 then 1 else if q = 1 then 2 else 3
    input := cc.input.move .right
    work := fun i => (cc.work i).writeAndMove
      ((if i = Fin.last m
        then (if q = 1 then Γw.zero else if q = 2 then Γw.one else Γw.blank)
        else ((cc.work i).read).toΓwId) : Γ) .right
    output := cc.output.writeAndMove ((Γw.blank : Γ)) .right }

/-- One step of `emptyNodeTM` from a non-halted state matches `emptyStepOut`. -/
theorem emptyStep (m : ℕ) (cc : Cfg (m + 1) (emptyNodeTM m).Q) (q : Fin 4)
    (hq : cc.state = q) (hq3 : q ≠ 3) :
    (emptyNodeTM m).step cc = some (emptyStepOut m cc q) := by
  unfold TM.step
  rw [if_neg (by rw [hq]; exact hq3)]
  subst hq
  simp only [emptyNodeTM, emptyStepOut, apply_ite Γw.toΓ]

/-- One rightward write-and-move advances the head by one. -/
theorem writeAndMove_right_head (t : Tape) (s : Γ) :
    (t.writeAndMove s Dir3.right).head = t.head + 1 := by
  simp [Tape.writeAndMove, Tape.move, Tape.write_head]

/-- A rightward write-and-move leaves the same cells as writing in place. -/
theorem writeAndMove_right_cells (t : Tape) (s : Γ) :
    (t.writeAndMove s Dir3.right).cells = (t.write s).cells := by
  simp [Tape.writeAndMove, Tape.move_cells]

/-- Writing at a nonzero head updates exactly that cell. -/
theorem write_cells_of_ne_zero {t : Tape} (h : t.head ≠ 0) (s : Γ) :
    (t.write s).cells = Function.update t.cells t.head s := by
  simp [Tape.write, h]

/-- **Compiler part — `var i`** (statement only). A variable read compiles: the
machine copies the argument tape `slot i` (when `i < m`, else the empty node) to
the result tape. Matches `ProgSem.var`, whose time and space are the size of the
read value. -/
theorem compiled_var (m i : ℕ) : Compiled m (Prog.var i) := by
  sorry

/-- **Compiler part — `empty`.** The empty constructor compiles to `emptyNodeTM`,
a 4-state machine that writes the empty node `Data.empty.toBits = [false, true]`
on the result tape in three steps (all heads advance rightward each step).
Matches `ProgSem.empty` (time and space `2`): the run has length `3 ≤ 2·2 + 2`
and every reachable work head stays within `2·2 + 2`. -/
theorem compiled_empty (m : ℕ) : Compiled m Prog.empty := by
  refine ⟨m + 1, emptyNodeTM m, Fin.castSucc, Fin.last m, 2, 2, ?_⟩
  intro env result t s hsem c hstart
  cases hsem
  have hstate : c.state = (0 : Fin 4) := hstart.state
  have hres0 : c.work (Fin.last m) = Tape.init [] :=
    hstart.cleanTape (Fin.last m) (fun j => (Fin.castSucc_lt_last j).ne')
  have hheads0 : ∀ i, (c.work i).head = 0 := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [hres0]; rfl
    · intro j; rw [hstart.envTape j]; rfl
  set c1 := emptyStepOut m c 0 with hc1
  set c2 := emptyStepOut m c1 1 with hc2
  set c3 := emptyStepOut m c2 2 with hc3
  have hs0 : (emptyNodeTM m).step c = some c1 := emptyStep m c 0 hstate (by decide)
  have hc1state : c1.state = 1 := by rw [hc1]; simp [emptyStepOut]
  have hs1 : (emptyNodeTM m).step c1 = some c2 := emptyStep m c1 1 hc1state (by decide)
  have hc2state : c2.state = 2 := by rw [hc2]; simp [emptyStepOut]
  have hs2 : (emptyNodeTM m).step c2 = some c3 := emptyStep m c2 2 hc2state (by decide)
  have hc3state : c3.state = 3 := by rw [hc3]; simp [emptyStepOut]
  have htrace : (emptyNodeTM m).reachesIn 3 c c3 := .step hs0 (.step hs1 (.step hs2 .zero))
  -- The result tape after three steps.
  set t0 : Tape := Tape.init [] with ht0
  set t1 : Tape := t0.writeAndMove ((Γw.blank : Γ)) Dir3.right with ht1
  set t2 : Tape := t1.writeAndMove ((Γw.zero : Γ)) Dir3.right with ht2
  set t3 : Tape := t2.writeAndMove ((Γw.one : Γ)) Dir3.right with ht3
  have rres : c3.work (Fin.last m) = t3 := by
    simp only [hc3, hc2, hc1, emptyStepOut, ht3, ht2, ht1, ht0, hres0]
    simp
  have hh1 : t1.head = 1 := by rw [ht1, writeAndMove_right_head]; rfl
  have hh2 : t2.head = 2 := by rw [ht2, writeAndMove_right_head, hh1]
  -- Cells of the result tape.
  have hc2cells : t2.cells = Function.update t0.cells 1 ((Γw.zero : Γ)) := by
    rw [ht2, writeAndMove_right_cells, write_cells_of_ne_zero (by rw [hh1]; decide),
      hh1, ht1, writeAndMove_right_cells, Tape.write, ht0]
    simp
  have hc3cells : t3.cells =
      Function.update (Function.update t0.cells 1 ((Γw.zero : Γ))) 2 ((Γw.one : Γ)) := by
    rw [ht3, writeAndMove_right_cells, write_cells_of_ne_zero (by rw [hh2]; decide),
      hh2, hc2cells]
  have hle : (3 : ℕ) ≤ 2 * 2 + 2 := by omega
  refine ⟨⟨c3, 3, hle, htrace, ?_, ?_⟩, ?_⟩
  · -- halted
    show c3.state = (emptyNodeTM m).qhalt
    rw [hc3state]; rfl
  · -- the result tape holds `[false, true]`
    rw [rres]
    have htb : (Data.l []).toBits = [false, true] := by simp
    rw [htb, Tape.HasOutput]
    refine ⟨?_, ?_⟩
    · intro i hi
      rcases i with _ | _ | i
      · rw [hc3cells, Function.update_of_ne (by decide), Function.update_self]; rfl
      · rw [hc3cells, Function.update_self]; rfl
      · simp only [List.length_cons, List.length_nil] at hi; omega
    · rw [hc3cells, Function.update_of_ne (by decide), Function.update_of_ne (by decide), ht0]
      simp
  · -- space bound: every reachable configuration keeps work heads within `2·2 + 2`
    have head_c1 : ∀ i, (c1.work i).head = (c.work i).head + 1 := by
      intro i; rw [hc1]; simp only [emptyStepOut]; exact writeAndMove_right_head _ _
    have head_c2 : ∀ i, (c2.work i).head = (c1.work i).head + 1 := by
      intro i; rw [hc2]; simp only [emptyStepOut]; exact writeAndMove_right_head _ _
    have head_c3 : ∀ i, (c3.work i).head = (c2.work i).head + 1 := by
      intro i; rw [hc3]; simp only [emptyStepOut]; exact writeAndMove_right_head _ _
    have B0 : ∀ i, (c.work i).head ≤ 2 * 2 + 2 := fun i => by rw [hheads0 i]; omega
    have B1 : ∀ i, (c1.work i).head ≤ 2 * 2 + 2 := fun i => by
      rw [head_c1 i, hheads0 i]; omega
    have B2 : ∀ i, (c2.work i).head ≤ 2 * 2 + 2 := fun i => by
      rw [head_c2 i, head_c1 i, hheads0 i]; omega
    have B3 : ∀ i, (c3.work i).head ≤ 2 * 2 + 2 := fun i => by
      rw [head_c3 i, head_c2 i, head_c1 i, hheads0 i]; omega
    have hc3h : c3.state = (emptyNodeTM m).qhalt := hc3state
    have hnone : (emptyNodeTM m).step c3 = none := step_eq_none_iff_halted.mpr hc3h
    intro c'' hreach i
    rcases Relation.ReflTransGen.cases_head hreach with rfl | ⟨d1, hd1, hr1⟩
    · exact B0 i
    · simp only [TM.stepRel] at hd1; rw [hs0] at hd1; injection hd1 with hd1; subst hd1
      rcases Relation.ReflTransGen.cases_head hr1 with rfl | ⟨d2, hd2, hr2⟩
      · exact B1 i
      · simp only [TM.stepRel] at hd2; rw [hs1] at hd2; injection hd2 with hd2; subst hd2
        rcases Relation.ReflTransGen.cases_head hr2 with rfl | ⟨d3, hd3, hr3⟩
        · exact B2 i
        · simp only [TM.stepRel] at hd3; rw [hs2] at hd3; injection hd3 with hd3; subst hd3
          rcases Relation.ReflTransGen.cases_head hr3 with rfl | ⟨d4, hd4, _⟩
          · exact B3 i
          · simp only [TM.stepRel] at hd4; rw [hnone] at hd4; exact absurd hd4 (by simp)

/-- **Compiler part — `cons h t`** (statement only). Given compiled sub-machines
for `h` and `t`, `cons` runs them on disjoint tape banks and prepends the head
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
first-order (`InPlace`) program compiles to a Turing machine together with a tape
layout satisfying the layout-relative contract `CompilesUnder`.

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

/-- **A caller-chosen tape layout** for running an `m`-argument in-place RTM
program as a subroutine on a `Fin k` tape bank using `sc` scratch tapes. As with
the binary-arithmetic subroutines, the caller picks every index; the fields
record that they are pairwise distinct so the machine can treat them as
independent registers.

- `argIdx j` — the tape variable `j` is read from;
- `resIdx` — the tape the result is written to;
- `scratchIdx l` — the `l`-th auxiliary tape the machine may use. -/
structure SubroutineLayout (m sc k : ℕ) where
  /-- Variable `j` is read from work tape `argIdx j`. -/
  argIdx : Fin m → Fin k
  /-- The result is deposited on work tape `resIdx`. -/
  resIdx : Fin k
  /-- The `sc` auxiliary work tapes the machine may use. -/
  scratchIdx : Fin sc → Fin k
  /-- Distinct variables use distinct tapes. -/
  argIdx_inj : Function.Injective argIdx
  /-- Distinct scratch slots use distinct tapes. -/
  scratchIdx_inj : Function.Injective scratchIdx
  /-- No argument tape coincides with the result tape. -/
  arg_ne_res : ∀ j, argIdx j ≠ resIdx
  /-- No scratch tape coincides with the result tape. -/
  scratch_ne_res : ∀ l, scratchIdx l ≠ resIdx
  /-- Argument tapes and scratch tapes are disjoint. -/
  arg_ne_scratch : ∀ j l, argIdx j ≠ scratchIdx l

/-- The starting tape assignment expected by a `SubroutineLayout`: environment
entry `j` sits on its argument tape as the balanced-parenthesis serialization
`Data.toBits`, and the result and scratch tapes start blank. Tapes outside the
layout are unconstrained (and preserved as a frame). -/
def SubroutineLayout.Loaded {m sc k : ℕ} (L : SubroutineLayout m sc k)
    (env : Fin m → Data) (work : Fin k → Tape) : Prop :=
  (∀ j, work (L.argIdx j) = Tape.init ((env j).toBits.map Γ.ofBool)) ∧
  work L.resIdx = Tape.init [] ∧
  (∀ l, work (L.scratchIdx l) = Tape.init [])

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

Inputs live on the chosen argument work tapes, *not* the dedicated input tape
(which stays blank), so the space charge is over `Data.toBits`; by
`Data.toBits_length` it matches the RTM `Data.size` measure up to `b`. Exposing
`sc` tells the caller how many auxiliary tapes to reserve, and the
"only the result tape changes" frame makes `M` freely composable. -/
def Prog.RunsAsSubroutine (p : Prog) (m : ℕ) : Prop :=
  ∃ sc a b : ℕ, ∀ {k : ℕ} (L : SubroutineLayout m sc k),
    ∃ M : TM k, ∀ (env : Fin m → Data) (result : Data) (t s : ℕ)
      (work₀ : Fin k → Tape),
      ProgSem (List.ofFn (fun j => Value.data (env j))) p (Value.data result) t s →
      L.Loaded env work₀ →
      M.HoareTimeSpace
        (fun inp work out => inp = Tape.init [] ∧ work = work₀ ∧ out = Tape.init [])
        (fun inp work out => inp = Tape.init [] ∧ out = Tape.init [] ∧
          (work L.resIdx).HasOutput result.toBits ∧
          (∀ i, i ≠ L.resIdx → work i = work₀ i))
        (a * t + a) 0 (b * s + b)

/-- **The full in-place RTM → Turing-machine compiler theorem.** Every
first-order (`InPlace`) rose tree machine program compiles, at any argument
arity `m`, to a reusable tape-indexed Turing-machine subroutine
(`Prog.RunsAsSubroutine`): the caller runs it at tape indices of their choosing,
inputs are serialized via `Data.toBits`, and time/space match the RTM `ProgSem`
bounds up to a constant. See `Prog.RunsAsSubroutine` for the precise contract.

The base case `empty` is discharged by `compiled_empty`; the remaining
constructors are tracked in `ROADMAP.md`, track N0. The statement is provided
now so the subroutine interface is fixed; the proof is deferred. -/
theorem inPlace_compilesToTM {m : ℕ} (p : Prog) (hp : InPlace p) :
    p.RunsAsSubroutine m := by
  sorry

end RoseTreeMachine

end Complexity
