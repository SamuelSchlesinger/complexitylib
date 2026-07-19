/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexitylib.Models.RoseTreeMachine.Prog
import Complexitylib.Models.TuringMachine.Subroutines.CopyOutput

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

- `RoseTreeMachine.CompilesUnder` — the internal, **layout-relative** compiler
  contract: a machine implements a program for an environment layout that places
  one program argument per work tape (`slot : Fin m → Fin k`) and deposits the
  result on a chosen tape, with time/space matched to the RTM `ProgSem` bounds.
  This is where "multiple inputs map to tapes" lives.
- `RoseTreeMachine.LoadedStart` — the multi-tape analogue of `Cfg.init`: the
  starting configuration for `CompilesUnder`, with each argument serialized onto
  its designated tape via `Data.toBits`.
- `RoseTreeMachine.InPlaceRealizedByTM` — the (single-input) correspondence
  predicate: an `InPlace` program computing a binary function `f` is realized by
  some Turing machine that computes `f` with time and space bounds dominated by
  the program's RTM bounds.
- `RoseTreeMachine.emptyOutputTM` — the one-state machine that halts immediately
  with empty output.

## Main results

- `RoseTreeMachine.inPlace_compilesToTM` — **the full public compiler theorem**
  (stated now; proof deferred, see *Scope*): every `InPlace` program compiles to
  a single Turing machine, usable as a subroutine, whose time and space are
  within a constant factor of the program's RTM bounds.
- `RoseTreeMachine.compilesUnder_of_inPlace` — **the internal recursion**
  (statement only): every `InPlace` program compiles, for a fixed argument
  arity, to a machine plus a tape layout satisfying `CompilesUnder`. This is the
  theorem proved by structural recursion; `inPlace_compilesToTM` is its
  single-argument wrapper.
- `RoseTreeMachine.dataSize_encode_bool`, `dataSize_encode_listBool` — the binary
  encoding of a `List Bool` has `Data.size` linear in the list length; the
  reusable bridge between input length and RTM cost.
- `RoseTreeMachine.emptyOutputTM_computesInTime` /
  `emptyOutputTM_computesInSpace` — the trivial machine computes `fun _ => []`
  in zero time and zero auxiliary space.
- `RoseTreeMachine.empty_realized` — the `InPlace` program `empty` is realized by
  a Turing machine with matching time *and* space.
- `RoseTreeMachine.identity_time_matches` — the `InPlace` program `var 0` and the
  input-to-output copy machine both compute the identity, with the machine's
  exact time bound `n + 2` dominated by the program's RTM bound `4·n + 2`.

## Scope

This is the first verified slice of the `InPlace`-RTM → TM compiler. The
headline `inPlace_compilesToTM` and the internal recursion
`compilesUnder_of_inPlace` are stated but their proofs are currently `sorry`:
the inductive constructors (`cons`, `elim`, `ifEq`, `while_`, and the
immediately consumed `app`/`fn` let-binding) require concrete data-manipulation
subroutines over the `Data` encoding and are tracked as future work in
`ROADMAP.md` (track N0). The base cases are already proven (`empty_realized`,
`identity_time_matches`). The framework here — the `CompilesUnder` /
`LoadedStart` layout-relative interface, the `InPlaceRealizedByTM` predicate,
the `Data.toBits` tape serialization, the encoding-size bridge, the two proven
base cases, and the fixed statements of both theorems — pins down the interface
those constructors will compose through.

> Note: `compilesUnder_of_inPlace` and `inPlace_compilesToTM` use `sorry`, so
> `lake build --wfail` and the axiom guard will report them until the proofs are
> supplied.
-/

namespace Complexity

namespace RoseTreeMachine

open Complexity.TM

-- ════════════════════════════════════════════════════════════════════════
-- Encoding-size bridge: `Data.size` of a binary encoding is linear
-- ════════════════════════════════════════════════════════════════════════

/-- Each `Bool` encodes to a `Data` value of size at most `4` (`false ↦ 2`,
`true ↦ 4`). -/
lemma dataSize_encode_bool (b : Bool) : Data.size (DataEncode.encode b) ≤ 4 := by
  cases b <;> simp [DataEncode.encode]

/-- The binary encoding of a `List Bool` has `Data.size` bounded linearly by the
list length: `Data.size (encode x) ≤ 4·|x| + 2`. This is the bridge between a
Turing machine's input length `n` and the RTM cost of manipulating `encode x`. -/
lemma dataSize_encode_listBool (x : List Bool) :
    Data.size (DataEncode.encode x) ≤ 4 * x.length + 2 := by
  induction x with
  | nil => simp [DataEncode.encode]
  | cons b bs ih =>
    have hrw : DataEncode.encode (b :: bs)
        = Data.l (DataEncode.encode b :: bs.map DataEncode.encode) := by
      simp [DataEncode.encode]
    have hbs : Data.l (bs.map DataEncode.encode) = DataEncode.encode bs := by
      simp [DataEncode.encode]
    rw [hrw, Data.cons_size, hbs]
    have hb := dataSize_encode_bool b
    simp only [List.length_cons]
    omega

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
-- The correspondence predicate and the proven base cases
-- ════════════════════════════════════════════════════════════════════════

/-- An `InPlace` rose tree machine program `p` computing the binary function `f`
is *realized by a Turing machine* when some machine computes the same `f` with
time and space bounds dominated by `p`'s RTM `ProgSem` bounds. This is the
compiler's per-program correctness-and-resource contract. -/
def InPlaceRealizedByTM (p : Prog) (f : List Bool → List Bool) : Prop :=
  InPlace p ∧
  ∃ tR sR : ℕ → ℕ, p.ComputesBoolFunInTimeAndSpace f tR sR ∧
    ∃ (k : ℕ) (M : TM k) (tT sT : ℕ → ℕ),
      M.ComputesInTime f tT ∧ M.ComputesInSpace f sT ∧
      (∀ n, tT n ≤ tR n) ∧ (∀ n, sT n ≤ sR n)

/-- **The `empty` program is realized by a Turing machine with matching time and
space.** The `InPlace` program `empty` computes the constant empty-string
function in RTM time and space `2`, and `emptyOutputTM` computes the same
function in `0` time and `0` auxiliary space, both dominated by `2`. -/
theorem empty_realized : InPlaceRealizedByTM Prog.empty (fun _ => []) := by
  refine ⟨InPlace.empty, (fun _ => 2), (fun _ => 2), ?_, 0, emptyOutputTM 0,
    (fun _ => 0), (fun _ => 0), emptyOutputTM_computesInTime 0,
    emptyOutputTM_computesInSpace 0, fun _ => by dsimp only; omega,
    fun _ => by dsimp only; omega⟩
  intro x
  refine ⟨2, le_refl _, 2, le_refl _, ?_⟩
  show ProgSem [Value.data (DataEncode.encode x)] Prog.empty
    (Value.data (DataEncode.encode ([] : List Bool))) 2 2
  rw [DataEncode_list_nil]
  exact ProgSem.empty

/-- The `InPlace` program `var 0` computes the identity binary function in RTM
time and space `4·n + 2` (the `Data.size` of the encoded input, bounded via
`dataSize_encode_listBool`). -/
theorem var0_computesBoolFun_id :
    (Prog.var 0).ComputesBoolFunInTimeAndSpace id
      (fun n => 4 * n + 2) (fun n => 4 * n + 2) := by
  intro x
  refine ⟨Data.size (DataEncode.encode x), dataSize_encode_listBool x,
    Data.size (DataEncode.encode x), dataSize_encode_listBool x, ?_⟩
  show ProgSem [Value.data (DataEncode.encode x)] (Prog.var 0)
    (Value.data (DataEncode.encode (id x))) _ _
  have h : ProgSem [Value.data (DataEncode.encode x)] (Prog.var 0) _ _ _ := ProgSem.var
  simpa using h

/-- **The `var 0` program and the copy machine both compute the identity, with
matching (linear) time.** The `InPlace` program `var 0` computes the identity in
RTM time `4·n + 2`, and `copyInputToOutputTM` computes the identity in the exact
time bound `n + 2 ≤ 4·n + 2`. (The copy machine also uses only its fixed,
here empty, work-tape bank; a formal `ComputesInSpace` certificate is tracked
with the remaining constructors.) -/
theorem identity_time_matches :
    InPlace (Prog.var 0) ∧
    (Prog.var 0).ComputesBoolFunInTimeAndSpace id (fun n => 4 * n + 2)
      (fun n => 4 * n + 2) ∧
    ∃ (k : ℕ) (M : TM k) (T : ℕ → ℕ),
      M.ComputesInTime id T ∧ ∀ n, T n ≤ 4 * n + 2 :=
  ⟨InPlace.var, var0_computesBoolFun_id, 0, copyInputToOutputTM (n := 0),
    (fun m => m + 2), copyInputToOutputTM_computesInTime 0, fun n => by dsimp only; omega⟩

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

/-- **The internal compiler recursion (statement only; proof deferred).** For a
fixed argument arity `m`, every first-order (`InPlace`) program compiles to a
Turing machine together with a tape layout (`slot`, `res`) and constant factors
`a`, `b` satisfying the layout-relative contract `CompilesUnder`.

This is the workhorse proved by structural recursion on the `InPlace`
derivation: `var i` reads tape `slot i`; `empty` writes the empty node; `cons`
runs its two sub-machines on disjoint tape banks and concatenates; `elim`,
`ifEq`, and `while_` branch/loop over the sub-machines; and the immediately
consumed `app`/`fn` let-binding allocates one fresh environment tape (extending
`slot` for the `σ ++ [v]` body). Each constructor composes the sub-machines'
`CompilesUnder` certificates, accumulating `a`, `b` additively — matching the
`ProgSem` cost rules up to a constant. The base cases mirror `empty_realized`
and `identity_time_matches`. -/
theorem compilesUnder_of_inPlace {m : ℕ} (p : Prog) (hp : InPlace p) :
    ∃ (k : ℕ) (M : TM k) (slot : Fin m → Fin k) (res : Fin k) (a b : ℕ),
      CompilesUnder M slot res p a b := by
  sorry

/-- **The full in-place RTM → Turing-machine compiler theorem.**

For every first-order (`InPlace`) rose tree machine program `p`, there is a
Turing machine `M` and constants `a`, `b` such that, whenever `p` computes a
binary function `f` within RTM time `tR` and space `sR`, the *single* machine
`M` computes the same `f` within Turing-machine time `a·tR + a` and auxiliary
space `b·sR + b`.

The machine `M` and constants `a`, `b` depend only on `p` (they are produced by
compiling `p`), not on the function `f` being analyzed; by value-determinism of
`ProgSem` there is at most one such `f`. The constants capture the "match up to
a constant factor" convention documented at the top of this file.

Because `M` carries ordinary `ComputesInTime` / `ComputesInSpace` certificates,
it is directly usable as a **subroutine** — for instance composed with other
machines through `TM.seqTM` or `TM.compositionTM`.

This public statement keeps the standard single-input / single-output interface
of the whole subroutine ecosystem; the multi-tape flexibility (one work tape per
program argument) lives in the internal layout-relative contract
`CompilesUnder` / `compilesUnder_of_inPlace`. The plan is to derive this theorem
as the `m = 1` specialization of `compilesUnder_of_inPlace`, wrapping the
resulting machine with a prologue that unpacks the single input tape onto the
one environment tape and an epilogue that copies the result tape to the output
tape. Tape *renumbering* for arbitrary call sites is then handled externally by
the existing `Lift` / `RetargetCompute` / `Placement` combinators.

The proof compiles `p` by structural recursion on the `InPlace` derivation,
implementing each constructor with `Data`-manipulation subroutines over the
binary encoding and accumulating the resource bounds compositionally. The base
cases `empty` and `var 0` are already discharged by `empty_realized` and
`identity_time_matches`; the inductive constructors (`cons`, `elim`, `ifEq`,
`while_`, and the immediately consumed `app`/`fn` let-binding) remain to be
built (tracked in `ROADMAP.md`, track N0). The statement is provided now so the
subroutine interface is fixed; the proof is deferred. -/
theorem inPlace_compilesToTM (p : Prog) (hp : InPlace p) :
    ∃ (k : ℕ) (M : TM k) (a b : ℕ),
      ∀ (f : List Bool → List Bool) (tR sR : ℕ → ℕ),
        p.ComputesBoolFunInTimeAndSpace f tR sR →
        M.ComputesInTime f (fun n => a * tR n + a) ∧
        M.ComputesInSpace f (fun n => b * sR n + b) := by
  sorry

end RoseTreeMachine

end Complexity
