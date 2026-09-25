/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Complexitylib.Models.TuringMachine
public import Mathlib.Tactic.DeriveFintype

/-!
# Simulating CSLib multi-tape machines on Complexitylib machines

This file defines a Complexitylib machine (`TM k`) that simulates a binary
CSLib multi-tape machine (`Turing.MultiTapeTM k Bool S`) with the same number
of work tapes. It is the converse direction of
`Complexitylib.Interop.Cslib.MultiTape`.

The simulator bridges the two models as follows.

- **Symbols.** CSLib cells hold `Option Bool`; the blank `none` becomes `□`
  and `some b` becomes the bit `b`.
- **Two-way work tapes.** Each CSLib work tape is folded onto one of our
  one-sided work tapes: CSLib cell `z ≥ 0` lives in our cell `2 z + 1`, and
  CSLib cell `z < 0` in our cell `-2 z`. Our cell `0` (`▷`) is never used. A
  sign flag in the control state records which half the head is on. A CSLib
  head move becomes a move by two cells, or by one cell across the fold; the
  fold is detected by bumping into `▷`.
- **Phases.** Each CSLib step takes three of our steps: phase `0` (`run`)
  reads all heads, applies CSLib's transition, writes, and starts the head
  moves; phases `1` and `2` (`mid1`, `mid2`) finish them.
- **Input head.** Our input head sits on the cell with CSLib's input position:
  cell `0` (`▷`) is CSLib's left blank and cell `|x| + 1` its right blank.
  CSLib clamps moves past either blank. Since our head must leave `▷` at once,
  staying on position `0` is simulated by moving right and then back left.
- **Output.** CSLib emits output symbols one at a time. The simulator writes
  each emitted bit on its output tape and moves right, so the first emitted
  bit (CSLib's verdict) lands in output cell `1`.

## Main definitions

- `Complexity.FromMultiTape.St` — the simulator's states
- `Complexity.FromMultiTape.toTM` — the Complexitylib machine simulating a
  CSLib machine
-/


@[expose] public section

namespace Complexity

open Turing

/-- Read one of our symbols as a binary CSLib cell: `□` and `▷` are blank. -/
def Γ.toCell : Γ → Option Bool
  | .zero => some false
  | .one => some true
  | .blank => none
  | .start => none

/-- Store a binary CSLib cell as a writable symbol, with CSLib's blank as `□`. -/
def Γw.ofCell : Option Bool → Γw
  | none => .blank
  | some false => .zero
  | some true => .one

/-- The writable symbol that rewrites `s` unchanged (off the left-end marker). -/
def Γ.keep : Γ → Γw
  | .zero => .zero
  | .one => .one
  | .blank => .blank
  | .start => .blank

/-- Guard a head direction: a head reading `▷` moves right, as `TM.δ_right_of_start`
requires; otherwise it moves in direction `d`. -/
def Dir3.guard (r : Γ) (d : Dir3) : Dir3 :=
  if r = Γ.start then .right else d

namespace FromMultiTape

/-- What a folded work tape still has to do in phases `1` and `2` of a
simulated step. -/
inductive Plan where
  /-- Nothing more; the head is in place. -/
  | idle
  /-- One more move right (a move away from the fold, begun in phase `0`). -/
  | out
  /-- On the nonnegative half, moving toward the fold: one more left move,
  unless the head bumped into `▷`, in which case it crosses the fold. -/
  | inPos
  /-- On the negative half, moving toward the fold: one more left move, then
  a check for `▷` in phase `2`. -/
  | inNeg
  /-- Crossing from CSLib cell `0` to cell `-1`: one more move right. -/
  | cross
  deriving DecidableEq

instance : Fintype Plan where
  elems := {.idle, .out, .inPos, .inNeg, .cross}
  complete := fun p => by cases p <;> simp

/-- The simulator's states, for a CSLib machine with `k` work tapes and state
type `S`. The sign flags say, for each work tape, whether the CSLib head is at
a negative position. -/
inductive St (k : ℕ) (S : Type) where
  /-- Move every head off `▷`. -/
  | init
  /-- Phase `0`: simulate one step of CSLib state `q`. -/
  | run (q : S) (sign : Fin k → Bool)
  /-- Phase `1`: continue the moves; CSLib is now in state `q`. -/
  | mid1 (q : S) (sign : Fin k → Bool) (plan : Fin k → Plan) (inDir : Dir3)
  /-- Phase `2`: finish the moves, including the input head move `inDir`. -/
  | mid2 (q : S) (sign : Fin k → Bool) (plan : Fin k → Plan) (inDir : Dir3)
  /-- CSLib halted. -/
  | halt
  deriving DecidableEq

/-- The simulator's states as a sum of finite types. -/
def St.equivSum (k : ℕ) (S : Type) : St k S ≃
    Unit ⊕ (S × (Fin k → Bool)) ⊕ (S × (Fin k → Bool) × (Fin k → Plan) × Dir3) ⊕
      (S × (Fin k → Bool) × (Fin k → Plan) × Dir3) ⊕ Unit where
  toFun
    | .init => .inl ()
    | .run q sg => .inr (.inl (q, sg))
    | .mid1 q sg pl d => .inr (.inr (.inl (q, sg, pl, d)))
    | .mid2 q sg pl d => .inr (.inr (.inr (.inl (q, sg, pl, d))))
    | .halt => .inr (.inr (.inr (.inr ())))
  invFun
    | .inl () => .init
    | .inr (.inl (q, sg)) => .run q sg
    | .inr (.inr (.inl (q, sg, pl, d))) => .mid1 q sg pl d
    | .inr (.inr (.inr (.inl (q, sg, pl, d)))) => .mid2 q sg pl d
    | .inr (.inr (.inr (.inr ()))) => .halt
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with _ | _ | _ | _ | _ <;> rfl

instance {k : ℕ} {S : Type} [Fintype S] : Fintype (St k S) :=
  Fintype.ofEquiv _ (St.equivSum k S).symm

/-- Phase `0` of a folded work-tape move `m`, on the negative half when `s`
holds: the remaining plan and the first head move. -/
def plan0 (s : Bool) : SignType → Plan × Dir3
  | .zero => (.idle, .stay)
  | .pos => if s then (.inNeg, .left) else (.out, .right)
  | .neg => if s then (.out, .right) else (.inPos, .left)

/-- Phase `1` of a folded work-tape move with plan `p`, sign flag `s`, and
symbol `r` under the head: the next plan, the next sign flag, and the move. -/
def plan1 (p : Plan) (s : Bool) (r : Γ) : Plan × Bool × Dir3 :=
  match p with
  | .out => (.idle, s, .right)
  | .inPos => if r = Γ.start then (.cross, true, .right) else (.idle, s, .left)
  | .inNeg => (.inNeg, s, .left)
  | .idle => (.idle, s, .stay)
  | .cross => (.cross, s, .stay)

/-- Phase `2` of a folded work-tape move with plan `p`, sign flag `s`, and
symbol `r` under the head: the next sign flag and the move. -/
def plan2 (p : Plan) (s : Bool) (r : Γ) : Bool × Dir3 :=
  match p with
  | .cross => (s, .right)
  | .inNeg => if r = Γ.start then (false, .right) else (s, .stay)
  | _ => (s, .stay)

/-- The input head move made in phase `2` to simulate CSLib input move `m`,
where `r` is the input symbol read in phase `0`. On `▷` the head already moved
right in phase `0`; elsewhere a right move off the right blank is clamped. -/
def inputPlan (r : Γ) (m : SignType) : Dir3 :=
  if r = Γ.start then (if m = .pos then .stay else .left)
  else
    match m with
    | .pos => if r = Γ.blank then .stay else .right
    | .neg => .left
    | .zero => .stay

/-- The symbol written in phase `0` for a CSLib write `wr` over symbol `r`. -/
def writeSym (r : Γ) : Option (Option Bool) → Γw
  | none => r.keep
  | some c => Γw.ofCell c

/-- The symbol written on our output tape over symbol `o` when CSLib emits `e`. -/
def outSym (o : Γ) : Option Bool → Γw
  | none => o.keep
  | some b => Γw.ofBool b

/-- The output head move when CSLib emits `e`: right after each emitted bit. -/
def outDir : Option Bool → Dir3
  | none => .stay
  | some _ => .right

variable {k : ℕ} {S : Type}

/-- The simulator's transition function. Every direction is passed through
`Dir3.guard`, so heads on `▷` always move right. -/
def δ (M : MultiTapeTM k Bool S) (q : St k S) (i : Γ) (w : Fin k → Γ) (o : Γ) :
    St k S × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 :=
  match q with
  | .init =>
    (.run M.q₀ (fun _ => false), fun j => (w j).keep, o.keep, Dir3.guard i .stay,
      fun j => Dir3.guard (w j) .stay, Dir3.guard o .stay)
  | .run q sg =>
    let a := M.tr q i.toCell (fun j => (w j).toCell)
    let pl := fun j => plan0 (sg j) (a.workTapes j).2
    let q' : St k S := match a.state with
      | none => .halt
      | some q' => .mid1 q' sg (fun j => (pl j).1) (inputPlan i a.inputTape)
    (q', fun j => writeSym (w j) (a.workTapes j).1, outSym o a.output, Dir3.guard i .stay,
      fun j => Dir3.guard (w j) (pl j).2, Dir3.guard o (outDir a.output))
  | .mid1 q sg pl d =>
    let r := fun j => plan1 (pl j) (sg j) (w j)
    (.mid2 q (fun j => (r j).2.1) (fun j => (r j).1) d, fun j => (w j).keep, o.keep,
      Dir3.guard i .stay, fun j => Dir3.guard (w j) (r j).2.2, Dir3.guard o .stay)
  | .mid2 q sg pl d =>
    let r := fun j => plan2 (pl j) (sg j) (w j)
    (.run q (fun j => (r j).1), fun j => (w j).keep, o.keep, Dir3.guard i d,
      fun j => Dir3.guard (w j) (r j).2, Dir3.guard o .stay)
  | .halt =>
    (.halt, fun j => (w j).keep, o.keep, Dir3.guard i .stay,
      fun j => Dir3.guard (w j) .stay, Dir3.guard o .stay)

/-- Guarded directions move right off `▷`. -/
theorem Dir3.guard_start (d : Dir3) : Dir3.guard Γ.start d = .right := by
  simp [Dir3.guard]

/-- The Complexitylib machine simulating the binary CSLib machine `M`, with one
folded work tape per CSLib work tape. -/
def toTM [DecidableEq S] [Fintype S] (M : MultiTapeTM k Bool S) : TM k where
  Q := St k S
  qstart := .init
  qhalt := .halt
  δ := δ M
  δ_right_of_start := by
    intro q i w o
    refine ⟨fun h => ?_, fun j h => ?_, fun h => ?_⟩ <;>
      cases q <;> simp only [h, Dir3.guard_start]

end FromMultiTape

end Complexity
