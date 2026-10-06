/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Rectangle
public import Mathlib.Basic.Real.Basic

/-!
# Weighted threshold programs and one-dimensional capacity

This file fixes the definitions of the one-dimensional capacity method for threshold circuits
of unbounded depth.

## Rectangles

`TwoSidedRectangleFree f K` says that under every split of the coordinates into `U` and its
complement, every rectangle `P × Q` on which `f` is constant (with either value) has a side
with fewer than `K` elements. The one-sided `Cutwidth.RectangleFree` only excludes rectangles
on which `f` is identically `1`.

## Change counts

`ChangesAtMost Ψ T` is the discrete form of "`Ψ : ℝ → β` has at most `T + 1` interval pieces":
along every nondecreasing sequence of reals, the value of `Ψ` changes at most `T` times. A
threshold function `t ↦ [λ t + c ≥ 0]` changes at most once, and a multilevel threshold
function with `T` transitions changes at most `T` times. `PiecesAtMost Φ M` is the
constructive form used for runs of threshold gates: `Φ` is constant on the level sets of a
monotone rank function with fewer than `M` values.

## Threshold programs

`Program n s` is a straight-line program of `s` weighted threshold gates on `n` Boolean inputs,
with arbitrary real weights, arbitrary depth, and arbitrary fan-in and fan-out. Gate `j` reads
every input `x i` with weight `inputWeight j i` and every earlier gate `k < j` with weight
`gateWeight j k`, and outputs `1` exactly when its weighted sum plus `bias j` is nonnegative.
Integer weights are a special case. Booleans enter the sums as `0` and `1`. A gate is
*input-reading* when its input weight vector is nonzero (`Program.inputGates`); gates that read
only other gates are not counted by the bounds of this development.

`Program.evalFrom` evaluates the gates when some gates are overridden by given values and the
other gates receive arbitrary real input contributions in place of their weighted input sums;
the ordinary evaluation `Program.eval` overrides nothing and uses the true weighted sums. The
override form expresses a run of gates as a function of one real parameter.

## Block decompositions

A `BlockDecomposition f H` presents `f` as the output of a sequence of histories
`history i : {0,1}ⁿ → H`, starting from a constant one. Each step is one-dimensional (the next
history is a function of the previous one and of a single weighted sum `⟨w, x⟩`, with at most
`T` changes in the weighted sum for each previous history) or a summary (under every split, the
next history depends on the first side only through a value with at most `V` possibilities).
Its cost multiplies `4T` over the one-dimensional steps with `T ≥ 1` and `V` over the summary
steps.
-/

@[expose] public section

namespace Algebraic.Threshold

open Cutwidth

variable {n : ℕ}

/-- `f` is *two-sided `K`-rectangle-free* when, under every split of the coordinates into `U`
and its complement, every rectangle `P × Q` on which `f` is constant has a side with fewer than
`K` elements. -/
def TwoSidedRectangleFree (f : Cslib.BooleanFunction n) (K : ℕ) : Prop :=
  ∀ (U : Finset (Fin n)) (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)) (b : Bool),
    (∀ p ∈ P, ∀ q ∈ Q, f (glue U p q) = b) → P.card < K ∨ Q.card < K

/-- `Ψ` *changes at most `T` times*: along every nondecreasing sequence `z` of reals, every set
of positions `i` with `Ψ (z i) ≠ Ψ (z (i + 1))` has at most `T` elements. This is the discrete
form of having at most `T + 1` interval pieces. -/
def ChangesAtMost {β : Type*} (Ψ : ℝ → β) (T : ℕ) : Prop :=
  ∀ z : ℕ → ℝ, Monotone z → ∀ S : Finset ℕ, (∀ i ∈ S, Ψ (z i) ≠ Ψ (z (i + 1))) → S.card ≤ T

/-- `Φ` *has at most `M` pieces*: it is constant on the level sets of a monotone rank function
`π : ℝ → ℕ` with values below `M`. The level sets are intervals. -/
def PiecesAtMost {β : Type*} (Φ : ℝ → β) (M : ℕ) : Prop :=
  ∃ π : ℝ → ℕ, Monotone π ∧ (∀ t, π t < M) ∧ ∀ t t', π t = π t' → Φ t = Φ t'

/-- The real weighted sum `∑ i, w i * x i` of the bits of `x`, read as `0` and `1`. -/
def weightedSum (w : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i, w i * (x i).toNat

/-- A weighted real threshold straight-line program with `n` inputs and `s` gates. Gate `j`
reads every input and every earlier gate, with arbitrary real weights; depth and fan-out are
unrestricted. -/
structure Program (n s : ℕ) where
  /-- The weight of input `i` in gate `j` (`inputWeight j i`). -/
  inputWeight : Fin s → Fin n → ℝ
  /-- The weight of gate `k` in gate `j` (`gateWeight j k`); only the entries with `k < j` are
  read. -/
  gateWeight : Fin s → Fin s → ℝ
  /-- The bias of gate `j`. -/
  bias : Fin s → ℝ
  /-- The output gate. -/
  output : Fin s

namespace Program

variable {s : ℕ}

/-- The gate values when every gate in `fixed` takes the value given by `η`, and every other
gate `j` receives the real input contribution `z j` in place of its weighted input sum: such a
gate is `1` exactly when `z j + ∑_{k < j} gateWeight j k * (gate k) + bias j ≥ 0`. -/
noncomputable def evalFrom (C : Program n s) (fixed : Finset (Fin s)) (η : Fin s → Bool)
    (z : Fin s → ℝ) (j : Fin s) : Bool :=
  if j ∈ fixed then η j else
    decide (0 ≤ z j + (∑ k : Fin s,
      if _h : k < j then C.gateWeight j k * (C.evalFrom fixed η z k).toNat else 0) + C.bias j)
termination_by j

/-- The gate values of the program on the input `x`: gate `j` is `1` exactly when
`∑ i, inputWeight j i * x i + ∑_{k < j} gateWeight j k * (gate k) + bias j ≥ 0`. -/
noncomputable def eval (C : Program n s) (x : Fin n → Bool) : Fin s → Bool :=
  C.evalFrom ∅ (fun _ => false) (fun j => weightedSum (C.inputWeight j) x)

/-- The program computes `f` at its output gate. -/
def Computes (C : Program n s) (f : Cslib.BooleanFunction n) : Prop :=
  ∀ x, C.eval x C.output = f x

open scoped Classical in
/-- The input-reading gates: those with a nonzero input weight vector. -/
noncomputable def inputGates (C : Program n s) : Finset (Fin s) :=
  Finset.univ.filter fun j => C.inputWeight j ≠ 0

/-- A split of the gates into `B` consecutive runs, numbered by the monotone map `run`, such
that every gate of run `i` reads the inputs along the direction `dir i`: its input weight
vector is a real multiple of `dir i`. A gate that reads no input fits every direction. -/
structure DirectionRuns (C : Program n s) (B : ℕ) where
  /-- The run of each gate. -/
  run : Fin s → ℕ
  /-- Runs are consecutive in the gate order. -/
  monotone : Monotone run
  /-- There are at most `B` runs. -/
  run_lt : ∀ j, run j < B
  /-- The direction of each run. -/
  dir : ℕ → Fin n → ℝ
  /-- Every gate reads the inputs along the direction of its run. -/
  along : ∀ j, ∃ c : ℝ, C.inputWeight j = c • dir (run j)

open scoped Classical in
/-- The number of input-reading gates in run `i`. -/
noncomputable def DirectionRuns.size {C : Program n s} {B : ℕ} (R : C.DirectionRuns B)
    (i : ℕ) : ℕ :=
  (C.inputGates.filter fun j => R.run j = i).card

end Program

/-- The kind of a block in a block decomposition. -/
inductive BlockKind
  /-- A one-dimensional block whose value changes at most `T` times along its weighted sum. -/
  | oneDim (T : ℕ)
  /-- A summary block, depending on the first side of every split through at most `V`
  values. -/
  | summary (V : ℕ)

namespace BlockKind

/-- The capacity cost of a block: `4T` for a one-dimensional block with `T ≥ 1` changes, `1`
for one without changes, and `V` for a summary block. -/
def cost : BlockKind → ℕ
  | oneDim T => if T = 0 then 1 else 4 * T
  | summary V => V

/-- A step of kind `κ` from the history `prev` to the history `next`.

* One-dimensional with `T` changes: for some weight vector `w` and some `Φ`,
  `next x = Φ (prev x) ⟨w, x⟩`, where every `Φ η` changes at most `T` times.
* Summary with `V` values: for every split `U`, some `σ` on the first side with `V` values and
  some `Φ` satisfy `next (glue U p q) = Φ (prev (glue U p q)) (σ p) q`. -/
def Step {H : Type*} : BlockKind → ((Fin n → Bool) → H) → ((Fin n → Bool) → H) → Prop
  | oneDim T, prev, next => ∃ (w : Fin n → ℝ) (Φ : H → ℝ → H),
      (∀ η, ChangesAtMost (Φ η) T) ∧ ∀ x, next x = Φ (prev x) (weightedSum w x)
  | summary V, prev, next => ∀ U : Finset (Fin n), ∃ (σ : (U → Bool) → Fin V)
      (Φ : H → Fin V → (↥Uᶜ → Bool) → H),
      ∀ p q, next (glue U p q) = Φ (prev (glue U p q)) (σ p) q

end BlockKind

/-- A decomposition of `f` into blocks: histories `history 0, …, history length`, the first
constant, each obtained from the previous one by a step of the given kind, and `f` read off the
last history. -/
structure BlockDecomposition (f : Cslib.BooleanFunction n) (H : Type*) where
  /-- The number of blocks. -/
  length : ℕ
  /-- The kind of each block. -/
  kind : ℕ → BlockKind
  /-- The history after the first `i` blocks. -/
  history : ℕ → (Fin n → Bool) → H
  /-- The output read from the final history. -/
  output : H → Bool
  /-- Before any block, the history is constant. -/
  history_zero : ∀ x y, history 0 x = history 0 y
  /-- Each block is a step of its kind. -/
  step : ∀ i < length, (kind i).Step (history i) (history (i + 1))
  /-- The final history determines `f`. -/
  output_history : ∀ x, output (history length x) = f x

/-- The capacity cost of a block decomposition: the product of the costs of its blocks. -/
def BlockDecomposition.cost {f : Cslib.BooleanFunction n} {H : Type*}
    (D : BlockDecomposition f H) : ℕ :=
  ∏ i ∈ Finset.range D.length, (D.kind i).cost

end Algebraic.Threshold
