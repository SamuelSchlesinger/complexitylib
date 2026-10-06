/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Circuit
public import Complexitylib.Algebraic.LowerBound.Nechiporuk.Subfunctions

/-!
# Definitions for programs with shared gates over the full binary basis

This file holds the definitions behind the bounded-sharing Nechiporuk bounds, so that both the
proof internals (`Complexitylib.Algebraic.LowerBound.Nechiporuk.Sharing.Internal`) and the surface
statements (`Complexitylib.Algebraic.LowerBound.Nechiporuk.Sharing`) can refer to them:

- leaf and gate counts of full-binary-basis formulas (`Binary.Formula.gates`, `occ`,
  `inputLeaves`, `sharedLeaves`, `inputLeavesIn`);
- programs with shared gates (`Nechiporuk.SharedProgram`), their semantics and size measures, and
  the per-block measures `SharedProgram.activeShared` and `SharedProgram.activeSharedLeaves`, which
  advance a block through each shared gate with `SharedProgram.stepBlock`;
- the circuit-side sharing measures `sharedFanOut`, `activeSharedGateCount`,
  `activeSharedFanOut`, and `gateBlockSpan`, where a gate is *active* on a block `Y` when its
  syntactic input cone contains a coordinate of `Y` (`gateActive`).
-/

@[expose] public section

namespace Algebraic

namespace Binary
namespace Formula

variable {N : Nat}

/-- The number of binary gates in a formula. -/
def gates : Formula N → Nat
  | var _ => 0
  | const _ => 0
  | gate _ left right => left.gates + right.gates + 1

/-- The number of variable leaves with index `v`. -/
def occ (v : Nat) : Formula N → Nat
  | var i => if i.val = v then 1 else 0
  | const _ => 0
  | gate _ l r => l.occ v + r.occ v

/-- The number of variable leaves on the primary input variables `0, …, m - 1`. -/
def inputLeaves : Formula N → Nat → Nat
  | var i, m => if i.val < m then 1 else 0
  | const _, _ => 0
  | gate _ l r, m => l.inputLeaves m + r.inputLeaves m

/-- The number of variable leaves on the shared variables from `m` on. -/
def sharedLeaves : Formula N → Nat → Nat
  | var i, m => if m ≤ i.val then 1 else 0
  | const _, _ => 0
  | gate _ l r, m => l.sharedLeaves m + r.sharedLeaves m

/-- The number of variable leaves on variables below `n` that belong to `Y`. -/
def inputLeavesIn {n : Nat} (Y : Finset (Fin n)) : Formula N → Nat
  | var i => if h : i.val < n then if ⟨i.val, h⟩ ∈ Y then 1 else 0 else 0
  | const _ => 0
  | gate _ l r => l.inputLeavesIn Y + r.inputLeavesIn Y

end Formula
end Binary

namespace Nechiporuk

open scoped Classical
open Binary Cutwidth

/-- A program on `n` inputs with `k` shared gates over the full binary basis: `k + 1` binary
formulas, where each formula reads the primary inputs and the values of the earlier shared
formulas. -/
inductive SharedProgram : Nat → Nat → Type
  /-- Return a binary formula of the current variables. -/
  | output {n : Nat} (F : Formula n) : SharedProgram n 0
  /-- Compute a shared binary formula and continue with its value as a new last variable. -/
  | share {n k : Nat} (G : Formula n) (P : SharedProgram (n + 1) k) : SharedProgram n (k + 1)

namespace SharedProgram

variable {n N k : Nat}

/-- Evaluate a binary program with shared gates. -/
def eval : {n k : Nat} → SharedProgram n k → (Fin n → Bool) → Bool
  | _, _, output F, x => F.eval x
  | _, _, share G P, x => P.eval (Fin.snoc x (G.eval x))

/-- A program that only returns `F` evaluates as `F`. -/
@[simp] theorem eval_output (F : Formula n) (x : Fin n → Bool) :
    (output F).eval x = F.eval x := rfl

/-- A shared gate evaluates `G` and appends its value as the last variable. -/
@[simp] theorem eval_share (G : Formula n) (P : SharedProgram (n + 1) k) (x : Fin n → Bool) :
    (share G P).eval x = P.eval (Fin.snoc x (G.eval x)) := rfl

/-- A program computes `f` when it agrees with `f` on every input. -/
def Computes (P : SharedProgram n k) (f : Cslib.BooleanFunction n) : Prop :=
  ∀ x, P.eval x = f x

/-- A program computing `f` has evaluation function `f`. -/
theorem Computes.eval_eq {P : SharedProgram n k} {f : Cslib.BooleanFunction n} (h : P.Computes f) :
    P.eval = f :=
  funext h

/-- The number of binary gates, summed over the formulas of the program. -/
def gates : {n k : Nat} → SharedProgram n k → Nat
  | _, _, output F => F.gates
  | _, _, share G P => G.gates + P.gates

/-- The gates of an output-only program are those of its formula. -/
@[simp] theorem gates_output (F : Formula n) : (output F).gates = F.gates := rfl

/-- The gates of `share G P` are those of `G` plus those of `P`. -/
@[simp] theorem gates_share (G : Formula n) (P : SharedProgram (n + 1) k) :
    (share G P).gates = G.gates + P.gates := rfl

/-- The number of variable leaves on the variables `0, …, m - 1`, summed over the formulas. -/
def inputLeaves : {N k : Nat} → SharedProgram N k → Nat → Nat
  | _, _, output F, m => F.inputLeaves m
  | _, _, share G P, m => G.inputLeaves m + P.inputLeaves m

/-- The number of variable leaves on the variables from `m` on, summed over the formulas. -/
def sharedLeaves : {N k : Nat} → SharedProgram N k → Nat → Nat
  | _, _, output F, m => F.sharedLeaves m
  | _, _, share G P, m => G.sharedLeaves m + P.sharedLeaves m

/-- The number of variable leaves on variables below `n` that lie in `Y`, summed over the
formulas. -/
def inputLeavesIn {n : Nat} (Y : Finset (Fin n)) : {N k : Nat} → SharedProgram N k → Nat
  | _, _, output F => F.inputLeavesIn Y
  | _, _, share G P => G.inputLeavesIn Y + P.inputLeavesIn Y

/-- The number of variable leaves with index `v`, summed over the formulas of the program. -/
def occ (v : Nat) : {N k : Nat} → SharedProgram N k → Nat
  | _, _, output F => F.occ v
  | _, _, share G P => G.occ v + P.occ v

/-- Occurrences in an output-only program are those of its formula. -/
@[simp] theorem occ_output (v : Nat) (F : Formula N) : (output F).occ v = F.occ v := rfl

/-- Occurrences in `share G P` are those of `G` plus those of `P`. -/
@[simp] theorem occ_share (v : Nat) (G : Formula N) (P : SharedProgram (N + 1) k) :
    (share G P).occ v = G.occ v + P.occ v := rfl

/-- Embed a block `Y ⊆ Fin N` into `Fin (N + 1)` without including `Fin.last N`. -/
def castBlock {N : Nat} (Y : Finset (Fin N)) : Finset (Fin (N + 1)) :=
  Y.map Fin.castSuccEmb

/-- Extend a block `Y ⊆ Fin N` to `Fin (N + 1)` by including the new shared variable `Fin.last N`.
-/
def snocBlock {N : Nat} (Y : Finset (Fin N)) : Finset (Fin (N + 1)) :=
  insert (Fin.last N) (Y.map Fin.castSuccEmb)

/-- Advance a block across `share G P`: include `Fin.last N` iff `G` has a leaf in `Y`. -/
def stepBlock {N : Nat} (G : Formula N) (Y : Finset (Fin N)) : Finset (Fin (N + 1)) :=
  if G.leavesIn Y = 0 then castBlock Y else snocBlock Y

/-- The block leaf count of a program on `Y` when every shared variable is unconditionally added
to the block. -/
def leavesIn : {N k : Nat} → SharedProgram N k → Finset (Fin N) → Nat
  | _, _, output F, Y => F.leavesIn Y
  | _, _, share G P, Y => G.leavesIn Y + P.leavesIn (snocBlock Y)

/-- The number of shared gates of `P` that are active on `Y` (have at least one leaf in the
current active block). -/
def activeShared : {N k : Nat} → SharedProgram N k → Finset (Fin N) → Nat
  | _, _, output _, _ => 0
  | _, _, share G P, Y =>
      (if G.leavesIn Y = 0 then 0 else 1) + P.activeShared (stepBlock G Y)

/-- The active leaf count of `P` on `Y`, advancing the block via `stepBlock` at each shared gate.
-/
def activeLeavesIn : {N k : Nat} → SharedProgram N k → Finset (Fin N) → Nat
  | _, _, output F, Y => F.leavesIn Y
  | _, _, share G P, Y => G.leavesIn Y + P.activeLeavesIn (stepBlock G Y)

/-- The number of shared-variable leaves of `P` that read shared gates active on `Y`. -/
def activeSharedLeaves : {N k : Nat} → SharedProgram N k → Finset (Fin N) → Nat
  | _, _, output _, _ => 0
  | N, _, share G P, Y =>
      (if G.leavesIn Y = 0 then 0 else P.occ N) + P.activeSharedLeaves (stepBlock G Y)

end SharedProgram

/-! ### Sharing measures of binary circuits -/

section BinaryCircuits

variable {σ : Signature} {n m t : Nat}

/-- The total fan-out of all shared gates (gates of fan-out at least two) of a circuit. -/
def sharedFanOut (c : Circuit σ n m) : Nat :=
  ∑ g ∈ Finset.univ.filter (fun g => 2 ≤ KW.gateFanOut c g), KW.gateFanOut c g

/-- Whether gate `g` of `p` has at least one input from `Y` in its syntactic cone. -/
def gateActive (Y : Finset (Fin n)) : {t : Nat} → Program σ n t → Fin t → Bool
  | _, .empty => Fin.elim0
  | _, .gate p line =>
    Fin.lastCases
      (decide (∃ a,
        (match line.wires a with
         | .input i => decide (i ∈ Y)
         | .gate g => gateActive Y p g) = true))
      (gateActive Y p)

/-- Whether wire `w` of `p` has at least one input from `Y` in its syntactic cone. -/
def wireActive (Y : Finset (Fin n)) {t : Nat} (p : Program σ n t) : Wire n t → Bool
  | .input i => decide (i ∈ Y)
  | .gate g => gateActive Y p g

/-- The number of shared gates of `c` whose syntactic cone intersects `Y`. -/
def activeSharedGateCount (c : Circuit σ n m) (Y : Finset (Fin n)) : Nat :=
  (Finset.univ.filter fun g => 2 ≤ KW.gateFanOut c g ∧ gateActive Y c.program g = true).card

/-- The total fan-out of the shared gates of `c` whose syntactic cone intersects `Y`. -/
def activeSharedFanOut (c : Circuit σ n m) (Y : Finset (Fin n)) : Nat :=
  ∑ g ∈ Finset.univ.filter (fun g => 2 ≤ KW.gateFanOut c g ∧ gateActive Y c.program g = true),
    KW.gateFanOut c g

/-- The number of blocks in `Y : Fin B → Finset (Fin n)` on which gate `g` of `p` is active. -/
def gateBlockSpan {B : Nat} (Y : Fin B → Finset (Fin n)) (p : Program σ n t) (g : Fin t) : Nat :=
  (Finset.univ.filter fun i : Fin B => gateActive (Y i) p g = true).card

end BinaryCircuits

end Nechiporuk
end Algebraic
