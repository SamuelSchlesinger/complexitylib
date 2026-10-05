/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Cslib.Circuit.Upstream
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Ledgers for gates of unbounded fan-in

The frontier method charges each gate for its fan-in, so it cannot afford gates of unbounded
fan-in. A few of them can nevertheless be absorbed, when they *aggregate*: when their outputs are
determined by a product, in a commutative monoid, of contributions of the wires.

Mark a set of gates as *special*. A *ledger* for them in a commutative monoid `M`
(`Frontier.Ledger`) assigns to each wire and each of its values a *contribution* in `M`, and
reads off the value of every special gate from the product of the contributions of all wires.
The defining identity holds for *every* assignment of values to the wires, not only for runs of
the circuit. For example, `k` gates computing AND, OR, parity, or counts modulo `m` of their
arguments have a ledger in a product of `k` small monoids.

**Guess and check.** Replace each special gate by a constant *placeholder* (`Frontier.erase`):
the result has fan-in bounded by that of the other gates. To run it, guess the final product
`m ∈ M` and let each placeholder read its value from `m` (`Frontier.Ledger.run`). The guess is
*consistent* when the run reproduces it: when the product of the contributions of the run is `m`.

* A consistent guess yields the true run (`Frontier.Ledger.run_eq_trace`): the placeholders
  hold the values that the special gates would compute from the run.
* The product of the contributions of the true run is a consistent guess
  (`Frontier.Ledger.run_total_trace`).

So a circuit with special gates is an ordinary circuit, of bounded fan-in, together with one
global register in `M`: the guess, checked against an accumulated product. A sweep carries the
guess and the product accumulated so far in its messages, at a cost of `2 log |M|`.

## Main definitions

* `Frontier.guessSignature σ`: the signature `σ` with a placeholder constant for every natural.
* `Frontier.erase special p`: the program `p` with its special gates replaced by placeholders.
* `Frontier.Ledger p I special M`: a ledger for the special gates of `p` in `M`.

## Main results

* `Frontier.Ledger.run_eq_trace`, `Frontier.Ledger.run_total_trace`: guess and check.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits

universe v

variable {σ : Signature.{v}} {n s : ℕ} {U : Type*}

/-- The signature `σ` with a *placeholder* constant for every natural number. -/
abbrev guessSignature (σ : Signature.{v}) : Signature.{v} where
  Op := σ.Op ⊕ ℕ
  Arity := Sum.elim σ.Arity fun _ => 0

/-- The interpretation `I`, with the placeholder `k` holding the value `γ k`. -/
def guessInterpretation (I : Interpretation σ U) (γ : ℕ → U) :
    Interpretation (guessSignature σ) U
  | .inl o, x => I o x
  | .inr k, _ => γ k

/-- The line of the placeholder for gate `g`. -/
def placeholderLine (g : ℕ) {n s : ℕ} : Line (guessSignature σ) n s :=
  ⟨.inr g, Fin.elim0⟩

/-- An ordinary line, over the signature with placeholders. -/
def liftLine {n s : ℕ} (line : Line σ n s) : Line (guessSignature σ) n s :=
  ⟨.inl line.op, line.wires⟩

open Classical in
/-- **Erasing the special gates.** The gate numbered `g` becomes the placeholder `g` when
`special g`, and is unchanged otherwise. -/
noncomputable def erase (special : ℕ → Prop) : {s : ℕ} → Program σ n s →
    Program (guessSignature σ) n s
  | _, .empty => .empty
  | _, @Program.gate _ _ s p line =>
    (erase special p).gate (if special s then placeholderLine s else liftLine line)

open Classical in
theorem erase_gate (special : ℕ → Prop) (p : Program σ n s) (line : Line σ n s) :
    erase special (p.gate line) =
      (erase special p).gate (if special s then placeholderLine s else liftLine line) :=
  rfl

theorem placeholderLine_mapWires {n s n' s' : ℕ} (g : ℕ) (f : Wire n s → Wire n' s') :
    (placeholderLine (σ := σ) g).mapWires f = placeholderLine g := by
  simp only [placeholderLine, Line.mapWires]
  congr 1
  funext a
  exact (show Fin 0 from a).elim0

theorem liftLine_mapWires {n s n' s' : ℕ} (line : Line σ n s) (f : Wire n s → Wire n' s') :
    (liftLine line).mapWires f = liftLine (line.mapWires f) :=
  rfl

open Classical in
/-- The lines of an erased program. -/
theorem lines_erase (special : ℕ → Prop) (p : Program σ n s) (g : Fin s) :
    (erase special p).lines g =
      if special g then placeholderLine g else liftLine (p.lines g) := by
  induction p with
  | empty => exact g.elim0
  | @gate s p line ih =>
    refine Fin.lastCases ?_ (fun g => ?_) g
    · rw [erase_gate, Program.lines_gate_last, Program.lines_gate_last, Fin.val_last]
      split_ifs <;> simp [placeholderLine_mapWires, liftLine_mapWires]
    · rw [erase_gate, Program.lines_gate_castSucc, Program.lines_gate_castSucc, ih,
        Fin.val_castSucc]
      split_ifs <;> simp [placeholderLine_mapWires, liftLine_mapWires]

theorem lines_erase_of_special {special : ℕ → Prop} (p : Program σ n s) {g : Fin s}
    (hg : special g) : (erase special p).lines g = placeholderLine g := by
  classical
  simp [lines_erase, hg]

theorem lines_erase_of_not_special {special : ℕ → Prop} (p : Program σ n s) {g : Fin s}
    (hg : ¬ special g) : (erase special p).lines g = liftLine (p.lines g) := by
  classical
  simp [lines_erase, hg]

/-- Erasing the special gates leaves the fan-in of the others. -/
theorem fanInAtMost_erase (special : ℕ → Prop) (p : Program σ n s) {r : ℕ}
    (h : ∀ g : Fin s, ¬ special g → σ.Arity (p.lines g).op ≤ r) :
    (erase special p).FanInAtMost r := by
  induction p with
  | empty => trivial
  | @gate s p line ih =>
    refine ⟨ih fun g hg => ?_, ?_⟩
    · have := h g.castSucc (by simpa using hg)
      simpa using this
    · split_ifs with hs
      · exact Nat.zero_le _
      · have := h (Fin.last s) (by simpa using hs)
        simpa [liftLine] using this

/-- A *ledger* for the special gates of a program, in a commutative monoid `M`: a contribution
of each wire for each of its values, and a readout of the value of each special gate from the
product of all contributions. The identity holds for every assignment of values to the wires. -/
structure Ledger (p : Program σ n s) (I : Interpretation σ U) (special : ℕ → Prop) (M : Type*)
    [CommMonoid M] where
  /-- The contribution of a wire carrying a value. -/
  contribution : Wire n s → U → M
  /-- The value of each special gate, read off the product of the contributions. -/
  readout : M → ℕ → U
  /-- The readout of a special gate is the gate applied to the values of its arguments. -/
  readout_prod : ∀ (v : Wire n s → U) (g : Fin s), special g →
    readout (∏ w, contribution w (v w)) g = I (p.lines g).op fun a => v ((p.lines g).wires a)

namespace Ledger

variable {p : Program σ n s} {I : Interpretation σ U} {special : ℕ → Prop} {M : Type*}
  [CommMonoid M] (L : Ledger p I special M)

/-- The product of the contributions of an assignment of values to the wires. -/
def total (v : Wire n s → U) : M :=
  ∏ w, L.contribution w (v w)

/-- The run of the erased program, with the placeholders reading their values from the guess
`m`. -/
noncomputable def run (m : M) (x : Fin n → U) : Wire n s → U :=
  (erase special p).trace (guessInterpretation I (L.readout m)) x

/-- A trace is determined by its values at the gates. -/
private theorem elim_trace_gate {σ' : Signature} (q : Program σ' n s) (J : Interpretation σ' U)
    (x : Fin n → U) : Wire.elim x (fun g => q.trace J x (.gate g)) = q.trace J x := by
  funext w
  cases w <;> rfl

private theorem elim_run_gate (m : M) (x : Fin n → U) :
    Wire.elim x (fun g => L.run m x (.gate g)) = L.run m x :=
  elim_trace_gate _ _ x

/-- The value of a special gate in the run with guess `m` is its readout. -/
theorem run_gate_of_special (m : M) (x : Fin n → U) {g : Fin s} (hg : special g) :
    L.run m x (.gate g) = L.readout m g := by
  rw [run, Program.trace_gate, lines_erase_of_special p hg]
  rfl

/-- The value of an ordinary gate in the run with guess `m` is the gate applied to its
arguments. -/
theorem run_gate_of_not_special (m : M) (x : Fin n → U) {g : Fin s} (hg : ¬ special g) :
    L.run m x (.gate g) = I (p.lines g).op fun a => L.run m x ((p.lines g).wires a) := by
  rw [run, Program.trace_gate, lines_erase_of_not_special p hg]
  rfl

/-- **Guess and check, soundness.** If the run with guess `m` reproduces `m`, it is the true
run. -/
theorem run_eq_trace {m : M} {x : Fin n → U} (h : L.total (L.run m x) = m) :
    L.run m x = p.trace I x := by
  have hgates : (fun g => L.run m x (.gate g)) = p.eval I x := by
    refine p.eq_eval_of_forall_lines_eval I x _ fun g => ?_
    simp only [Line.eval, Function.comp_def]
    rw [L.elim_run_gate]
    by_cases hg : special g
    · have := L.readout_prod (L.run m x) g hg
      rw [← total, h] at this
      exact ((L.run_gate_of_special m x hg).trans this).symm
    · exact (L.run_gate_of_not_special m x hg).symm
  rw [← L.elim_run_gate, hgates]
  rfl

/-- **Guess and check, completeness.** The product of the contributions of the true run is a
guess whose run is the true run. -/
theorem run_total_trace (x : Fin n → U) : L.run (L.total (p.trace I x)) x = p.trace I x := by
  have hgates : (fun g => p.trace I x (.gate g)) =
      (erase special p).eval (guessInterpretation I (L.readout (L.total (p.trace I x)))) x := by
    refine (erase special p).eq_eval_of_forall_lines_eval _ x _ fun g => ?_
    simp only [Line.eval, Function.comp_def]
    rw [elim_trace_gate (q := p) I x]
    by_cases hg : special g
    · rw [lines_erase_of_special p hg]
      simp only [placeholderLine, guessInterpretation]
      rw [total, L.readout_prod _ g hg]
      exact (p.trace_gate I x g).symm
    · rw [lines_erase_of_not_special p hg]
      simp only [liftLine, guessInterpretation]
      exact (p.trace_gate I x g).symm
  change Wire.elim x ((erase special p).eval _ x) = _
  rw [← hgates, elim_trace_gate]

/-- A guessed ledger is consistent exactly when it is the ledger of the unique true run.
This is the uniqueness needed when summing counts over ledger guesses. -/
theorem total_run_eq_iff (m : M) (x : Fin n → U) :
    L.total (L.run m x) = m ↔ m = L.total (p.trace I x) := by
  constructor
  · intro h
    rw [L.run_eq_trace h] at h
    exact h.symm
  · rintro rfl
    rw [L.run_total_trace]

end Ledger

end Complexity.Frontier
