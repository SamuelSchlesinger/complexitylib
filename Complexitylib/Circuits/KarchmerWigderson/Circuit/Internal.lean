/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.Rounds
public import Complexitylib.Circuits.AndOrNot.Defs
public import Complexitylib.Circuits.Dependency.Defs
import Complexitylib.Algebraic.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.SuccPred

/-!
# A circuit gives a bounded-round general KW protocol

The standard Karchmer--Wigderson translation, as used in Section 1.1 of Oliver
Korten, *Top-Down Lower Bounds for All Depths*, ECCC TR26-221 (2026),
https://eccc.weizmann.ac.il/report/2026/221/.

Descend through a gate input selected by the appropriate player. Every gate
has fan-in at most the circuit's total input-wire count. Negated wires swap
the players without an extra message. Empty gates have constant value and
therefore an empty KW relation; an arbitrary coordinate is a valid answer.
-/

public section

namespace Complexity

theorem eval_and_true_internal (n : ℕ) (v : Fin n → Bool) :
    AndOrOp.eval .and n v = true ↔ ∀ i, v i = true := by
  induction n with
  | zero => simp [AndOrOp.eval, Fin.foldl_zero]
  | succ n ih =>
    rw [AndOrOp.eval, Fin.foldl_succ_last, Bool.and_eq_true, Fin.forall_fin_succ']
    exact and_congr (ih (fun i => v i.castSucc)) Iff.rfl

theorem eval_or_true_internal (n : ℕ) (v : Fin n → Bool) :
    AndOrOp.eval .or n v = true ↔ ∃ i, v i = true := by
  induction n with
  | zero => simp [AndOrOp.eval, Fin.foldl_zero]
  | succ n ih =>
    rw [AndOrOp.eval, Fin.foldl_succ_last, Bool.or_eq_true, Fin.exists_fin_succ']
    exact or_congr (ih (fun i => v i.castSucc)) Iff.rfl

namespace KarchmerWigderson.RoundProtocol

theorem exists_negated_internal {ι M : Type*} {d : ℕ} {P : RoundProtocol ι M d}
    {f : (ι → Bool) → Bool} (h : P.SolvesKW f) (b : Bool) :
    ∃ Q : RoundProtocol ι M d, Q.SolvesKW (fun x => b.xor (f x)) := by
  cases b
  · exact ⟨P, by simpa using h⟩
  · exact ⟨P.swapPlayers, by simpa using h.swapPlayers⟩

open scoped Classical

theorem exists_or_protocol_internal {ι : Type*} (i0 : ι) {W a d : ℕ} (ha : a ≤ W)
    (f : Fin a → (ι → Bool) → Bool)
    (child : Fin a → RoundProtocol ι (Fin W) d) (hchild : ∀ j, (child j).SolvesKW (f j)) :
    ∃ P : RoundProtocol ι (Fin W) (d + 1),
      P.SolvesKW (fun x => AndOrOp.eval .or a (fun j => f j x)) := by
  cases a with
  | zero =>
    exact ⟨.answer i0, by intro x y hx hy; simp [AndOrOp.eval, Fin.foldl_zero] at hy⟩
  | succ a =>
    let pick (x : ι → Bool) : Fin (a + 1) :=
      if h : ∃ j, f j x = true then Classical.choose h else ⟨0, by omega⟩
    let send (x : ι → Bool) : Fin W := Fin.castLE ha (pick x)
    let next (j : Fin W) : RoundProtocol ι (Fin W) d :=
      if h : j.val < a + 1 then child ⟨j.val, h⟩ else .answer i0
    refine ⟨.bob send next, ?_⟩
    intro x y hx hy
    dsimp only at hx hy
    have hy' := (eval_or_true_internal _ _).mp hy
    have hpick : f (pick y) y = true := by
      simp only [pick, dite_eq_left hy']
      exact Classical.choose_spec hy'
    have hx' : f (pick y) x = false := by
      cases he : f (pick y) x with
      | false => rfl
      | true =>
        have hh := (eval_or_true_internal (a + 1) (fun j => f j x)).mpr ⟨pick y, he⟩
        rw [hx] at hh
        contradiction
    have hh := hchild (pick y) x y hx' hpick
    simpa only [run, next, send, Fin.castLE, dite_eq_left (pick y).isLt] using hh

theorem exists_and_protocol_internal {ι : Type*} (i0 : ι) {W a d : ℕ} (ha : a ≤ W)
    (f : Fin a → (ι → Bool) → Bool)
    (child : Fin a → RoundProtocol ι (Fin W) d) (hchild : ∀ j, (child j).SolvesKW (f j)) :
    ∃ P : RoundProtocol ι (Fin W) (d + 1),
      P.SolvesKW (fun x => AndOrOp.eval .and a (fun j => f j x)) := by
  cases a with
  | zero =>
    exact ⟨.answer i0, by intro x y hx hy; simp [AndOrOp.eval, Fin.foldl_zero] at hx⟩
  | succ a =>
    let pick (x : ι → Bool) : Fin (a + 1) :=
      if h : ∃ j, f j x = false then Classical.choose h else ⟨0, by omega⟩
    let send (x : ι → Bool) : Fin W := Fin.castLE ha (pick x)
    let next (j : Fin W) : RoundProtocol ι (Fin W) d :=
      if h : j.val < a + 1 then child ⟨j.val, h⟩ else .answer i0
    refine ⟨.alice send next, ?_⟩
    intro x y hx hy
    dsimp only at hx hy
    have hx' : ∃ j, f j x = false := by
      by_contra hn
      have ht : ∀ j, f j x = true := by
        intro j
        cases he : f j x with
        | false => exact False.elim (hn ⟨j, he⟩)
        | true => rfl
      have hh := (eval_and_true_internal _ _).mpr ht
      rw [hx] at hh
      contradiction
    have hpick : f (pick x) x = false := by
      simp only [pick, dite_eq_left hx']
      exact Classical.choose_spec hx'
    have hh := hchild (pick x) x y hpick ((eval_and_true_internal _ _).mp hy (pick x))
    simpa only [run, next, send, Fin.castLE, dite_eq_left (pick x).isLt] using hh

theorem exists_gate_protocol_internal {ι : Type*} (i0 : ι) {W a d : ℕ} (ha : a ≤ W)
    (op : AndOrOp) (f : Fin a → (ι → Bool) → Bool)
    (h : ∀ j, ∃ P : RoundProtocol ι (Fin W) d, P.SolvesKW (f j)) :
    ∃ P : RoundProtocol ι (Fin W) (d + 1),
      P.SolvesKW (fun x => AndOrOp.eval op a (fun j => f j x)) := by
  choose child hchild using h
  cases op
  · exact exists_and_protocol_internal i0 ha f child hchild
  · exact exists_or_protocol_internal i0 ha f child hchild

theorem exists_coded_or_protocol_internal {ι α : Type*} (i0 : ι) {a d : ℕ}
    (code : Fin a → α) (F : α → (ι → Bool) → Bool)
    (child : α → RoundProtocol ι α d)
    (hchild : ∀ j, (child (code j)).SolvesKW (F (code j))) :
    ∃ P : RoundProtocol ι α (d + 1),
      P.SolvesKW (fun x => AndOrOp.eval .or a (fun j => F (code j) x)) := by
  cases a with
  | zero =>
    exact ⟨.answer i0, by intro x y hx hy; simp [AndOrOp.eval, Fin.foldl_zero] at hy⟩
  | succ a =>
    let pick (x : ι → Bool) : Fin (a + 1) :=
      if h : ∃ j, F (code j) x = true then Classical.choose h else ⟨0, by omega⟩
    let send (x : ι → Bool) : α := code (pick x)
    refine ⟨.bob send child, ?_⟩
    intro x y hx hy
    dsimp only at hx hy
    have hy' := (eval_or_true_internal _ _).mp hy
    have hpick : F (code (pick y)) y = true := by
      simp only [pick, dite_eq_left hy']
      exact Classical.choose_spec hy'
    have hx' : F (code (pick y)) x = false := by
      cases he : F (code (pick y)) x with
      | false => rfl
      | true =>
        have hh := (eval_or_true_internal (a + 1) (fun j => F (code j) x)).mpr ⟨pick y, he⟩
        rw [hx] at hh
        contradiction
    exact hchild (pick y) x y hx' hpick

theorem exists_coded_and_protocol_internal {ι α : Type*} (i0 : ι) {a d : ℕ}
    (code : Fin a → α) (F : α → (ι → Bool) → Bool)
    (child : α → RoundProtocol ι α d)
    (hchild : ∀ j, (child (code j)).SolvesKW (F (code j))) :
    ∃ P : RoundProtocol ι α (d + 1),
      P.SolvesKW (fun x => AndOrOp.eval .and a (fun j => F (code j) x)) := by
  cases a with
  | zero =>
    exact ⟨.answer i0, by intro x y hx hy; simp [AndOrOp.eval, Fin.foldl_zero] at hx⟩
  | succ a =>
    let pick (x : ι → Bool) : Fin (a + 1) :=
      if h : ∃ j, F (code j) x = false then Classical.choose h else ⟨0, by omega⟩
    let send (x : ι → Bool) : α := code (pick x)
    refine ⟨.alice send child, ?_⟩
    intro x y hx hy
    dsimp only at hx hy
    have hx' : ∃ j, F (code j) x = false := by
      by_contra hn
      have ht : ∀ j, F (code j) x = true := by
        intro j
        cases he : F (code j) x with
        | false => exact False.elim (hn ⟨j, he⟩)
        | true => rfl
      have hh := (eval_and_true_internal _ _).mpr ht
      rw [hx] at hh
      contradiction
    have hpick : F (code (pick x)) x = false := by
      simp only [pick, dite_eq_left hx']
      exact Classical.choose_spec hx'
    exact hchild (pick x) x y hpick ((eval_and_true_internal _ _).mp hy (pick x))

theorem exists_coded_gate_protocol_internal {ι α : Type*} (i0 : ι) {a d : ℕ}
    (op : AndOrOp) (code : Fin a → α) (F : α → (ι → Bool) → Bool)
    (h : ∀ j, ∃ P : RoundProtocol ι α d, P.SolvesKW (F (code j))) :
    ∃ P : RoundProtocol ι α (d + 1),
      P.SolvesKW (fun x => AndOrOp.eval op a (fun j => F (code j) x)) := by
  choose P hP using h
  let child (m : α) : RoundProtocol ι α d :=
    if hm : ∃ j, code j = m then P (Classical.choose hm) else .answer i0
  have hchild (j : Fin a) : (child (code j)).SolvesKW (F (code j)) := by
    have hm : ∃ j', code j' = code j := ⟨j, rfl⟩
    have hspec := hP (Classical.choose hm)
    rw [Classical.choose_spec hm] at hspec
    simpa only [child, dite_eq_left hm] using hspec
  cases op
  · exact exists_coded_and_protocol_internal i0 code F child hchild
  · exact exists_coded_or_protocol_internal i0 code F child hchild

end KarchmerWigderson.RoundProtocol
namespace Circuit

open KarchmerWigderson Finset
open scoped BigOperators Classical

variable {N M G : ℕ} [NeZero N] [NeZero M]

theorem gate_fanIn_le_total_internal (c : Circuit Basis.unboundedAndOr N M G) (i : Fin G) :
    (c.gates i).fanIn ≤ c.totalFanIn := by
  have h : (c.gates i).fanIn ≤ ∑ j, (c.gates j).fanIn :=
    single_le_sum (f := fun j => (c.gates j).fanIn) (fun j _ => Nat.zero_le _) (mem_univ i)
  unfold totalFanIn
  omega

theorem output_fanIn_le_total_internal (c : Circuit Basis.unboundedAndOr N M G) (i : Fin M) :
    (c.outputs i).fanIn ≤ c.totalFanIn := by
  have h : (c.outputs i).fanIn ≤ ∑ j, (c.outputs j).fanIn :=
    single_le_sum (f := fun j => (c.outputs j).fanIn) (fun j _ => Nat.zero_le _) (mem_univ i)
  unfold totalFanIn
  omega

theorem exists_input_protocol_internal (c : Circuit Basis.unboundedAndOr N M G) (d : ℕ)
    (w : Fin (N + G)) (hw : w.val < N) :
    ∃ P : RoundProtocol (Fin N) (Fin c.totalFanIn) d,
      P.SolvesKW (fun x => c.wireValue x w) := by
  refine ⟨.answer ⟨w.val, hw⟩, ?_⟩
  intro x y hx hy
  change c.wireValue x w = false at hx
  change c.wireValue y w = true at hy
  rw [c.wireValue_of_lt x w hw] at hx
  rw [c.wireValue_of_lt y w hw] at hy
  change x ⟨w.val, hw⟩ ≠ y ⟨w.val, hw⟩
  rw [hx, hy]
  decide

theorem exists_wire_protocol_internal (c : Circuit Basis.unboundedAndOr N M G) (d : ℕ)
    (w : Fin (N + G)) (hw : c.wireDepth w ≤ d) :
    ∃ P : RoundProtocol (Fin N) (Fin c.totalFanIn) d,
      P.SolvesKW (fun x => c.wireValue x w) := by
  induction d generalizing w with
  | zero =>
    by_cases hi : w.val < N
    · exact exists_input_protocol_internal c 0 w hi
    · rw [c.wireDepth_of_not_lt w hi] at hw
      omega
  | succ d ih =>
    by_cases hi : w.val < N
    · exact exists_input_protocol_internal c (d + 1) w hi
    let j : Fin G := ⟨w.val - N, by omega⟩
    let g := c.gates j
    rw [c.wireDepth_of_not_lt w hi] at hw
    change 1 + Fin.foldl g.fanIn (fun acc i => max acc (c.wireDepth (g.inputs i))) 0 ≤ d + 1 at hw
    have hchild (i : Fin g.fanIn) :
        ∃ P : RoundProtocol (Fin N) (Fin c.totalFanIn) d,
          P.SolvesKW (fun x => (g.negated i).xor (c.wireValue x (g.inputs i))) := by
      have hmax := Algebraic.Fin.le_foldl_max (fun i => c.wireDepth (g.inputs i)) 0 i
      obtain ⟨P, hP⟩ := ih (g.inputs i) (by omega)
      exact RoundProtocol.exists_negated_internal hP (g.negated i)
    obtain ⟨P, hP⟩ := RoundProtocol.exists_gate_protocol_internal (0 : Fin N)
      (gate_fanIn_le_total_internal c j) g.op
      (fun i x => (g.negated i).xor (c.wireValue x (g.inputs i))) hchild
    refine ⟨P, ?_⟩
    have he : (fun x => c.wireValue x w) =
        (fun x => AndOrOp.eval g.op g.fanIn
          (fun i => (g.negated i).xor (c.wireValue x (g.inputs i)))) := by
      funext x
      rw [c.wireValue_of_not_lt x w hi]
      rfl
    rw [he]
    exact hP

theorem exists_roundProtocol_internal (c : Circuit Basis.unboundedAndOr N M G) (d : ℕ)
    (hd : c.depth ≤ d) (j : Fin M) :
    ∃ P : RoundProtocol (Fin N) (Fin c.totalFanIn) d,
      P.SolvesKW (fun x => c.eval x j) := by
  have hdepth : c.outputDepth j ≤ d :=
    (Algebraic.Fin.le_foldl_max (fun j => c.outputDepth j) 0 j).trans hd
  let g := c.outputs j
  cases d with
  | zero =>
    change 1 + Fin.foldl g.fanIn (fun acc i => max acc (c.wireDepth (g.inputs i))) 0 ≤ 0 at hdepth
    omega
  | succ d =>
    change 1 + Fin.foldl g.fanIn (fun acc i => max acc (c.wireDepth (g.inputs i))) 0 ≤
      d + 1 at hdepth
    have hchild (i : Fin g.fanIn) :
        ∃ P : RoundProtocol (Fin N) (Fin c.totalFanIn) d,
          P.SolvesKW (fun x => (g.negated i).xor (c.wireValue x (g.inputs i))) := by
      have hmax := Algebraic.Fin.le_foldl_max (fun i => c.wireDepth (g.inputs i)) 0 i
      obtain ⟨P, hP⟩ := exists_wire_protocol_internal c d (g.inputs i) (by omega)
      exact RoundProtocol.exists_negated_internal hP (g.negated i)
    obtain ⟨P, hP⟩ := RoundProtocol.exists_gate_protocol_internal (0 : Fin N)
      (output_fanIn_le_total_internal c j) g.op
      (fun i x => (g.negated i).xor (c.wireValue x (g.inputs i))) hchild
    exact ⟨P, hP⟩

/-- Encode a wire and negation flag into `Fin (2 * (N + G))`. -/
private def codeOfWire (w : Fin (N + G)) (b : Bool) : Fin (2 * (N + G)) :=
  ⟨2 * w.val + b.toNat, by
    have : b.toNat < 2 := by cases b <;> decide
    omega⟩

/-- Decode the wire index from a wire-literal code. -/
private def wireOfCode (m : Fin (2 * (N + G))) : Fin (N + G) :=
  ⟨m.val / 2, by omega⟩

/-- Decode the negation flag from a wire-literal code. -/
private def negOfCode (m : Fin (2 * (N + G))) : Bool :=
  decide (m.val % 2 = 1)

omit [NeZero N] in
private theorem wireOfCode_codeOfWire (w : Fin (N + G)) (b : Bool) :
    wireOfCode (codeOfWire w b) = w := by
  ext
  dsimp [wireOfCode, codeOfWire]
  have : b.toNat < 2 := by cases b <;> decide
  omega

omit [NeZero N] in
private theorem negOfCode_codeOfWire (w : Fin (N + G)) (b : Bool) :
    negOfCode (codeOfWire w b) = b := by
  dsimp [negOfCode, codeOfWire]
  cases b <;> simp [Bool.toNat]

/-- Evaluate the wire literal represented by code `m`. -/
private def codeLiteral (c : Circuit Basis.unboundedAndOr N M G)
    (m : Fin (2 * (N + G))) (x : Fin N → Bool) : Bool :=
  (negOfCode m).xor (c.wireValue x (wireOfCode m))

@[simp] private theorem codeLiteral_codeOfWire (c : Circuit Basis.unboundedAndOr N M G)
    (w : Fin (N + G)) (b : Bool) :
    codeLiteral c (codeOfWire w b) = fun x => b.xor (c.wireValue x w) := by
  funext x
  simp [codeLiteral, wireOfCode_codeOfWire, negOfCode_codeOfWire]

@[simp] private theorem codeLiteral_codeOfWire_apply (c : Circuit Basis.unboundedAndOr N M G)
    (w : Fin (N + G)) (b : Bool) (x : Fin N → Bool) :
    codeLiteral c (codeOfWire w b) x = b.xor (c.wireValue x w) :=
  congrFun (codeLiteral_codeOfWire c w b) x

theorem exists_input_protocol_of_gates_internal (c : Circuit Basis.unboundedAndOr N M G) (d : ℕ)
    (w : Fin (N + G)) (hw : w.val < N) :
    ∃ P : RoundProtocol (Fin N) (Fin (2 * (N + G))) d,
      P.SolvesKW (fun x => c.wireValue x w) := by
  refine ⟨.answer ⟨w.val, hw⟩, ?_⟩
  intro x y hx hy
  change c.wireValue x w = false at hx
  change c.wireValue y w = true at hy
  rw [c.wireValue_of_lt x w hw] at hx
  rw [c.wireValue_of_lt y w hw] at hy
  change x ⟨w.val, hw⟩ ≠ y ⟨w.val, hw⟩
  rw [hx, hy]
  decide

/-- One gate layer of the gate-count translation: if every input wire of `g`
has a `d`-message protocol over wire-literal codes, so does the gate itself with
one more message. -/
private theorem exists_gate_protocol_of_gates (c : Circuit Basis.unboundedAndOr N M G) {d : ℕ}
    (g : Gate Basis.unboundedAndOr (N + G))
    (hwire : ∀ i, ∃ P : RoundProtocol (Fin N) (Fin (2 * (N + G))) d,
      P.SolvesKW (fun x => c.wireValue x (g.inputs i))) :
    ∃ P : RoundProtocol (Fin N) (Fin (2 * (N + G))) (d + 1),
      P.SolvesKW (fun x => AndOrOp.eval g.op g.fanIn
        (fun i => (g.negated i).xor (c.wireValue x (g.inputs i)))) := by
  let code (i : Fin g.fanIn) : Fin (2 * (N + G)) :=
    codeOfWire (g.inputs i) (g.negated i)
  have hchild (i : Fin g.fanIn) :
      ∃ P : RoundProtocol (Fin N) (Fin (2 * (N + G))) d,
        P.SolvesKW (codeLiteral c (code i)) := by
    obtain ⟨P, hP⟩ := hwire i
    simpa only [code, codeLiteral_codeOfWire] using
      RoundProtocol.exists_negated_internal hP (g.negated i)
  obtain ⟨P, hP⟩ := RoundProtocol.exists_coded_gate_protocol_internal (0 : Fin N)
    g.op code (codeLiteral c) hchild
  exact ⟨P, by simpa only [code, codeLiteral_codeOfWire_apply] using hP⟩

theorem exists_wire_protocol_of_gates_internal (c : Circuit Basis.unboundedAndOr N M G) (d : ℕ)
    (w : Fin (N + G)) (hw : c.wireDepth w ≤ d) :
    ∃ P : RoundProtocol (Fin N) (Fin (2 * (N + G))) d,
      P.SolvesKW (fun x => c.wireValue x w) := by
  induction d generalizing w with
  | zero =>
    by_cases hi : w.val < N
    · exact exists_input_protocol_of_gates_internal c 0 w hi
    · rw [c.wireDepth_of_not_lt w hi] at hw
      omega
  | succ d ih =>
    by_cases hi : w.val < N
    · exact exists_input_protocol_of_gates_internal c (d + 1) w hi
    let j : Fin G := ⟨w.val - N, by omega⟩
    let g := c.gates j
    rw [c.wireDepth_of_not_lt w hi] at hw
    change 1 + Fin.foldl g.fanIn (fun acc i => max acc (c.wireDepth (g.inputs i))) 0 ≤ d + 1 at hw
    obtain ⟨P, hP⟩ := exists_gate_protocol_of_gates c g fun i =>
      ih (g.inputs i)
        (by have := Algebraic.Fin.le_foldl_max (fun i => c.wireDepth (g.inputs i)) 0 i; omega)
    refine ⟨P, ?_⟩
    have he : (fun x => c.wireValue x w) =
        (fun x => AndOrOp.eval g.op g.fanIn
          (fun i => (g.negated i).xor (c.wireValue x (g.inputs i)))) := by
      funext x
      rw [c.wireValue_of_not_lt x w hi]
      rfl
    rw [he]
    exact hP

theorem exists_roundProtocol_of_gates_internal (c : Circuit Basis.unboundedAndOr N M G) (d : ℕ)
    (hd : c.depth ≤ d) (j : Fin M) :
    ∃ P : RoundProtocol (Fin N) (Fin (2 * (N + G))) d,
      P.SolvesKW (fun x => c.eval x j) := by
  have hdepth : c.outputDepth j ≤ d :=
    (Algebraic.Fin.le_foldl_max (fun j => c.outputDepth j) 0 j).trans hd
  let g := c.outputs j
  cases d with
  | zero =>
    change 1 + Fin.foldl g.fanIn (fun acc i => max acc (c.wireDepth (g.inputs i))) 0 ≤ 0 at hdepth
    omega
  | succ d =>
    change 1 + Fin.foldl g.fanIn (fun acc i => max acc (c.wireDepth (g.inputs i))) 0 ≤
      d + 1 at hdepth
    obtain ⟨P, hP⟩ := exists_gate_protocol_of_gates c g fun i =>
      exists_wire_protocol_of_gates_internal c d (g.inputs i)
        (by have := Algebraic.Fin.le_foldl_max (fun i => c.wireDepth (g.inputs i)) 0 i; omega)
    exact ⟨P, hP⟩

end Circuit
end Complexity
