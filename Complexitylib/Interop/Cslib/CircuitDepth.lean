/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Cslib.Circuit.Defs
public import Complexitylib.Circuits.DepthClasses.Defs
import Complexitylib.Interop.Cslib.Circuit

/-!
# Depth of the CSLib circuit bridge

CSLib measures depth by `Program.wireDepths`: inputs have depth zero and every
gate, including negations and constants, adds one. Its circuit depth
`Cslib.Circuits.Circuit.depth` is the largest depth of a designated output
wire, so outputs are free. Our `Circuit.wireDepth` also gives inputs depth zero
and adds one per gate, while `Circuit.depth` charges one more layer for the
output gates.

The translation `Circuit.ofCslib` replaces each CSLib line by one gate reading
the same wires (or the first input, for constants), so it preserves every wire
depth exactly, and its output gates add exactly one layer.

The converse translation `Circuit.toCslib` is a dual-rail construction: CSLib
gates `0, …, N - 1` negate the inputs, each of our gates becomes a positive and
a negative rail (the negative one by De Morgan, from the complementary rails),
and each output gate becomes one CSLib gate. It has exactly `N + 2G + M` gates,
and every rail sits at most one layer above our wire, so depth grows by at most
one. The two directions pin the depth class `DEPTH` down in CSLib terms up to
an additive constant.

## Main results

- `Complexity.Circuit.wireDepth_ofCslib` — wire depths agree
- `Complexity.Circuit.depth_ofCslib` — `ofCslib` adds exactly one layer
- `Complexity.Circuit.eval_toCslib`, `Complexity.Circuit.depth_toCslib_le` — the
  dual-rail simulation is correct and adds at most one layer
- `Complexity.Circuit.exists_cslib_depth_le` — every fan-in-two AND/OR circuit
  has a CSLib circuit with `N + 2G + M` gates and depth at most one more
- `Complexity.exists_cslib_of_mem_DEPTH`, `Complexity.mem_DEPTH_of_cslib` —
  `DEPTH d` versus CSLib circuits of depth `d + 1`

## Supporting CSLib lemmas

- `Complexity.Program.depths_eq_lines_depth` — CSLib's depth equation, line by line
- `Complexity.Program.wireDepths_le` — bounding CSLib depth by a certificate
- `Complexity.Program.ofLines`, `Complexity.Program.lines_ofLines` — building a
  program from its lines
-/
public section

namespace Complexity

open Cslib.Circuits

/-- A max-fold from zero is bounded by `b` exactly when every term is. -/
private theorem foldl_max_le_iff {n : ℕ} (f : Fin n → ℕ) (b : ℕ) :
    Fin.foldl n (fun acc k => max acc (f k)) 0 ≤ b ↔ ∀ k, f k ≤ b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ_last, max_le_iff, ih (fun k => f k.castSucc)]
    constructor
    · rintro ⟨h1, h2⟩ k
      exact Fin.lastCases h2 h1 k
    · intro h
      exact ⟨fun k => h _, h _⟩

/-- Every term of a max-fold from zero is at most the fold. -/
private theorem le_foldl_max {n : ℕ} (f : Fin n → ℕ) (k : Fin n) :
    f k ≤ Fin.foldl n (fun acc k => max acc (f k)) 0 :=
  (foldl_max_le_iff f _).mp le_rfl k

/-- Adding one to every term of a nonempty max-fold adds one to the fold. -/
private theorem foldl_max_add_one {n : ℕ} [NeZero n] (f : Fin n → ℕ) :
    Fin.foldl n (fun acc k => max acc (f k + 1)) 0 =
      Fin.foldl n (fun acc k => max acc (f k)) 0 + 1 := by
  set L := Fin.foldl n (fun acc k => max acc (f k + 1)) 0
  have hL : ∀ k, f k + 1 ≤ L := le_foldl_max (fun k => f k + 1)
  have hpos : 1 ≤ L := le_trans (by omega) (hL 0)
  refine le_antisymm ((foldl_max_le_iff _ _).mpr fun k => ?_) ?_
  · have := le_foldl_max f k
    omega
  · have : Fin.foldl n (fun acc k => max acc (f k)) 0 ≤ L - 1 :=
      (foldl_max_le_iff f _).mpr fun k => by have := hL k; omega
    omega

variable {σ : Signature} {N g : ℕ}

/-- Widening a wire into a longer program keeps its CSLib depth. -/
theorem Program.wireDepths_gate_castSucc (p : Program σ N g) (line : Line σ N g)
    (w : Wire N g) : (p.gate line).wireDepths w.castSucc = p.wireDepths w := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) w
  · simp [Program.wireDepths, Fin.castSucc_castAdd]
  · simp [Program.wireDepths, Program.depths]

/-- Line `j` of a program has the CSLib depth of gate `j`. -/
theorem Program.depths_eq_lines_depth (p : Program σ N g) (j : Fin g) :
    p.depths j = (p.lines j).depth p.wireDepths := by
  induction p with
  | empty => exact j.elim0
  | @gate g p line ih =>
    have hmap (l : Line σ N g) :
        (l.mapWires Wire.Renaming.castSucc).depth (p.gate line).wireDepths =
          l.depth p.wireDepths := by
      simp only [Line.depth, Line.mapWires, Function.comp_apply, Wire.Renaming.castSucc_apply,
        Program.wireDepths_gate_castSucc]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [Program.lines_gate_last, hmap]
      simp only [Program.depths, Fin.lastCases_last]
      rfl
    · rw [Program.lines_gate_castSucc, hmap, ← ih]
      simp [Program.depths]

/-- The program whose line `j` is `F j`, a line reading only the inputs and the
`j` gates before it. -/
def Program.ofLines : (g : ℕ) → ((j : Fin g) → Line σ N j) → Program σ N g
  | 0, _ => .empty
  | g + 1, F => .gate (Program.ofLines g fun j => F j.castSucc) (F (Fin.last g))

/-- The lines of `Program.ofLines` are the given lines, widened. -/
theorem Program.lines_ofLines (g : ℕ) (F : (j : Fin g) → Line σ N j) (j : Fin g) :
    (Program.ofLines g F).lines j = (F j).mapWires (Fin.castLE (by omega)) := by
  induction g with
  | zero => exact j.elim0
  | succ g ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [Program.ofLines, Program.lines_gate_last]
      simp only [Line.mapWires]
      congr 1
      funext a
      apply Fin.ext
      simp
    · rw [Program.ofLines, Program.lines_gate_castSucc, ih]
      simp only [Line.mapWires]
      congr 1
      funext a
      apply Fin.ext
      simp

/-- A line's depth is monotone in the depths of the wires it reads. -/
theorem Line.depth_mono {g : ℕ} (l : Line σ N g) {d e : Wire N g → ℕ}
    (h : ∀ a, d (l.wires a) ≤ e (l.wires a)) : l.depth d ≤ l.depth e := by
  unfold Line.depth
  refine Nat.succ_le_succ ((foldl_max_le_iff _ _).mpr fun k => ?_)
  exact (h k).trans (le_foldl_max (fun k => e (l.wires k)) k)

/-- **Bounding CSLib depth by a line-wise certificate.** If `b` bounds every
line's depth at the line's own wire, it bounds every wire's depth. -/
theorem Program.wireDepths_le (p : Program σ N g) (b : Wire N g → ℕ)
    (hb : ∀ j, (p.lines j).depth b ≤ b (Fin.natAdd N j)) (w : Wire N g) :
    p.wireDepths w ≤ b w := by
  have hg : ∀ n (j : Fin g), j.val = n → p.depths j ≤ b (Fin.natAdd N j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro j hj
    rw [Program.depths_eq_lines_depth]
    refine le_trans (Line.depth_mono _ fun a => ?_) (hb j)
    have hlt := Program.lines_wires_lt p j a
    refine Fin.addCases (motive := fun w => w.val < N + j → p.wireDepths w ≤ b w)
      (fun i _ => by simp [Program.wireDepths]) (fun k hk => ?_) ((p.lines j).wires a) hlt
    rw [Program.wireDepths, Fin.addCases_right]
    exact ih k (by simp at hk; omega) k rfl
  refine Fin.addCases (fun i => ?_) (fun j => ?_) w
  · simp [Program.wireDepths]
  · rw [Program.wireDepths, Fin.addCases_right]
    exact hg _ j rfl

namespace Circuit

/-- The gate simulating a CSLib line has the line's depth, given matching depths
on the wires it reads and depth zero on the first input. -/
theorem ofCslibGate_depth [NeZero N] (l : Line Boolean.signature N g)
    (d e : Fin (N + g) → ℕ) (h0 : d firstWire = 0) (hl : ∀ a, d (l.wires a) = e (l.wires a)) :
    1 + Fin.foldl (ofCslibGate l).fanIn
        (fun acc k => max acc (d ((ofCslibGate l).inputs k))) 0 = l.depth e := by
  obtain ⟨op, w⟩ := l
  cases op <;> simp [ofCslibGate, Line.depth, Fin.foldl_succ, h0, hl, Nat.add_comm]

variable {M : ℕ} [NeZero N] [NeZero M]

/-- **Wire depths agree.** Every wire of the translation has the CSLib depth of
the same wire. -/
theorem wireDepth_ofCslib (c : Cslib.Circuits.Circuit Boolean.signature N g M)
    (w : Fin (N + g)) : (ofCslib c).wireDepth w = c.program.wireDepths w := by
  suffices h : ∀ n (w : Fin (N + g)), w.val = n →
      (ofCslib c).wireDepth w = c.program.wireDepths w from h _ w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw
  by_cases hlt : w.val < N
  · rw [wireDepth_of_lt _ _ hlt]
    have hw' : w = Fin.castAdd g ⟨w.val, hlt⟩ := Fin.ext rfl
    rw [hw', Program.wireDepths, Fin.addCases_left]
  · rw [wireDepth_of_not_lt _ _ hlt]
    have hw' : w = Fin.natAdd N ⟨w.val - N, by omega⟩ := Fin.ext (by simp; omega)
    conv_rhs => rw [hw', Program.wireDepths, Fin.addCases_right, Program.depths_eq_lines_depth]
    have h0 : (ofCslib c).wireDepth firstWire = 0 :=
      wireDepth_of_lt _ _ (Nat.pos_of_ne_zero (NeZero.ne N))
    exact ofCslibGate_depth _ _ _ h0 fun a =>
      ih _ (by
        have := Program.lines_wires_lt c.program ⟨w.val - N, by omega⟩ a
        simp only at this
        omega) _ rfl

/-- **Each output gets one extra layer.** Output gate `j` of the translation
sits one layer above CSLib's output wire `j`. -/
theorem outputDepth_ofCslib (c : Cslib.Circuits.Circuit Boolean.signature N g M) (j : Fin M) :
    (ofCslib c).outputDepth j = c.outputDepths j + 1 := by
  show 1 + Fin.foldl 2
      (fun acc k => max acc ((ofCslib c).wireDepth (![c.outputs j, c.outputs j] k))) 0 = _
  simp [Fin.foldl_succ, wireDepth_ofCslib, Cslib.Circuits.Circuit.outputDepths, Nat.add_comm]

/-- **Circuit depth grows by exactly one.** The translation of a CSLib circuit
has depth one more than the CSLib circuit, the extra layer being our output
gates. -/
theorem depth_ofCslib (c : Cslib.Circuits.Circuit Boolean.signature N g M) :
    (ofCslib c).depth = c.depth + 1 := by
  simp only [depth, outputDepth_ofCslib, Cslib.Circuits.Circuit.depth]
  exact foldl_max_add_one _


section DualRail

variable {N M G : ℕ}

/-- The wire of the dual-rail CSLib simulation carrying the literal `b ⊕ w`:
input `i` and its negation sit at wires `i` and `N + i`, and our gate wire
`w ≥ N` and its negation at wires `2w` and `2w + 1`. -/
def litIdx (N w : ℕ) (b : Bool) : ℕ :=
  if w < N then (if b then N + w else w) else 2 * w + (if b then 1 else 0)

/-- Literals of wires below `N + k` sit below wire `2N + 2k`. -/
theorem litIdx_lt {w k : ℕ} (b : Bool) (hw : w < N + k) : litIdx N w b < 2 * N + 2 * k := by
  unfold litIdx
  split_ifs <;> omega

/-- Whether a fan-in-two AND/OR operation is an AND. -/
def opIsAnd : AndOrOp → Bool
  | .and => true
  | .or => false

/-- The CSLib line computing `b ⊕ gt` from literals of the gate's inputs (by De
Morgan when `b` is true), in a program reading `N + j` wires. -/
def dualLine {W j : ℕ} (gt : Gate Basis.andOr2 W) (b : Bool)
    (h : ∀ k b', litIdx N (gt.inputs k) b' < N + j) : Line Boolean.signature N j :=
  let w : Fin 2 → Wire N j := fun a =>
    ⟨litIdx N (gt.inputs (Fin.cast (fanIn_andOr2 gt).symm a))
      (b.xor (gt.negated (Fin.cast (fanIn_andOr2 gt).symm a))), h _ _⟩
  if (opIsAnd gt.op).xor b then ⟨.and, w⟩ else ⟨.or, w⟩

/-- The line `dualLine gt b` computes `b ⊕ gt` from correct literal values. -/
theorem dualLine_eval {W j : ℕ} (gt : Gate Basis.andOr2 W) (b : Bool)
    (h : ∀ k b', litIdx N (gt.inputs k) b' < N + j) (v : Wire N j → Bool) (val : Fin W → Bool)
    (hv : ∀ (w : Fin W) (b' : Bool) (i : Wire N j), i.val = litIdx N w b' →
      v i = b'.xor (val w)) :
    Boolean.interpretation (dualLine gt b h).op (v ∘ (dualLine gt b h).wires) =
      b.xor (gt.eval val) := by
  obtain ⟨op, fanIn, hfan, inputs, negated⟩ := gt
  change fanIn = 2 at hfan
  subst hfan
  have h0 := hv (inputs 0) (b.xor (negated 0)) ⟨_, h 0 (b.xor (negated 0))⟩ rfl
  have h1 := hv (inputs 1) (b.xor (negated 1)) ⟨_, h 1 (b.xor (negated 1))⟩ rfl
  cases op <;> cases b <;>
    simp [dualLine, opIsAnd, Boolean.interpretation, Gate.eval, Basis.andOr2,
      AndOrOp.eval_two_and, AndOrOp.eval_two_or] at h0 h1 ⊢ <;>
    rw [h0, h1]

/-- The line `dualLine gt b` sits one layer above the literals it reads. -/
theorem dualLine_depth_le {W j : ℕ} (gt : Gate Basis.andOr2 W) (b : Bool)
    (h : ∀ k b', litIdx N (gt.inputs k) b' < N + j) (e : Wire N j → ℕ) (d : Fin W → ℕ)
    (he : ∀ (w : Fin W) (b' : Bool) (i : Wire N j), i.val = litIdx N w b' → e i ≤ d w + 1) :
    (dualLine gt b h).depth e ≤
      (1 + Fin.foldl gt.fanIn (fun acc k => max acc (d (gt.inputs k))) 0) + 1 := by
  obtain ⟨op, fanIn, hfan, inputs, negated⟩ := gt
  change fanIn = 2 at hfan
  subst hfan
  have h0 := he (inputs 0) (b.xor (negated 0)) ⟨_, h 0 (b.xor (negated 0))⟩ rfl
  have h1 := he (inputs 1) (b.xor (negated 1)) ⟨_, h 1 (b.xor (negated 1))⟩ rfl
  unfold dualLine
  split <;> simp [Line.depth, Fin.foldl_succ] at h0 h1 ⊢ <;> omega

variable [NeZero N] [NeZero M]

/-- Line `j` of the dual-rail simulation of `c`: first the negated inputs, then
each of our gates as a positive and a negative rail, then the output gates. -/
def dualRailLine (c : Circuit Basis.andOr2 N M G) (j : Fin (N + 2 * G + M)) :
    Line Boolean.signature N j :=
  if h1 : j.val < N then
    ⟨.not, fun _ => ⟨j.val, by have := Nat.pos_of_ne_zero (NeZero.ne N); omega⟩⟩
  else if h2 : j.val < N + 2 * G then
    dualLine (c.gates ⟨(j.val - N) / 2, by omega⟩) ((j.val - N) % 2 == 1) fun k b' => by
      have := litIdx_lt (N := N) b' (c.acyclic ⟨(j.val - N) / 2, by omega⟩ k)
      simp only at this
      omega
  else
    dualLine (c.outputs ⟨j.val - N - 2 * G, by omega⟩) false fun k b' => by
      have := litIdx_lt (N := N) b' ((c.outputs ⟨j.val - N - 2 * G, by omega⟩).inputs k).isLt
      omega

/-- The dual-rail CSLib simulation of `c`, with `N + 2G + M` gates. -/
def toCslib (c : Circuit Basis.andOr2 N M G) :
    Cslib.Circuits.Circuit Boolean.signature N (N + 2 * G + M) M where
  program := Program.ofLines _ c.dualRailLine
  outputs o := ⟨N + (N + 2 * G + o), by omega⟩

/-- The intended value of each gate of the dual-rail simulation. -/
def dualRailValue (c : Circuit Basis.andOr2 N M G) (x : BitString N)
    (j : Fin (N + 2 * G + M)) : Bool :=
  if h1 : j.val < N then !x ⟨j.val, h1⟩
  else if h2 : j.val < N + 2 * G then
    ((j.val - N) % 2 == 1).xor (c.wireValue x ⟨N + (j.val - N) / 2, by omega⟩)
  else c.eval x ⟨j.val - N - 2 * G, by omega⟩

/-- Each literal wire of the dual-rail simulation carries its literal. -/
theorem addCases_dualRailValue (c : Circuit Basis.andOr2 N M G) (x : BitString N)
    (w : Fin (N + G)) (b : Bool) (i : Fin (N + (N + 2 * G + M))) (hi : i.val = litIdx N w b) :
    Fin.addCases x (c.dualRailValue x) i = b.xor (c.wireValue x w) := by
  unfold litIdx at hi
  by_cases hw : w.val < N
  · rw [wireValue_of_lt _ _ _ hw]
    cases b
    · simp only [hw, ite_true, Bool.false_eq_true, ite_false] at hi
      have : i = Fin.castAdd _ ⟨w.val, hw⟩ := Fin.ext hi
      rw [this, Fin.addCases_left]
      simp
    · simp only [hw, ite_true] at hi
      have : i = Fin.natAdd N ⟨w.val, by omega⟩ := Fin.ext (by simp [hi])
      rw [this, Fin.addCases_right]
      simp [dualRailValue, hw]
  · have hwl := w.isLt
    cases b
    · simp only [hw, ite_false, Bool.false_eq_true] at hi
      have : i = Fin.natAdd N ⟨N + 2 * (w.val - N), by omega⟩ := Fin.ext (by simp; omega)
      rw [this, Fin.addCases_right]
      simp only [dualRailValue]
      split_ifs
      · omega
      · simp
        exact congrArg _ (Fin.ext (by simp; omega))
      · omega
    · simp only [hw, ite_false, ite_true] at hi
      have : i = Fin.natAdd N ⟨N + 2 * (w.val - N) + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [this, Fin.addCases_right]
      simp only [dualRailValue]
      split_ifs
      · omega
      · have h2 : (N + 2 * (w.val - N) + 1 - N) % 2 = 1 := by omega
        have h3 : (⟨N + (N + 2 * (w.val - N) + 1 - N) / 2, by omega⟩ : Fin (N + G)) = w :=
          Fin.ext (by simp; omega)
        simp [h2, h3]
      · omega

/-- Every gate of the dual-rail simulation computes its intended value. -/
theorem program_eval_toCslib (c : Circuit Basis.andOr2 N M G) (x : BitString N) :
    c.toCslib.program.eval Boolean.interpretation x = c.dualRailValue x := by
  refine (Program.eq_eval_of_forall_lines_eval _ _ _ _ fun j => ?_).symm
  rw [show c.toCslib.program = Program.ofLines _ c.dualRailLine from rfl, Program.lines_ofLines]
  have hv : ∀ (w : Fin (N + G)) (b' : Bool) (i : Wire N j), i.val = litIdx N w b' →
      (Fin.addCases x (c.dualRailValue x) ∘ Fin.castLE (by omega)) i =
        b'.xor (c.wireValue x w) :=
    fun w b' i hi => c.addCases_dualRailValue x w b' _ (by simpa using hi)
  show Boolean.interpretation (c.dualRailLine j).op
    ((Fin.addCases x (c.dualRailValue x) ∘ Fin.castLE (by omega)) ∘
      (c.dualRailLine j).wires) = _
  by_cases h1 : j.val < N
  · unfold dualRailLine
    rw [dite_eq_left_of_eq_true (eq_true h1)]
    simp only [Boolean.interpretation, Function.comp_apply]
    have hj : Fin.castLE (show N + j.val ≤ N + (N + 2 * G + M) by omega)
        ⟨j.val, by have := Nat.pos_of_ne_zero (NeZero.ne N); omega⟩ =
          Fin.castAdd _ ⟨j.val, h1⟩ := Fin.ext rfl
    rw [hj, Fin.addCases_left]
    unfold dualRailValue
    rw [dite_eq_left_of_eq_true (eq_true h1)]
  · by_cases h2 : j.val < N + 2 * G
    · unfold dualRailLine
      rw [dite_eq_right_of_eq_false (eq_false h1), dite_eq_left_of_eq_true (eq_true h2),
        dualLine_eval _ _ _ _ _ hv]
      unfold dualRailValue
      rw [dite_eq_right_of_eq_false (eq_false h1), dite_eq_left_of_eq_true (eq_true h2)]
      congr 1
      rw [wireValue_of_not_lt _ _ _ (by simp)]
      simp
    · unfold dualRailLine
      rw [dite_eq_right_of_eq_false (eq_false h1), dite_eq_right_of_eq_false (eq_false h2),
        dualLine_eval _ _ _ _ _ hv]
      unfold dualRailValue
      rw [dite_eq_right_of_eq_false (eq_false h1), dite_eq_right_of_eq_false (eq_false h2),
        Bool.false_xor]
      rfl

/-- **The dual-rail simulation computes what `c` computes.** -/
theorem eval_toCslib (c : Circuit Basis.andOr2 N M G) (x : BitString N) (o : Fin M) :
    c.toCslib.eval Boolean.interpretation x o = c.eval x o := by
  show (Fin.addCases x (c.toCslib.program.eval Boolean.interpretation x)
    (Fin.natAdd N (⟨N + 2 * G + o, by omega⟩ : Fin (N + 2 * G + M))) : Bool) = _
  rw [Fin.addCases_right, program_eval_toCslib]
  unfold dualRailValue
  rw [dite_eq_right_of_eq_false (eq_false (by simp; omega)),
    dite_eq_right_of_eq_false (eq_false (by simp))]
  exact congrArg _ (Fin.ext (by simp; omega))

/-- The depth certificate of the dual-rail simulation: inputs at depth zero,
negated inputs at one, both rails of our wire `w` at `wireDepth w + 1`, and
output `o` at `outputDepth o + 1`. -/
def dualRailDepth (c : Circuit Basis.andOr2 N M G) (i : Fin (N + (N + 2 * G + M))) : ℕ :=
  if h0 : i.val < N then 0
  else if h1 : i.val < 2 * N then 1
  else if h : i.val < 2 * N + 2 * G then c.wireDepth ⟨N + (i.val - 2 * N) / 2, by omega⟩ + 1
  else c.outputDepth ⟨i.val - 2 * N - 2 * G, by omega⟩ + 1

/-- Each literal wire of the dual-rail simulation is certified one layer above
its wire. -/
theorem dualRailDepth_le (c : Circuit Basis.andOr2 N M G) (w : Fin (N + G)) (b : Bool)
    (i : Fin (N + (N + 2 * G + M))) (hi : i.val = litIdx N w b) :
    c.dualRailDepth i ≤ c.wireDepth w + 1 := by
  unfold litIdx at hi
  unfold dualRailDepth
  have hwl := w.isLt
  by_cases hw : w.val < N
  · cases b <;> simp only [hw, ite_true, ite_false, Bool.false_eq_true] at hi <;> split_ifs <;>
      omega
  · simp only [hw, ite_false] at hi
    split_ifs with h1 h2 h3
    · omega
    · omega
    · have : (⟨N + (i.val - 2 * N) / 2, by omega⟩ : Fin (N + G)) = w := by
        apply Fin.ext
        simp only
        split at hi <;> omega
      rw [this]
    · split at hi <;> omega

/-- The depth of our gate wire `N + k` unfolds to one more than its inputs'. -/
theorem wireDepth_natAdd (c : Circuit Basis.andOr2 N M G) (k : Fin G) :
    c.wireDepth (Fin.natAdd N k) =
      1 + Fin.foldl (c.gates k).fanIn
        (fun acc a => max acc (c.wireDepth ((c.gates k).inputs a))) 0 := by
  rw [wireDepth_of_not_lt _ _ (by simp)]
  have hk : (⟨(Fin.natAdd N k).val - N, by simp⟩ : Fin G) = k := Fin.ext (by simp)
  rw [hk]

/-- Every wire of the dual-rail simulation meets its depth certificate. -/
theorem wireDepths_toCslib_le (c : Circuit Basis.andOr2 N M G)
    (i : Fin (N + (N + 2 * G + M))) :
    c.toCslib.program.wireDepths i ≤ c.dualRailDepth i := by
  refine Program.wireDepths_le _ _ (fun j => ?_) i
  rw [show c.toCslib.program = Program.ofLines _ c.dualRailLine from rfl, Program.lines_ofLines]
  show (c.dualRailLine j).depth
    (c.dualRailDepth ∘ Fin.castLE (show N + j.val ≤ N + (N + 2 * G + M) by omega)) ≤ _
  have he : ∀ (w : Fin (N + G)) (b' : Bool) (i : Wire N j), i.val = litIdx N w b' →
      (c.dualRailDepth ∘ Fin.castLE (show N + j.val ≤ N + (N + 2 * G + M) by omega)) i ≤
        c.wireDepth w + 1 :=
    fun w b' i hi => c.dualRailDepth_le w b' _ (by simpa using hi)
  by_cases h1 : j.val < N
  · unfold dualRailLine
    rw [dite_eq_left_of_eq_true (eq_true h1)]
    have h3 : N + j.val < 2 * N := by omega
    have h4 : ¬ N + j.val < N := by omega
    simp [Line.depth, dualRailDepth, h1, h3, h4, Fin.foldl_succ, Fin.foldl_zero]
  · by_cases h2 : j.val < N + 2 * G
    · unfold dualRailLine
      rw [dite_eq_right_of_eq_false (eq_false h1), dite_eq_left_of_eq_true (eq_true h2)]
      refine (dualLine_depth_le _ _ _ _ c.wireDepth he).trans (le_of_eq ?_)
      have hr : c.dualRailDepth (Fin.natAdd N j) =
          c.wireDepth (Fin.natAdd N (⟨(j.val - N) / 2, by omega⟩ : Fin G)) + 1 := by
        unfold dualRailDepth
        rw [dite_eq_right_of_eq_false (eq_false (by simp only [Fin.val_natAdd]; omega)),
          dite_eq_right_of_eq_false (eq_false (by simp only [Fin.val_natAdd]; omega)),
          dite_eq_left_of_eq_true (eq_true (by simp only [Fin.val_natAdd]; omega))]
        exact congrArg (· + 1) (congrArg _ (Fin.ext (by simp only [Fin.val_natAdd]; omega)))
      rw [hr, wireDepth_natAdd]
    · unfold dualRailLine
      rw [dite_eq_right_of_eq_false (eq_false h1), dite_eq_right_of_eq_false (eq_false h2)]
      refine (dualLine_depth_le _ _ _ _ c.wireDepth he).trans (le_of_eq ?_)
      unfold dualRailDepth
      rw [dite_eq_right_of_eq_false (eq_false (by simp only [Fin.val_natAdd]; omega)),
        dite_eq_right_of_eq_false (eq_false (by simp only [Fin.val_natAdd]; omega)),
        dite_eq_right_of_eq_false (eq_false (by simp only [Fin.val_natAdd]; omega))]
      show c.outputDepth ⟨j.val - N - 2 * G, by omega⟩ + 1 = _
      exact congrArg (· + 1) (congrArg _ (Fin.ext (by simp only [Fin.val_natAdd]; omega)))

/-- **The dual-rail simulation adds at most one layer.** Its depth is at most
one more than the depth of `c`. -/
theorem depth_toCslib_le (c : Circuit Basis.andOr2 N M G) :
    c.toCslib.depth ≤ c.depth + 1 := by
  refine (foldl_max_le_iff _ _).mpr fun o => (c.wireDepths_toCslib_le _).trans ?_
  have ho : c.dualRailDepth (c.toCslib.outputs o) = c.outputDepth o + 1 := by
    show c.dualRailDepth (Fin.natAdd N (⟨N + 2 * G + o, by omega⟩ : Fin (N + 2 * G + M))) = _
    unfold dualRailDepth
    rw [dite_eq_right_of_eq_false (eq_false (by simp only [Fin.val_natAdd]; omega)),
      dite_eq_right_of_eq_false (eq_false (by simp only [Fin.val_natAdd]; omega)),
      dite_eq_right_of_eq_false (eq_false (by simp only [Fin.val_natAdd]; omega))]
    exact congrArg (· + 1) (congrArg _ (Fin.ext (by simp only [Fin.val_natAdd]; omega)))
  rw [ho]
  exact Nat.add_le_add_right (le_foldl_max _ o) 1

end DualRail

section

variable {N M G : ℕ} [NeZero N] [NeZero M]

/-- **Our circuits run as CSLib's, with depth control.** A fan-in-two AND/OR
circuit with `G` internal gates and `M` outputs has a CSLib De Morgan circuit
with exactly `N + 2G + M` gates computing the same outputs, whose depth is at
most one more. -/
theorem exists_cslib_depth_le (c : Circuit Basis.andOr2 N M G) :
    ∃ c' : Cslib.Circuits.Circuit Boolean.signature N (N + 2 * G + M) M,
      (∀ x j, c'.eval Boolean.interpretation x j = c.eval x j) ∧ c'.depth ≤ c.depth + 1 :=
  ⟨c.toCslib, c.eval_toCslib, c.depth_toCslib_le⟩

end

end Circuit

section DepthClasses

/-- **`DEPTH d` in CSLib terms, forward.** A Boolean function family in
`DEPTH d` has, at every positive length `n + 1`, a CSLib De Morgan circuit
computing it with depth at most `d (n + 1) + 1`. -/
theorem exists_cslib_of_mem_DEPTH {d : ℕ → ℕ} {f : BoolFunFamily} (hf : f ∈ DEPTH d)
    (n : ℕ) : ∃ g, ∃ c : Cslib.Circuits.Circuit Boolean.signature (n + 1) g 1,
      c.Computes Boolean.interpretation (f (n + 1)) ∧ c.depth ≤ d (n + 1) + 1 := by
  obtain ⟨F, hF, hd⟩ := hf
  obtain ⟨c, hc, hdepth⟩ := Circuit.exists_cslib_depth_le (F.circuit (n + 1))
  refine ⟨_, c, fun x => ?_, hdepth.trans (Nat.add_le_add_right (hd (n + 1)) 1)⟩
  rw [hc, ← hF]
  rfl

/-- **`DEPTH` in CSLib terms, backward.** If every positive length `n` has a
CSLib De Morgan circuit computing `f n` with depth at most `d n`, then `f` is in
`DEPTH (d + 1)`. -/
theorem mem_DEPTH_of_cslib {d : ℕ → ℕ} {f : BoolFunFamily}
    (h : ∀ (n : ℕ) [NeZero n], ∃ g, ∃ c : Cslib.Circuits.Circuit Boolean.signature n g 1,
      c.Computes Boolean.interpretation (f n) ∧ c.depth ≤ d n) :
    f ∈ DEPTH (fun n => d n + 1) := by
  choose g c hc hd using h
  refine ⟨{ emptyOutput := f 0 Fin.elim0
            circuits := fun n _ => ⟨g n, Circuit.ofCslib (c n)⟩ }, ?_, ?_⟩
  · funext n x
    rcases n with _ | m
    · exact congrArg (f 0) (funext fun i => i.elim0)
    · show (Circuit.ofCslib (c (m + 1))).eval x 0 = f (m + 1) x
      rw [Circuit.eval_ofCslib]
      exact hc (m + 1) x
  · intro n
    rcases n with _ | m
    · exact Nat.zero_le _
    · show (Circuit.ofCslib (c (m + 1))).depth ≤ d (m + 1) + 1
      rw [Circuit.depth_ofCslib]
      exact Nat.add_le_add_right (hd (m + 1)) 1

end DepthClasses

end Complexity
