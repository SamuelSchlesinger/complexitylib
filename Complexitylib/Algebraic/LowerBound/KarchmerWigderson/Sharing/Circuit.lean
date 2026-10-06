/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing
public import Complexitylib.Algebraic.Basis.DeMorgan
public import Complexitylib.Algebraic.Semantics
public import Complexitylib.Cslib.Circuit.Wire

/-!
# From De Morgan circuits to programs with shared gates

The fan-out of a gate of a circuit is the number of argument slots of gates that read it plus
the number of designated outputs equal to it (`gateFanOut`), and `sharedGateCount` counts the
gates of fan-out at least two. Every single-output circuit over the De Morgan basis computing
`f` yields a `SharedProgram` computing `f` with at most `sharedGateCount c` shared gates and at
most as many AND and OR gates as the circuit (`exists_sharedProgram_of_circuit`); NOT,
identity, and constant gates are free, as in `DeMorgan.binaryCost`.

The program is built from the last gate down. Its variables are all wires of the circuit, so
the initial program outputs the literal of the output wire. A gate of fan-out at least two
becomes a shared gate computing its formula, and its wire is then exactly the new shared
variable (`SharedProgram.share`). Any other gate is substituted into the program
(`SharedProgram.substVar`); since its variable occurs at most once, this adds the gate's own
cost and keeps every earlier gate occurring at most as often as its fan-out.

Consequently Khrapchenko's bound with shared gates holds for the library's De Morgan circuits:
a circuit computing the parity of `n ≥ 1` bits in which at most `k` gates have fan-out at least
two has `n² ≤ (k + 1) · (cost + k + 1)`, where `cost` counts the AND and OR gates
(`parity_sq_le_cost`). It has at least `C · n` AND and OR gates when `(k + 1) · (C + 1) ≤ n`
(`mul_le_cost_of_parity`), and a family of such circuits with `k(n) = o(n)` gates of fan-out at
least two has superlinear cost (`isLittleO_cost_of_parity`).
-/

@[expose] public section

namespace Algebraic
namespace KW

/-! ### Fan-out of circuit gates -/

section FanOut

variable {σ : Signature} {n m : Nat}

/-- The number of arguments of a gate that are equal to gate `g`. -/
def argUses {t : Nat} (line : Line σ n t) (g : Fin t) : Nat :=
  (Finset.univ.filter fun a => line.wires a = Wire.gate g).card

/-- The number of argument slots of the program's gates that read gate `g`. The last gate is
read by no gate of the program; an earlier gate is read by the gates before the last one and
by the arguments of the last gate that are equal to it. -/
def slotUses : {t : Nat} → Program σ n t → Fin t → Nat
  | _, .empty => Fin.elim0
  | _, .gate p line => Fin.lastCases 0 fun g => slotUses p g + argUses line g

/-- The fan-out of gate `g` of a circuit: the number of argument slots of gates that read `g`
plus the number of designated outputs equal to `g`. -/
def gateFanOut (c : Circuit σ n m) (g : Fin c.size) : Nat :=
  slotUses c.program g + (Finset.univ.filter fun o => c.outputs o = Wire.gate g).card

/-- The number of gates of a circuit whose fan-out is at least two. -/
def sharedGateCount (c : Circuit σ n m) : Nat :=
  (Finset.univ.filter fun g => 2 ≤ gateFanOut c g).card

@[simp] theorem slotUses_gate_last {t : Nat} (p : Program σ n t) (line : Line σ n t) :
    slotUses (p.gate line) (Fin.last t) = 0 := by
  simp [slotUses]

@[simp] theorem slotUses_gate_castSucc {t : Nat} (p : Program σ n t) (line : Line σ n t)
    (g : Fin t) : slotUses (p.gate line) g.castSucc = slotUses p g + argUses line g := by
  simp [slotUses]

/-- The number of gates of `p` whose fan-out is at least two when, besides the gates of `p`,
gate `g` is read `u g` more times. -/
def sharedCount {t : Nat} (p : Program σ n t) (u : Fin t → Nat) : Nat :=
  (Finset.univ.filter fun g => 2 ≤ slotUses p g + u g).card

theorem sharedGateCount_eq (c : Circuit σ n m) :
    sharedGateCount c = sharedCount c.program
      fun g => (Finset.univ.filter fun o => c.outputs o = Wire.gate g).card := rfl

end FanOut

/-! ### Occurrences and substitution of a variable -/

namespace Formula

variable {N M : Nat}

/-- The number of literal leaves on the variable with index `v`. -/
def occ (v : Nat) : Formula N → Nat
  | lit i _ => if i.val = v then 1 else 0
  | const _ => 0
  | and l r => l.occ v + r.occ v
  | or l r => l.occ v + r.occ v

@[simp] theorem occ_neg (v : Nat) : ∀ F : Formula N, F.neg.occ v = F.occ v
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by simp [neg, occ, occ_neg v l, occ_neg v r]
  | or l r => by simp [neg, occ, occ_neg v l, occ_neg v r]

@[simp] theorem occ_mapIndex_castLE (v : Nat) (h : N ≤ M) :
    ∀ F : Formula N, (F.mapIndex (Fin.castLE h)).occ v = F.occ v
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by simp [mapIndex, occ, occ_mapIndex_castLE v h l, occ_mapIndex_castLE v h r]
  | or l r => by simp [mapIndex, occ, occ_mapIndex_castLE v h l, occ_mapIndex_castLE v h r]

/-- The substitution behind `SharedProgram.substVar`: the variable `N` becomes `φ`, the
variables below `N` are kept, and those above `N` move down by one. -/
def substVarMap (φ : Formula N) (d : Nat) (i : Fin (N + 1 + d)) : Formula (N + d) :=
  if h : i.val < N then lit ⟨i.val, by omega⟩ true
  else if h' : i.val = N then φ.mapIndex (Fin.castLE (by omega))
  else lit ⟨i.val - 1, by omega⟩ true

/-- Insert the value `b` at position `N` of `y`, moving the later entries up by one. -/
def insertVal {d : Nat} (y : Fin (N + d) → Bool) (b : Bool) : Fin (N + 1 + d) → Bool :=
  fun i => if h : i.val < N then y ⟨i.val, by omega⟩
    else if h' : i.val = N then b else y ⟨i.val - 1, by omega⟩

theorem gates_subst_substVarMap (φ : Formula N) (d : Nat) :
    ∀ F : Formula (N + 1 + d), (F.subst (substVarMap φ d)).gates = F.gates + F.occ N * φ.gates
  | lit i b => by
    have key : (substVarMap φ d i).gates = (if i.val = N then 1 else 0) * φ.gates := by
      unfold substVarMap
      split_ifs <;> first | omega | simp [gates]
    cases b <;> simp [subst, gates, occ, key]
  | const _ => by simp [subst, gates, occ]
  | and l r => by
    simp only [subst, gates, occ, gates_subst_substVarMap φ d l, gates_subst_substVarMap φ d r]
    ring
  | or l r => by
    simp only [subst, gates, occ, gates_subst_substVarMap φ d l, gates_subst_substVarMap φ d r]
    ring

theorem occ_subst_substVarMap (φ : Formula N) (d : Nat) {w : Nat} (hw : w < N) :
    ∀ F : Formula (N + 1 + d),
      (F.subst (substVarMap φ d)).occ w = F.occ w + F.occ N * φ.occ w
  | lit i b => by
    have key : (substVarMap φ d i).occ w =
        (if i.val = w then 1 else 0) + (if i.val = N then 1 else 0) * φ.occ w := by
      unfold substVarMap
      split_ifs <;> simp [occ] <;> omega
    cases b <;> simp [subst, occ, key]
  | const _ => by simp [subst, occ]
  | and l r => by
    simp only [subst, occ, occ_subst_substVarMap φ d hw l, occ_subst_substVarMap φ d hw r]
    ring
  | or l r => by
    simp only [subst, occ, occ_subst_substVarMap φ d hw l, occ_subst_substVarMap φ d hw r]
    ring

theorem eval_subst_substVarMap (φ : Formula N) (d : Nat) (F : Formula (N + 1 + d))
    (y : Fin (N + d) → Bool) :
    (F.subst (substVarMap φ d)).eval y =
      F.eval (insertVal y (φ.eval fun j => y (Fin.castLE (by omega) j))) := by
  rw [eval_subst]
  congr 1
  funext i
  unfold substVarMap insertVal
  split_ifs <;> simp [Function.comp_def]

/-- `Fin.snoc` on Boolean vectors, entry by entry. -/
theorem snoc_apply {m : Nat} (y : Fin m → Bool) (g : Bool) (i : Fin (m + 1)) :
    Fin.snoc (α := fun _ => Bool) y g i = if h : i.val < m then y ⟨i.val, h⟩ else g := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

theorem insertVal_zero (y : Fin N → Bool) (b : Bool) :
    insertVal (d := 0) y b = Fin.snoc y b := by
  funext i
  rw [snoc_apply (m := N)]
  unfold insertVal
  split_ifs <;> first | rfl | omega

theorem insertVal_snoc {d : Nat} (y : Fin (N + d) → Bool) (g b : Bool) :
    insertVal (d := d + 1) (Fin.snoc y g) b = Fin.snoc (insertVal y b) g := by
  funext i
  simp only [insertVal, snoc_apply, Nat.add_eq]
  split_ifs <;> first | rfl | omega

end Formula

namespace SharedProgram

variable {N : Nat}

/-- The number of literal leaves on the variable with index `v`, summed over the formulas. -/
def occ (v : Nat) : {N k : Nat} → SharedProgram N k → Nat
  | _, _, output F => F.occ v
  | _, _, share G P => G.occ v + P.occ v

@[simp] theorem occ_output (v : Nat) (F : Formula N) : (output F).occ v = F.occ v := rfl

@[simp] theorem occ_share {k : Nat} (v : Nat) (G : Formula N) (P : SharedProgram (N + 1) k) :
    (share G P).occ v = G.occ v + P.occ v := rfl

@[simp] theorem gates_output (F : Formula N) : (output F).gates = F.gates := rfl

@[simp] theorem gates_share {k : Nat} (G : Formula N) (P : SharedProgram (N + 1) k) :
    (share G P).gates = G.gates + P.gates := rfl

/-- Substitute the formula `φ` for the variable `N` of a program reading `N + 1 + d`
variables, the last `d` of them shared values: the variables above `N` move down by one, and
the program then reads `φ` wherever it read variable `N`. -/
def substVar (φ : Formula N) : {d k : Nat} → SharedProgram (N + 1 + d) k → SharedProgram (N + d) k
  | d, _, output F => output (F.subst (Formula.substVarMap φ d))
  | d, _, share G P => share (G.subst (Formula.substVarMap φ d)) (substVar φ (d := d + 1) P)

theorem eval_substVar (φ : Formula N) : ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k)
    (y : Fin (N + d) → Bool),
    (substVar φ P).eval y =
      P.eval (Formula.insertVal y (φ.eval fun j => y (Fin.castLE (by omega) j)))
  | d, _, output F, y => by
    rw [substVar, eval_output, Formula.eval_subst_substVarMap, eval_output]
  | d, _, share G P, y => by
    rw [substVar, eval_share, eval_share, eval_substVar φ (d := d + 1) P,
      Formula.eval_subst_substVarMap]
    congr 1
    have hφ : (φ.eval fun j => Fin.snoc (α := fun _ => Bool) y
        (G.eval (Formula.insertVal y (φ.eval fun j => y (Fin.castLE (by omega) j))))
          (Fin.castLE (by omega) j)) = φ.eval fun j => y (Fin.castLE (by omega) j) := by
      congr 1
      funext j
      rw [Formula.snoc_apply (m := N + d)]
      simp only [Fin.val_castLE]
      split_ifs with h
      · rfl
      · omega
    rw [hφ, Formula.insertVal_snoc]

theorem gates_substVar (φ : Formula N) : ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k),
    (substVar φ P).gates = P.gates + P.occ N * φ.gates
  | d, _, output F => by
    rw [substVar]
    simp only [gates, occ, Formula.gates_subst_substVarMap]
  | d, _, share G P => by
    rw [substVar]
    simp only [gates, occ, Formula.gates_subst_substVarMap, gates_substVar φ (d := d + 1) P]
    ring

theorem occ_substVar (φ : Formula N) {w : Nat} (hw : w < N) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k),
      (substVar φ P).occ w = P.occ w + P.occ N * φ.occ w
  | d, _, output F => by
    rw [substVar]
    simp only [occ, Formula.occ_subst_substVarMap φ d hw]
  | d, _, share G P => by
    rw [substVar]
    simp only [occ, Formula.occ_subst_substVarMap φ d hw, occ_substVar φ hw (d := d + 1) P]
    ring

end SharedProgram

/-! ### De Morgan gates as formulas -/

section DeMorganGates

variable {n t : Nat}

/-- The formula of one De Morgan gate over the earlier wires, numbered by `Wire.index`. -/
def lineFormula : Line DeMorgan.signature n t → Formula (n + t)
  | ⟨.false, _⟩ => .const false
  | ⟨.true, _⟩ => .const true
  | ⟨.id, w⟩ => .lit (w ⟨0, by decide⟩).index true
  | ⟨.not, w⟩ => .lit (w ⟨0, by decide⟩).index false
  | ⟨.and, w⟩ => .and (.lit (w ⟨0, by decide⟩).index true) (.lit (w ⟨1, by decide⟩).index true)
  | ⟨.or, w⟩ => .or (.lit (w ⟨0, by decide⟩).index true) (.lit (w ⟨1, by decide⟩).index true)

/-- The values of the inputs and gates of a De Morgan program, numbered by `Wire.index`. -/
def wireValues (p : Program DeMorgan.signature n t) (x : Fin n → Bool) : Fin (n + t) → Bool :=
  Fin.append x (p.eval DeMorgan.interpretation x)

theorem append_index (x : Fin n → Bool) (vals : Fin t → Bool) (w : Wire n t) :
    Fin.append x vals w.index = Wire.elim x vals w := by
  cases w <;> simp [Fin.append_left, Fin.append_right]

theorem eval_lineFormula (line : Line DeMorgan.signature n t) (x : Fin n → Bool)
    (vals : Fin t → Bool) :
    (lineFormula line).eval (Fin.append x vals) = line.eval DeMorgan.interpretation x vals := by
  obtain ⟨op, w⟩ := line
  cases op <;> simp [lineFormula, Line.eval, DeMorgan.interpretation, append_index] <;> rfl

theorem gates_lineFormula (line : Line DeMorgan.signature n t) :
    (lineFormula line).gates = DeMorgan.binaryCost line.op := by
  obtain ⟨op, w⟩ := line
  cases op <;> rfl

theorem index_val_eq_iff (w : Wire n t) (g : Fin t) :
    w.index.val = n + g.val ↔ w = Wire.gate g := by
  cases w with
  | input i => simp; omega
  | gate g' => simp [Fin.ext_iff]

theorem occ_lineFormula_le (line : Line DeMorgan.signature n t) (g : Fin t) :
    (lineFormula line).occ (n + g.val) ≤ argUses line g := by
  obtain ⟨op, w⟩ := line
  rw [argUses, Finset.card_filter]
  cases op with
  | false => simp [lineFormula, Formula.occ]
  | true => simp [lineFormula, Formula.occ]
  | id =>
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨0, by decide⟩ : Fin (DeMorgan.arity .id))))
    simp only [lineFormula, Formula.occ, index_val_eq_iff]
    split_ifs <;> simp_all
  | not =>
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨0, by decide⟩ : Fin (DeMorgan.arity .not))))
    simp only [lineFormula, Formula.occ, index_val_eq_iff]
    split_ifs <;> simp_all
  | and =>
    have hne : (⟨0, by decide⟩ : Fin (DeMorgan.arity .and)) ≠ ⟨1, by decide⟩ := by decide
    refine le_trans ?_ (Finset.sum_le_sum_of_subset (Finset.subset_univ {⟨0, by decide⟩,
      (⟨1, by decide⟩ : Fin (DeMorgan.arity .and))}))
    rw [Finset.sum_pair hne]
    simp only [lineFormula, Formula.occ, index_val_eq_iff]
    split_ifs <;> simp_all
  | or =>
    have hne : (⟨0, by decide⟩ : Fin (DeMorgan.arity .or)) ≠ ⟨1, by decide⟩ := by decide
    refine le_trans ?_ (Finset.sum_le_sum_of_subset (Finset.subset_univ {⟨0, by decide⟩,
      (⟨1, by decide⟩ : Fin (DeMorgan.arity .or))}))
    rw [Finset.sum_pair hne]
    simp only [lineFormula, Formula.occ, index_val_eq_iff]
    split_ifs <;> simp_all

theorem eval_gate (p : Program DeMorgan.signature n t) (line : Line DeMorgan.signature n t)
    (x : Fin n → Bool) :
    (p.gate line).eval DeMorgan.interpretation x =
      Fin.snoc (p.eval DeMorgan.interpretation x)
        (line.eval DeMorgan.interpretation x (p.eval DeMorgan.interpretation x)) := by
  funext g
  refine Fin.lastCases ?_ (fun g => ?_) g
  · rw [Program.eval_gate_last, Fin.snoc_last]
  · rw [Program.eval_gate_castSucc, Fin.snoc_castSucc]

theorem wireValues_gate (p : Program DeMorgan.signature n t) (line : Line DeMorgan.signature n t)
    (x : Fin n → Bool) :
    wireValues (p.gate line) x =
      Fin.snoc (wireValues p x) ((lineFormula line).eval (wireValues p x)) := by
  rw [wireValues, eval_gate, Fin.append_snoc, wireValues, eval_lineFormula]

theorem wireValues_empty (x : Fin n → Bool) : wireValues (.empty : Program _ n 0) x = x := by
  funext i
  change Fin.append x Fin.elim0 i = x i
  rw [Fin.append_elim0]
  rfl

end DeMorganGates

/-! ### From circuits to programs -/

theorem sharedCount_gate {σ : Signature} {n t : Nat} (p : Program σ n t) (line : Line σ n t)
    (u : Fin (t + 1) → Nat) :
    sharedCount (p.gate line) u = (if 2 ≤ u (Fin.last t) then 1 else 0) +
      sharedCount p fun g => u g.castSucc + argUses line g := by
  rw [sharedCount, sharedCount, Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc,
    add_comm]
  simp only [slotUses_gate_last, slotUses_gate_castSucc, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs <;> omega

/-- Build a program from the last gate of a De Morgan program down. `Q` reads all wires of
`p`, gate `g` occurring at most `u g` times; a gate of total fan-out `slotUses p g + u g` at
least two becomes a shared gate and any other gate is substituted. -/
theorem exists_sharedProgram_of_program {n : Nat} (f : Cslib.BooleanFunction n) :
    ∀ {t : Nat} (p : Program DeMorgan.signature n t) (u : Fin t → Nat) {j : Nat}
      (Q : SharedProgram (n + t) j),
      (∀ x, Q.eval (wireValues p x) = f x) → (∀ g : Fin t, Q.occ (n + g.val) ≤ u g) →
      ∃ k, ∃ P : SharedProgram n k,
        k ≤ j + sharedCount p u ∧ P.Computes f ∧ P.gates ≤ Q.gates + p.cost DeMorgan.binaryCost
  | _, .empty, u, j, Q, hQ, _ =>
    ⟨j, Q, by simp, fun x => by simpa [wireValues_empty] using hQ x, by simp⟩
  | _, .gate (gateCount := t) p line, u, j, Q, hQ, hocc => by
    have hφocc := occ_lineFormula_le line
    have hφgates := gates_lineFormula line
    have hcount := sharedCount_gate p line u
    have hcost : (p.gate line).cost DeMorgan.binaryCost =
        p.cost DeMorgan.binaryCost + DeMorgan.binaryCost line.op := Program.cost_gate _ _ _
    have hlast : Q.occ (n + t) ≤ u (Fin.last t) := hocc (Fin.last t)
    by_cases hL : 2 ≤ u (Fin.last t)
    · obtain ⟨k, P, hk, hP, hgates⟩ := exists_sharedProgram_of_program f p
        (fun g => u g.castSucc + argUses line g) (SharedProgram.share (lineFormula line) Q)
        (fun x => by
          rw [SharedProgram.eval_share, ← wireValues_gate]
          exact hQ x)
        (fun g => by
          have h₁ : Q.occ (n + g.val) ≤ u g.castSucc := hocc g.castSucc
          have h₂ := hφocc g
          rw [SharedProgram.occ_share]
          omega)
      refine ⟨k, P, ?_, hP, ?_⟩
      · rw [hcount, ite_eq_left hL]
        omega
      · rw [SharedProgram.gates_share] at hgates
        omega
    · have hL₁ : Q.occ (n + t) ≤ 1 := by omega
      obtain ⟨k, P, hk, hP, hgates⟩ := exists_sharedProgram_of_program f p
        (fun g => u g.castSucc + argUses line g)
        (SharedProgram.substVar (lineFormula line) (d := 0) Q)
        (fun x => by
          rw [SharedProgram.eval_substVar, Formula.insertVal_zero]
          change Q.eval (Fin.snoc (wireValues p x) ((lineFormula line).eval (wireValues p x))) = _
          rw [← wireValues_gate]
          exact hQ x)
        (fun g => by
          rw [SharedProgram.occ_substVar _ (by omega)]
          have h₁ : Q.occ (n + g.val) ≤ u g.castSucc := hocc g.castSucc
          have h₂ := hφocc g
          have h₃ : Q.occ (n + t) * (lineFormula line).occ (n + g.val) ≤ argUses line g :=
            le_trans ((Nat.mul_le_mul_right _ hL₁).trans_eq (one_mul _)) h₂
          omega)
      refine ⟨k, P, ?_, hP, ?_⟩
      · rw [hcount, ite_eq_right hL]
        omega
      · rw [SharedProgram.gates_substVar] at hgates
        have h₃ : Q.occ (n + t) * (lineFormula line).gates ≤ DeMorgan.binaryCost line.op := by
          rw [hφgates]
          exact (Nat.mul_le_mul_right _ hL₁).trans_eq (one_mul _)
        omega

/-- **De Morgan circuits as programs with shared gates.** A single-output circuit over the
De Morgan basis computing `f` yields a program computing `f` with at most as many shared gates
as the circuit has gates of fan-out at least two, and at most as many AND and OR gates as the
circuit. -/
theorem exists_sharedProgram_of_circuit {n : Nat} (c : Circuit DeMorgan.signature n 1)
    {f : Cslib.BooleanFunction n} (hc : c.ComputesWith DeMorgan.interpretation fun x _ => f x) :
    ∃ k, ∃ P : SharedProgram n k,
      k ≤ sharedGateCount c ∧ P.Computes f ∧ P.gates ≤ c.cost DeMorgan.binaryCost := by
  obtain ⟨k, P, hk, hP, hgates⟩ := exists_sharedProgram_of_program f c.program
    (fun g => (Finset.univ.filter fun o => c.outputs o = Wire.gate g).card) (j := 0)
    (SharedProgram.output (.lit (c.outputs 0).index true))
    (fun x => by
      have := congrFun (hc x) 0
      simp only [Circuit.eval, Function.comp_apply, Program.trace] at this
      simp [wireValues, append_index, this])
    (fun g => by
      simp only [SharedProgram.occ, Formula.occ]
      split_ifs with h
      · exact Finset.card_pos.mpr ⟨0, by simpa using (index_val_eq_iff _ g).mp h⟩
      · exact Nat.zero_le _)
  refine ⟨k, P, by rw [sharedGateCount_eq]; simpa using hk, hP, ?_⟩
  simpa [Formula.gates, Circuit.cost] using hgates

/-! ### Parity -/

/-- **Parity in De Morgan circuits with few shared gates.** If a De Morgan circuit computes the
parity of `n ≥ 1` bits and at most `k` of its gates have fan-out at least two, then
`n² ≤ (k + 1) · (cost + k + 1)`, where `cost` counts its AND and OR gates; so it has at least
`n² / (k + 1) - (k + 1)` AND and OR gates. -/
theorem parity_sq_le_cost [NeZero n] {k : Nat} (c : Circuit DeMorgan.signature n 1)
    (computes : c.ComputesWith DeMorgan.interpretation (GateElimination.Xor.parityTarget n))
    (hk : sharedGateCount c ≤ k) :
    n ^ 2 ≤ (k + 1) * (c.cost DeMorgan.binaryCost + k + 1) := by
  obtain ⟨k', P, hk', hP, hgates⟩ := exists_sharedProgram_of_circuit c computes
  calc n ^ 2 ≤ (k' + 1) * (P.gates + k' + 1) := SharedProgram.parity_sq_le_gates hP
    _ ≤ (k + 1) * (c.cost DeMorgan.binaryCost + k + 1) :=
      Nat.mul_le_mul (by omega) (by omega)

/-- **Superlinear cost for parity with few shared gates.** If `(k + 1) · (C + 1) ≤ n`, every
De Morgan circuit computing the parity of `n` bits in which at most `k` gates have fan-out at
least two has at least `C · n` AND and OR gates. -/
theorem mul_le_cost_of_parity {k C : Nat} (hkn : (k + 1) * (C + 1) ≤ n)
    (c : Circuit DeMorgan.signature n 1)
    (computes : c.ComputesWith DeMorgan.interpretation (GateElimination.Xor.parityTarget n))
    (hk : sharedGateCount c ≤ k) : C * n ≤ c.cost DeMorgan.binaryCost := by
  obtain ⟨k', P, hk', hP, hgates⟩ := exists_sharedProgram_of_circuit c computes
  have hkn' : (k' + 1) * (C + 1) ≤ n :=
    le_trans (Nat.mul_le_mul_right _ (by omega)) hkn
  exact (SharedProgram.mul_le_gates_of_parity hkn' hP).trans hgates

/-- **Parity needs superlinear De Morgan circuits when `o(n)` gates have fan-out at least
two.** If `k n = o(n)` and, for every `n`, `c n` is a De Morgan circuit computing the parity of
`n` bits in which at most `k n` gates have fan-out at least two, then the number of AND and OR
gates of `c n` grows faster than `n`. -/
theorem isLittleO_cost_of_parity {k : ℕ → ℕ}
    (hk : (fun n => (k n : ℝ)) =o[Filter.atTop] fun n : ℕ => (n : ℝ))
    (c : (n : ℕ) → Circuit DeMorgan.signature n 1)
    (computes : ∀ n,
      (c n).ComputesWith DeMorgan.interpretation (GateElimination.Xor.parityTarget n))
    (hshared : ∀ n, sharedGateCount (c n) ≤ k n) :
    (fun n : ℕ => (n : ℝ)) =o[Filter.atTop] fun n => ((c n).cost DeMorgan.binaryCost : ℝ) :=
  isLittleO_of_forall_mul_le hk fun n _ hkn =>
    mul_le_cost_of_parity hkn (c n) (computes n) (hshared n)

end KW
end Algebraic
