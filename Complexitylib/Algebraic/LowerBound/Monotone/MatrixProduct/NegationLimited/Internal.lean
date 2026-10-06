/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Monotone.MatrixProduct.Internal

/-!
# Internals of the negation-limited Boolean matrix product bound

This file reduces De Morgan circuits with few NOT gates computing the Boolean
matrix product to the monotone partial-product bound
`Algebraic.Monotone.MatrixProduct.Internal.card_le_andCost`. The surface
statements are in
`Complexitylib.Algebraic.LowerBound.Monotone.MatrixProduct.NegationLimited`.

## Circuit surgery

* `freeze` replaces the line of selected gates by constant gates. When every
  frozen gate already takes its constant value on an assignment, evaluation on
  that assignment is unchanged (`trace_freeze`). Freezing only NOT gates keeps
  the AND-gate count (`andCost_freeze`) and removes the frozen NOT gates from
  the NOT-gate count.
* `restrictInputs` fixes the inputs outside a selected set to a constant by
  instantiating the circuit after a single constant gate.

## Few NOT gates (`div_mul_div_mul_le_andCost`)

Induction on the bound `t` on the number of NOT gates. Let `G` be the first NOT
gate. Every wire before it computes a monotone function (`isMonotone_trace`),
in particular its argument `h`. Let `F` be the left half of the variables:
the rows `i < I / 2` of `x` and the columns `j < J / 2` of `y`, and let `c` be
the value of `h` on the indicator of `F`. If `c = 0`, every assignment that is
zero outside `F` lies below that indicator, so `h` is zero there; if `c = 1`,
every assignment that is one on `F` lies above it, so `h` is one there. Fixing
the variables outside `F` to `0`, respectively those of `F` to `1`, therefore
makes `G` constant, so it can be frozen, and keeps a product of
`(I / 2) × K` by `K × (J / 2)` matrices on the rows and columns whose variables
stay free (the first halves if `c = 0`, the next halves if `c = 1`). The new
circuit has one NOT gate fewer and the same AND gates. With no NOT gate left,
the monotone bound gives `K * (I / 2 ^ t) * (J / 2 ^ t)` AND gates.

## NOT gates of few variables (`card_le_andCost_of_dependsOnlyOn`)

If every NOT gate computes a function of the variables in `S`, fixing those
variables to zero makes every NOT gate constant. Freezing them leaves a
circuit without NOT gates computing the partial product over the triples whose
variables avoid `S`, and at most `|S| * max I J` triples meet `S`.
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace MatrixProduct
namespace NegationLimited
namespace Internal

open Cslib.Circuits
open Algebraic.Monotone.MatrixProduct.Internal

noncomputable section

open scoped Classical

variable {n m g N M I J K : Nat}

/-! ### Freezing gates to constants -/

/-- The constant gate of value `b`. -/
def constLine : Bool → Line DeMorgan.signature n g
  | false => ⟨.false, Fin.elim0⟩
  | true => ⟨.true, Fin.elim0⟩

theorem constLine_mapWires (b : Bool) {n' g' : Nat} (f : Wire n g → Wire n' g') :
    (constLine b : Line DeMorgan.signature n g).mapWires f = constLine b := by
  cases b <;>
    · show Line.mk _ _ = Line.mk _ _
      congr
      funext a
      exact a.elim0

theorem constLine_eval (b : Bool) (x : Fin n → Bool) (values : Fin g → Bool) :
    (constLine b : Line DeMorgan.signature n g).eval DeMorgan.interpretation x values = b := by
  cases b <;> rfl

@[simp] theorem andCost_constLine (b : Bool) :
    DeMorgan.andCost (constLine b : Line DeMorgan.signature n g).op = 0 := by
  cases b <;> rfl

@[simp] theorem notCost_constLine (b : Bool) :
    DeMorgan.notCost (constLine b : Line DeMorgan.signature n g).op = 0 := by
  cases b <;> rfl

/-- Replace the line of every gate `G` with `sel G = some b` by the constant
gate `b`. -/
def freeze : {gates : Nat} → Program DeMorgan.signature n gates → (Fin gates → Option Bool) →
    Program DeMorgan.signature n gates
  | _, .empty, _ => .empty
  | _, .gate p line, sel =>
      (freeze p fun G => sel G.castSucc).gate ((sel (Fin.last _)).elim line constLine)

theorem lines_freeze (p : Program DeMorgan.signature n g) (sel : Fin g → Option Bool)
    (G : Fin g) : (freeze p sel).lines G = (sel G).elim (p.lines G) constLine := by
  induction p with
  | empty => exact G.elim0
  | @gate g p line ih =>
      induction G using Fin.lastCases with
      | last =>
          simp only [freeze, Program.lines_gate_last]
          cases sel (Fin.last g) <;> simp [constLine_mapWires]
      | cast G =>
          simp only [freeze, Program.lines_gate_castSucc, ih]
          cases sel G.castSucc <;> simp [constLine_mapWires]

/-- Freezing gates that already take their constant values does not change the
evaluation. -/
theorem eval_freeze (p : Program DeMorgan.signature n g) (sel : Fin g → Option Bool)
    (x : Fin n → Bool) (hsel : ∀ G b, sel G = some b → p.eval DeMorgan.interpretation x G = b) :
    (freeze p sel).eval DeMorgan.interpretation x = p.eval DeMorgan.interpretation x := by
  refine (Program.eq_eval_of_forall_lines_eval _ _ _ _ fun G => ?_).symm
  rw [lines_freeze]
  cases h : sel G with
  | none => exact p.lines_eval _ _ G
  | some b => rw [Option.elim_some, constLine_eval, hsel G b h]

theorem trace_freeze (p : Program DeMorgan.signature n g) (sel : Fin g → Option Bool)
    (x : Fin n → Bool) (hsel : ∀ G b, sel G = some b → p.eval DeMorgan.interpretation x G = b) :
    (freeze p sel).trace DeMorgan.interpretation x = p.trace DeMorgan.interpretation x := by
  unfold Program.trace
  rw [eval_freeze p sel x hsel]

theorem cost_freeze (p : Program DeMorgan.signature n g) (sel : Fin g → Option Bool)
    (cost : OperationCost DeMorgan.signature) :
    (freeze p sel).cost cost = ∑ G, cost ((sel G).elim (p.lines G) constLine).op := by
  rw [Program.cost_eq_sum_lines]
  simp only [lines_freeze]

/-- Freezing NOT gates keeps the AND-gate count. -/
theorem andCost_freeze (p : Program DeMorgan.signature n g) (sel : Fin g → Option Bool)
    (hsel : ∀ G b, sel G = some b → (p.lines G).op = .not) :
    (freeze p sel).cost DeMorgan.andCost = p.cost DeMorgan.andCost := by
  rw [cost_freeze, Program.cost_eq_sum_lines]
  refine Finset.sum_congr rfl fun G _ => ?_
  cases h : sel G with
  | none => rfl
  | some b => simp [hsel G b h]

/-- Freezing every NOT gate leaves none. -/
theorem notCost_freeze_eq_zero (p : Program DeMorgan.signature n g) (sel : Fin g → Option Bool)
    (hsel : ∀ G, (p.lines G).op = .not → sel G ≠ none) :
    (freeze p sel).cost DeMorgan.notCost = 0 := by
  rw [cost_freeze]
  refine Finset.sum_eq_zero fun G _ => ?_
  cases h : sel G with
  | none =>
      have hG : (p.lines G).op ≠ .not := fun hG => hsel G hG h
      simp only [Option.elim_none]
      cases hop : (p.lines G).op <;> simp_all
  | some b => simp

/-- Freezing one NOT gate removes exactly one NOT gate. -/
theorem notCost_freeze_single (p : Program DeMorgan.signature n g) (G₀ : Fin g)
    (hG₀ : (p.lines G₀).op = .not) (b : Bool) :
    (freeze p fun G => if G = G₀ then some b else none).cost DeMorgan.notCost + 1 =
      p.cost DeMorgan.notCost := by
  rw [cost_freeze, Program.cost_eq_sum_lines,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ G₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ G₀)]
  have hrest : ∑ G ∈ Finset.univ.erase G₀, DeMorgan.notCost
      ((if G = G₀ then some b else none).elim (p.lines G) constLine).op =
      ∑ G ∈ Finset.univ.erase G₀, DeMorgan.notCost (p.lines G).op := by
    refine Finset.sum_congr rfl fun G hG => ?_
    simp [Finset.ne_of_mem_erase hG]
  rw [hrest]
  simp [hG₀]
  omega

/-- Freeze the selected gates of a circuit. -/
def freezeCircuit (C : Circuit DeMorgan.signature n m) (sel : Fin C.size → Option Bool) :
    Circuit DeMorgan.signature n m :=
  ⟨freeze C.program sel, C.outputs⟩

/-! ### Fixing inputs to a constant -/

/-- Fix every input `v` with `keep v = false` to the constant `b`, read from a
single constant gate placed before the circuit. -/
def restrictInputs (C : Circuit DeMorgan.signature n m) (keep : Fin n → Bool) (b : Bool) :
    Circuit DeMorgan.signature n m :=
  C.instantiate (Program.empty.gate (constLine b)) fun v =>
    if keep v then Wire.input v else Wire.gate 0

theorem eval_restrictInputs (C : Circuit DeMorgan.signature n m) (keep : Fin n → Bool)
    (b : Bool) (a : Fin n → Bool) :
    (restrictInputs C keep b).eval DeMorgan.interpretation a =
      C.eval DeMorgan.interpretation fun v => if keep v then a v else b := by
  rw [restrictInputs, Circuit.eval_instantiate]
  congr 1
  funext v
  by_cases h : keep v
  · simp [h]
  · simp only [Function.comp_apply, h, Bool.false_eq_true, ite_false]
    exact constLine_eval b a _

theorem cost_restrictInputs (C : Circuit DeMorgan.signature n m) (keep : Fin n → Bool)
    (b : Bool) (cost : OperationCost DeMorgan.signature)
    (hcost : cost (constLine b : Line DeMorgan.signature n 0).op = 0) :
    (restrictInputs C keep b).cost cost = C.cost cost := by
  rw [restrictInputs, Circuit.cost_instantiate]
  simp [hcost]

/-! ### Wires below the first NOT gate -/

/-- A NOT gate computes the negation of its argument. -/
theorem interpretation_of_not (l : Line DeMorgan.signature n g) (hl : l.op = .not)
    (value : Wire n g → Bool) :
    DeMorgan.interpretation l.op (fun a => value (l.wires a)) =
      !value (l.wires ⟨0, by rw [hl]; decide⟩) := by
  obtain ⟨op, wires⟩ := l
  dsimp only at hl
  subst hl
  rfl

/-- Every wire before the first NOT gate computes a monotone function. -/
theorem isMonotone_trace (p : Program DeMorgan.signature n g) (B : Nat)
    (hB : ∀ G : Fin g, G.val < B → (p.lines G).op ≠ .not) (w : Wire n g)
    (hw : w.index.val < n + B) : IsMonotone fun a => p.trace DeMorgan.interpretation a w := by
  induction hi : w.index.val using Nat.strong_induction_on generalizing w with
  | _ i ih =>
    cases w with
    | input v => exact fun a b hab h => hab v h
    | gate G =>
      have hG : G.val < B := by simp at hw; omega
      have heq : (fun a => p.trace DeMorgan.interpretation a (Wire.gate G)) = fun a =>
          DeMorgan.interpretation (p.lines G).op fun m =>
            p.trace DeMorgan.interpretation a ((p.lines G).wires m) :=
        funext fun a => trace_gate p _ a G
      rw [heq]
      refine isMonotone_interpretation (hB G hG) fun m => ?_
      have hlt := p.lines_wires_lt G m
      exact ih _ (by simp at hi; omega) _ (by omega) rfl

/-! ### Halving -/

/-- The left half of the variables: rows `i < I / 2` of `x` and columns
`j < J / 2` of `y`. -/
def leftHalf (L : Layout N I J K) (v : Fin N) : Bool :=
  decide ((∃ i k, (i : Fin I).val < I / 2 ∧ L.x i k = v) ∨
    (∃ k j, (j : Fin J).val < J / 2 ∧ L.y k j = v))

theorem leftHalf_x (L : Layout N I J K) (i : Fin I) (k : Fin K) :
    leftHalf L (L.x i k) = decide (i.val < I / 2) := by
  rw [Bool.eq_iff_iff, leftHalf, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro (⟨i', k', h, he⟩ | ⟨k', j, -, he⟩)
    · exact (L.x_inj he).1 ▸ h
    · exact absurd he.symm (L.x_ne_y _ _ _ _)
  · exact fun h => Or.inl ⟨i, k, h, rfl⟩

theorem leftHalf_y (L : Layout N I J K) (k : Fin K) (j : Fin J) :
    leftHalf L (L.y k j) = decide (j.val < J / 2) := by
  rw [Bool.eq_iff_iff, leftHalf, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro (⟨i, k', -, he⟩ | ⟨k', j', h, he⟩)
    · exact absurd he (L.x_ne_y _ _ _ _)
    · exact (L.y_inj he).2 ▸ h
  · exact fun h => Or.inr ⟨k, j, h, rfl⟩

/-- The kept half of `Fin I`: the first `I / 2` indices when `b = false`, the
next `I / 2` when `b = true`. -/
def half (b : Bool) (i : Fin (I / 2)) : Fin I :=
  ⟨(bif b then I / 2 else 0) + i, by cases b <;> simp <;> omega⟩

theorem half_lt_iff (b : Bool) (i : Fin (I / 2)) : (half b i).val < I / 2 ↔ b = false := by
  cases b <;> simp [half]

theorem half_injective (b : Bool) : Function.Injective (half (I := I) b) := by
  intro i i' h
  ext
  have := congrArg Fin.val h
  simp only [half] at this
  omega

/-- The layout of the kept rows and columns. -/
def halveLayout (L : Layout N I J K) (b : Bool) : Layout N (I / 2) (J / 2) K where
  x i k := L.x (half b i) k
  y k j := L.y k (half b j)
  x_inj h := by
    obtain ⟨h₁, h₂⟩ := L.x_inj h
    exact ⟨half_injective b h₁, h₂⟩
  y_inj h := by
    obtain ⟨h₁, h₂⟩ := L.y_inj h
    exact ⟨h₁, half_injective b h₂⟩
  x_ne_y _ _ _ _ := L.x_ne_y _ _ _ _

/-- One NOT gate can be traded for halving the numbers of rows and columns. -/
theorem exists_halve (L : Layout N I J K) (z : Fin I → Fin J → Fin M)
    (C : Circuit DeMorgan.signature N M)
    (computes : ∀ a i j, C.eval DeMorgan.interpretation a (z i j) =
      decide (∃ k, a (L.x i k) = true ∧ a (L.y k j) = true))
    (hnot : 0 < C.cost DeMorgan.notCost) :
    ∃ (L' : Layout N (I / 2) (J / 2) K) (z' : Fin (I / 2) → Fin (J / 2) → Fin M)
      (C' : Circuit DeMorgan.signature N M),
      C'.cost DeMorgan.notCost + 1 = C.cost DeMorgan.notCost ∧
      C'.cost DeMorgan.andCost = C.cost DeMorgan.andCost ∧
      ∀ a i j, C'.eval DeMorgan.interpretation a (z' i j) =
        decide (∃ k, a (L'.x i k) = true ∧ a (L'.y k j) = true) := by
  -- The first NOT gate.
  have hex : (Finset.univ.filter fun G => (C.program.lines G).op = .not).Nonempty := by
    by_contra hno
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hno
    have : C.cost DeMorgan.notCost = 0 := by
      rw [Circuit.cost, Program.cost_eq_sum_lines]
      refine Finset.sum_eq_zero fun G _ => ?_
      have hG := hno (Finset.mem_univ G)
      cases hop : (C.program.lines G).op <;> simp_all
    omega
  set G₀ := (Finset.univ.filter fun G => (C.program.lines G).op = .not).min' hex
  have hG₀ : (C.program.lines G₀).op = .not := (Finset.mem_filter.1 (Finset.min'_mem _ hex)).2
  have hmin : ∀ G : Fin C.size, G.val < G₀.val → (C.program.lines G).op ≠ .not := by
    intro G hG hop
    have := Finset.min'_le (Finset.univ.filter fun G => (C.program.lines G).op = .not) G
      (Finset.mem_filter.2 ⟨Finset.mem_univ G, hop⟩)
    exact absurd hG (not_lt.2 this)
  -- Its argument is monotone.
  set arg := (C.program.lines G₀).wires ⟨0, by rw [hG₀]; decide⟩
  have hmono : IsMonotone fun a => C.program.trace DeMorgan.interpretation a arg :=
    isMonotone_trace C.program G₀.val hmin arg (C.program.lines_wires_lt G₀ _)
  set c := C.program.trace DeMorgan.interpretation (leftHalf L) arg
  set keep : Fin N → Bool := fun v => decide (leftHalf L v ≠ c)
  set restrict : (Fin N → Bool) → Fin N → Bool := fun a v => if keep v then a v else c
  have harg : ∀ a, C.program.trace DeMorgan.interpretation (restrict a) arg = c := by
    intro a
    cases hc : c
    · by_contra hne
      rw [Bool.not_eq_false] at hne
      have hle : AssignmentLE (restrict a) (leftHalf L) := by
        intro v hv
        simp only [restrict, keep, hc] at hv
        split_ifs at hv with hk
        · simpa using hk
      have h1 : c = true := hmono _ _ hle hne
      rw [hc] at h1
      exact absurd h1 (by simp)
    · have hle : AssignmentLE (leftHalf L) (restrict a) := by
        intro v hv
        simp [restrict, keep, hc, hv]
      exact hmono _ _ hle hc
  -- Freeze the NOT gate and fix the inputs.
  set sel : Fin C.size → Option Bool := fun G => if G = G₀ then some (!c) else none
  set C' := restrictInputs (freezeCircuit C sel) keep c
  have hsel : ∀ a, ∀ G b, sel G = some b →
      C.program.eval DeMorgan.interpretation (restrict a) G = b := by
    intro a G b h
    simp only [sel] at h
    split_ifs at h with hG
    subst hG
    cases h
    have := trace_gate C.program DeMorgan.interpretation (restrict a) G₀
    rw [interpretation_of_not _ hG₀] at this
    simp only [Program.trace_gateWire, Program.gateFunction_apply] at this
    rw [this, ← harg a]
  have heval : ∀ a, C'.eval DeMorgan.interpretation a =
      C.eval DeMorgan.interpretation (restrict a) := by
    intro a
    rw [eval_restrictInputs]
    show (freeze C.program sel).trace _ _ ∘ C.outputs = C.program.trace _ _ ∘ C.outputs
    rw [trace_freeze _ _ _ (hsel a)]
  refine ⟨halveLayout L c, fun i j => z (half c i) (half c j), C', ?_, ?_, ?_⟩
  · rw [cost_restrictInputs _ _ _ _ (notCost_constLine c)]
    exact notCost_freeze_single C.program G₀ hG₀ (!c)
  · rw [cost_restrictInputs _ _ _ _ (andCost_constLine c)]
    refine andCost_freeze C.program sel fun G b h => ?_
    simp only [sel] at h
    split_ifs at h with hG
    exact hG ▸ hG₀
  · intro a i j
    rw [heval, computes]
    have hkeep : ∀ v, keep v = true → restrict a v = a v := fun v h => by simp [restrict, h]
    have hx : ∀ k, keep (L.x (half c i) k) = true := fun k => by
      simp only [keep, leftHalf_x, decide_eq_true_eq]
      cases c <;> simp [half_lt_iff]
    have hy : ∀ k, keep (L.y k (half c j)) = true := fun k => by
      simp only [keep, leftHalf_y, decide_eq_true_eq]
      cases c <;> simp [half_lt_iff]
    simp only [hkeep _ (hx _), hkeep _ (hy _)]
    rfl

/-! ### Few NOT gates -/

/-- **Few NOT gates.** A De Morgan circuit with at most `t` NOT gates computing
the product of an `I × K` matrix and a `K × J` matrix, laid out injectively among
its inputs, has at least `(I / 2 ^ t) * (J / 2 ^ t) * K` AND gates. -/
theorem div_mul_div_mul_le_andCost (t : Nat) :
    ∀ {I J : Nat} (L : Layout N I J K) {M : Nat} (z : Fin I → Fin J → Fin M)
      (C : Circuit DeMorgan.signature N M), C.cost DeMorgan.notCost ≤ t →
      (∀ a i j, C.eval DeMorgan.interpretation a (z i j) =
        decide (∃ k, a (L.x i k) = true ∧ a (L.y k j) = true)) →
      I / 2 ^ t * (J / 2 ^ t) * K ≤ C.cost DeMorgan.andCost := by
  induction t with
  | zero =>
      intro I J L M z C ht computes
      have hcard := card_le_andCost L Finset.univ z C (by omega) fun a i j => by
        rw [computes]
        simp
      have hIJK : I * J * K = I * (K * J) := by
        rw [Nat.mul_assoc, Nat.mul_comm J K]
      simpa [hIJK, Finset.card_univ, Fintype.card_prod] using hcard
  | succ t ih =>
      intro I J L M z C ht computes
      by_cases h : C.cost DeMorgan.notCost ≤ t
      · refine le_trans ?_ (ih L z C h computes)
        have hpow : 2 ^ t ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ t)
        have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.div_le_div_left hpow hpos)
          (Nat.div_le_div_left hpow hpos)) le_rfl
      · obtain ⟨L', z', C', hnot, hand, hcomp⟩ := exists_halve L z C computes (by omega)
        have := ih L' z' C' (by omega) hcomp
        rw [hand, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_succ'] at this
        exact this

/-! ### NOT gates of few variables -/

/-- At most `|S| * max I J` triples have a variable in `S`. -/
theorem mul_mul_le_card_add (L : Layout N I J K) (S : Finset (Fin N)) :
    I * J * K ≤ (Finset.univ.filter fun t : Fin I × Fin K × Fin J =>
      L.x t.1 t.2.1 ∉ S ∧ L.y t.2.1 t.2.2 ∉ S).card + S.card * max I J := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    fun t : Fin I × Fin K × Fin J => L.x t.1 t.2.1 ∉ S ∧ L.y t.2.1 t.2.2 ∉ S
  have hbad : (Finset.univ.filter fun t : Fin I × Fin K × Fin J =>
      ¬ (L.x t.1 t.2.1 ∉ S ∧ L.y t.2.1 t.2.2 ∉ S)).card ≤ S.card * max I J := by
    rw [← Finset.card_range (max I J), ← Finset.card_product]
    refine Finset.card_le_card_of_injOn
      (fun t => if L.x t.1 t.2.1 ∈ S then (L.x t.1 t.2.1, t.2.2.val)
        else (L.y t.2.1 t.2.2, t.1.val)) ?_ ?_
    · rintro ⟨i, k, j⟩ ht
      rw [Finset.mem_coe, Finset.mem_filter, not_and_or, not_not, not_not] at ht
      replace ht := ht.2
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
      dsimp only at ht ⊢
      split_ifs with hx
      · exact ⟨hx, lt_of_lt_of_le j.isLt (le_max_right I J)⟩
      · exact ⟨ht.resolve_left hx, lt_of_lt_of_le i.isLt (le_max_left I J)⟩
    · rintro ⟨i, k, j⟩ - ⟨i', k', j'⟩ - h
      simp only at h
      split_ifs at h with hx hx' hx'
      · obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
        obtain ⟨rfl, rfl⟩ := L.x_inj h₁
        rw [Fin.val_inj.1 h₂]
      · exact absurd (Prod.mk.inj h).1 (L.x_ne_y _ _ _ _)
      · exact absurd (Prod.mk.inj h).1.symm (L.x_ne_y _ _ _ _)
      · obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
        obtain ⟨rfl, rfl⟩ := L.y_inj h₁
        rw [Fin.val_inj.1 h₂]
  have huniv : (Finset.univ : Finset (Fin I × Fin K × Fin J)).card = I * J * K := by
    simp [Finset.card_univ, Fintype.card_prod, Nat.mul_assoc, Nat.mul_comm J K]
  omega

/-- **NOT gates of few variables.** If every NOT gate of a De Morgan circuit
computing the product of an `I × K` matrix and a `K × J` matrix computes a
function of the variables in `S`, the circuit has at least
`I * J * K - |S| * max I J` AND gates. -/
theorem mul_mul_le_andCost_add (L : Layout N I J K) (z : Fin I → Fin J → Fin M)
    (C : Circuit DeMorgan.signature N M)
    (computes : ∀ a i j, C.eval DeMorgan.interpretation a (z i j) =
      decide (∃ k, a (L.x i k) = true ∧ a (L.y k j) = true))
    (S : Finset (Fin N))
    (local_ : ∀ G, (C.program.lines G).op = .not →
      DependsOnlyOn (C.program.gateFunction DeMorgan.interpretation G) S) :
    I * J * K ≤ C.cost DeMorgan.andCost + S.card * max I J := by
  set keep : Fin N → Bool := fun v => decide (v ∉ S)
  set restrict : (Fin N → Bool) → Fin N → Bool := fun a v => if keep v then a v else false
  set sel : Fin C.size → Option Bool := fun G =>
    if (C.program.lines G).op = .not then
      some (C.program.gateFunction DeMorgan.interpretation G fun _ => false)
    else none
  set C' := restrictInputs (freezeCircuit C sel) keep false
  have hsel : ∀ a, ∀ G b, sel G = some b →
      C.program.eval DeMorgan.interpretation (restrict a) G = b := by
    intro a G b h
    simp only [sel] at h
    split_ifs at h with hG
    cases h
    exact local_ G hG _ _ fun v hv => by simp [restrict, keep, hv]
  have heval : ∀ a, C'.eval DeMorgan.interpretation a =
      C.eval DeMorgan.interpretation (restrict a) := by
    intro a
    rw [eval_restrictInputs]
    show (freeze C.program sel).trace _ _ ∘ C.outputs = C.program.trace _ _ ∘ C.outputs
    rw [trace_freeze _ _ _ (hsel a)]
  set T := Finset.univ.filter fun t : Fin I × Fin K × Fin J =>
    L.x t.1 t.2.1 ∉ S ∧ L.y t.2.1 t.2.2 ∉ S
  have hcard : T.card ≤ C'.cost DeMorgan.andCost := by
    refine card_le_andCost L T z C' ?_ fun a i j => ?_
    · rw [cost_restrictInputs _ _ _ _ (notCost_constLine false)]
      refine notCost_freeze_eq_zero C.program sel fun G hG => ?_
      simp [sel, hG]
    · rw [heval, computes]
      congr 1
      refine propext (exists_congr fun k => ?_)
      by_cases hx : L.x i k ∈ S <;> by_cases hy : L.y k j ∈ S <;>
        simp [T, restrict, keep, hx, hy]
  have hand : C'.cost DeMorgan.andCost = C.cost DeMorgan.andCost := by
    rw [cost_restrictInputs _ _ _ _ (andCost_constLine false)]
    refine andCost_freeze C.program sel fun G b h => ?_
    simp only [sel] at h
    split_ifs at h with hG
    exact hG
  have hT : I * J * K ≤ T.card + S.card * max I J := mul_mul_le_card_add L S
  omega

end

end Internal
end NegationLimited
end MatrixProduct
end Monotone
end Algebraic
