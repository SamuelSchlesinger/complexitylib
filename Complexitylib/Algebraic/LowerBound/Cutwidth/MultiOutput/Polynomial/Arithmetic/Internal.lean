/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Defs
public import Complexitylib.Algebraic.Basis.Arithmetic

/-!
# Absorbing arithmetic constants into polynomial coefficients

The compiler tracks an original wire either as a field constant or as a wire of
the emitted program. Only addition and multiplication emit gates. Their constant
operands are absorbed into the displayed bivariate polynomial.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Polynomial.ArithmeticInternal

variable {F K : Type*} [CommSemiring F] {n g h : ℕ}

/-- An eliminated constant or a retained signal. -/
abbrev Ref (F : Type*) (n h : ℕ) := F ⊕ Wire n h

/-- Semantic value of a retained reference. -/
def value (values : Wire n h → F) : Ref F n h → F := Sum.elim id values

/-- Constants ignore their placeholder wire; other references use their retained wire. -/
def wire (dummy : Fin n) : Ref F n h → Wire n h
  | .inl _ => .input dummy
  | .inr w => w

/-- A local argument becomes either a constant polynomial or the corresponding variable. -/
noncomputable def argument (slot : Fin 2) : Ref F n h → MvPolynomial (Fin 2) F
  | .inl c => MvPolynomial.C c
  | .inr _ => MvPolynomial.X slot

/-- Interpret the addition/multiplication selector. -/
def binary (add : Bool) (x y : F) : F := if add then x + y else x * y

/-- One emitted binary gate, with constants absorbed into its polynomial coefficients. -/
noncomputable def binaryLine (dummy : Fin n) (add : Bool) (args : Fin 2 → Ref F n h) :
    Line (signature F) n h where
  op := ⟨2, if add then argument 0 (args 0) + argument 1 (args 1)
    else argument 0 (args 0) * argument 1 (args 1)⟩
  wires slot := wire dummy (args slot)

/-- Substituting constants and variables recovers each original argument value. -/
theorem eval_argument (dummy : Fin n) (args : Fin 2 → Ref F n h)
    (values : Wire n h → F) (slot : Fin 2) :
    MvPolynomial.eval (fun i => values (wire dummy (args i)))
      (argument slot (args slot)) = value values (args slot) := by
  cases harg : args slot <;> simp [argument, value, wire, harg]

/-- The emitted gate has the same local arithmetic value. -/
theorem eval_binaryLine (dummy : Fin n) (add : Bool) (args : Fin 2 → Ref F n h)
    (x : Fin n → F) (prior : Fin h → F) :
    (binaryLine dummy add args).eval (interpretation F) x prior =
      binary add (value (Wire.elim x prior) (args 0))
        (value (Wire.elim x prior) (args 1)) := by
  change MvPolynomial.eval (fun i : Fin 2 => Wire.elim x prior (wire dummy (args i)))
    (if add then argument 0 (args 0) + argument 1 (args 1)
      else argument 0 (args 0) * argument 1 (args 1)) = _
  cases add <;> simp [binary, MvPolynomial.eval_add, MvPolynomial.eval_mul, eval_argument]

/-- Existing retained wires survive the insertion of one new gate. -/
def liftRef : Ref F n h → Ref F n (h + 1) := Sum.map id Wire.castSucc

/-- Lifting a reference preserves its value when extending the target program. -/
theorem value_liftRef (q : Program (signature F) n h) (line : Line (signature F) n h)
    (x : Fin n → F) (ref : Ref F n h) :
    value ((q.gate line).trace (interpretation F) x) (liftRef ref) =
      value (q.trace (interpretation F) x) ref := by
  cases ref <;> simp [liftRef, value]

/-- Each arithmetic program has a polynomial realization with exactly its nonconstant cost. -/
theorem exists_program (hn : 0 < n) (constant : K → F)
    (p : Program (Arithmetic.signature K) n g) :
    ∃ (h : ℕ) (q : Program (signature F) n h) (refs : Wire n g → Ref F n h),
      h = p.cost Arithmetic.gateCost ∧ q.FanInAtMost 2 ∧
      ∀ x w, value (q.trace (interpretation F) x) (refs w) =
        p.trace (Arithmetic.interpretation constant) x w := by
  let dummy : Fin n := ⟨0, hn⟩
  induction p with
  | empty =>
      refine ⟨0, .empty, Sum.inr, rfl, trivial, ?_⟩
      intro x w
      cases w with
      | input => rfl
      | gate i => exact Fin.elim0 i
  | @gate g p line ih =>
      obtain ⟨h, q, refs, size, fanin, correct⟩ := ih
      cases line with
      | mk op wires =>
        cases op with
        | constant c =>
            refine ⟨h, q, Wire.lastCases (.inl (constant c)) refs, ?_, fanin, ?_⟩
            · simpa [Program.cost, Arithmetic.gateCost, Arithmetic.weightedCost] using size
            · intro x w
              refine Wire.lastCases ?_ (fun v => ?_) w
              · simp [value, Program.trace, Line.eval, Arithmetic.interpretation]
              · simpa using correct x v
        | add =>
            let args : Fin 2 → Ref F n h := fun i => refs (wires i)
            let line := binaryLine dummy true args
            refine ⟨h + 1, q.gate line,
              Wire.lastCases (.inr (.gate (Fin.last h))) (fun w => liftRef (refs w)),
              ?_, ⟨fanin, le_rfl⟩, ?_⟩
            · simp [Program.cost, Arithmetic.gateCost, Arithmetic.weightedCost, size]
            · intro x w
              refine Wire.lastCases ?_ (fun v => ?_) w
              · simp only [Wire.lastCases_last, value, Sum.elim_inr, Program.trace_gateWire,
                  Program.gateFunction_gate_last]
                rw [show line = binaryLine dummy true args from rfl, eval_binaryLine]
                change value (q.trace (interpretation F) x) (refs (wires (0 : Fin 2))) +
                  value (q.trace (interpretation F) x) (refs (wires (1 : Fin 2))) = _
                rw [correct, correct]
                rfl
              · simpa only [Wire.lastCases_castSucc, value_liftRef,
                  Program.trace_gate_castSucc] using correct x v
        | mul =>
            let args : Fin 2 → Ref F n h := fun i => refs (wires i)
            let line := binaryLine dummy false args
            refine ⟨h + 1, q.gate line,
              Wire.lastCases (.inr (.gate (Fin.last h))) (fun w => liftRef (refs w)),
              ?_, ⟨fanin, le_rfl⟩, ?_⟩
            · simp [Program.cost, Arithmetic.gateCost, Arithmetic.weightedCost, size]
            · intro x w
              refine Wire.lastCases ?_ (fun v => ?_) w
              · simp only [Wire.lastCases_last, value, Sum.elim_inr, Program.trace_gateWire,
                  Program.gateFunction_gate_last]
                rw [show line = binaryLine dummy false args from rfl, eval_binaryLine]
                change value (q.trace (interpretation F) x) (refs (wires (0 : Fin 2))) *
                  value (q.trace (interpretation F) x) (refs (wires (1 : Fin 2))) = _
                rw [correct, correct]
                rfl
              · simpa only [Wire.lastCases_castSucc, value_liftRef,
                  Program.trace_gate_castSucc] using correct x v

/-- Nonconstant designated outputs use retained signals, so they need no final constant gates. -/
theorem exists_circuit (hn : 0 < n) (constant : K → F) {m : ℕ}
    (c : Circuit (Arithmetic.signature K) n m)
    (nonconstant : ∀ j, ∃ x y,
      c.eval (Arithmetic.interpretation constant) x j ≠
        c.eval (Arithmetic.interpretation constant) y j) :
    ∃ d : Circuit (signature F) n m,
      d.size = c.cost Arithmetic.gateCost ∧ d.FanInAtMost 2 ∧
      ∀ x, d.eval (interpretation F) x = c.eval (Arithmetic.interpretation constant) x := by
  classical
  obtain ⟨h, q, refs, size, fan, correct⟩ := exists_program hn constant c.program
  have signal : ∀ j, ∃ w, refs (c.outputs j) = Sum.inr w := by
    intro j
    cases eq : refs (c.outputs j) with
    | inr w => exact ⟨w, rfl⟩
    | inl a =>
        obtain ⟨x, y, different⟩ := nonconstant j
        have hx := correct x (c.outputs j)
        have hy := correct y (c.outputs j)
        simp only [eq, value, Sum.elim_inl, id_eq] at hx hy
        exact False.elim (different (hx.symm.trans hy))
  choose outputs eq using signal
  refine ⟨⟨q, outputs⟩, size, fan, ?_⟩
  intro x
  funext j
  have equality := correct x (c.outputs j)
  simpa only [eq, value, Sum.elim_inr, Circuit.eval, Program.trace,
    Function.comp_apply] using equality

/-- Every output of a nonempty totally regular linear map is nonconstant. -/
theorem outputs_nonconstant {F K : Type*} [Field F] {n : ℕ} (hn : 0 < n)
    (constant : K → F) (c : Circuit (Arithmetic.signature K) n n)
    {M : Matrix (Fin n) (Fin n) F} (regular : TotallyRegular M)
    (computes : c.Computes (Arithmetic.interpretation constant) (fun x => M.mulVec x)) :
    ∀ i, ∃ x y, c.eval (Arithmetic.interpretation constant) x i ≠
      c.eval (Arithmetic.interpretation constant) y i := by
  classical
  intro i
  let j : Fin n := ⟨0, hn⟩
  have nonzero : M i j ≠ 0 := by
    have minor := regular 1 (fun _ => i) (fun _ => j)
      (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ _ => Subsingleton.elim _ _)
    simpa using minor
  refine ⟨0, Pi.single j 1, ?_⟩
  rw [computes, computes]
  simpa using nonzero.symm

end Algebraic.Cutwidth.MultiOutput.Polynomial.ArithmeticInternal
