/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Linear.Basis
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Pi

/-!
# Linearizing polynomial circuits

**Affine circuits compute affine functions** (`Frontier.exists_affine_trace`): in a circuit over
the affine basis, the value of every wire is an affine function of the input.

**Linearization** (`Frontier.exists_affine_circuit`). Over an infinite field, a circuit with
polynomial operations that computes a linear map `x ↦ M x` can be replaced by a circuit over
the affine basis, with the same wires, that computes the same map. Each gate is replaced by its
first-order Taylor expansion at the point its arguments take when the input is zero
(`Frontier.taylorOp`, `Frontier.linearize`).

To see why this works, evaluate the circuit over the dual numbers `F[ε]`, where `ε² = 0`, at the
input `ε x`. Because the operations are polynomials, a gate whose arguments are `z + ε v` takes
the value `P(z) + ε ∑_a ∂_a P(z) v_a` (`Frontier.snd_aeval_dualNumber`), and `z` is the value of
the arguments at the zero input. So where the circuit takes the value `a + ε b` at `ε x`, the
linearized circuit takes the value `a + b` at `x` (`Frontier.trace_linearize`). Over an
infinite field a polynomial is determined by its values, so the polynomial computed at an output
is the linear form `∑_j M_{ij} X_j`, whose value at `ε x` is `ε (M x)_i`.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits MvPolynomial TrivSqZeroExt
open scoped DualNumber

variable {F : Type*} {n s m : ℕ}

/-- The value of the last gate of a program is its operation applied to the values of its
arguments. -/
private theorem trace_gate_last {σ : Signature} {U : Type*} (p : Program σ n s)
    (line : Line σ n s) (I : Interpretation σ U) (x : Fin n → U) :
    (p.gate line).trace I x (.gate (Fin.last s)) = I line.op fun a => p.trace I x (line.wires a) :=
  p.eval_gate_last line I x

/-- **Affine circuits compute affine functions.** -/
theorem exists_affine_trace [CommRing F] (p : Program (affineSignature F) n s) (w : Wire n s) :
    ∃ (L : (Fin n → F) →ₗ[F] F) (b : F), ∀ x, p.trace (affineInterpretation F) x w = L x + b := by
  induction p with
  | empty =>
    cases w with
    | input i => exact ⟨LinearMap.proj i, 0, fun x => by simp⟩
    | gate g => exact g.elim0
  | gate p line ih =>
    refine Wire.lastCases ?_ (fun w => ?_) w
    · obtain ⟨⟨k, c, d⟩, wires⟩ := line
      choose L b h using fun a => ih (wires a)
      refine ⟨∑ a, c a • L a, ∑ a, c a * b a + d, fun x => ?_⟩
      rw [trace_gate_last]
      simp [affineInterpretation, h, mul_add, Finset.sum_add_distrib, add_assoc]
    · obtain ⟨L, b, h⟩ := ih w
      exact ⟨L, b, fun x => by rw [Program.trace_gate_castSucc, h]⟩

/-! ### Polynomial interpretations over algebras -/

section Polynomial

variable {σ : Signature} [CommRing F] (P : (o : σ.Op) → MvPolynomial (Fin (σ.Arity o)) F)

/-- The interpretation over an `F`-algebra `R` in which each operation `o` substitutes its
arguments into the polynomial `P o`. Every polynomial interpretation over `F` is of this form,
for a suitable choice of the polynomials `P`. -/
noncomputable def polynomialInterpretation (R : Type*) [CommRing R] [Algebra F R] :
    Interpretation σ R :=
  fun o x => aeval x (P o)

/-- An operation of a polynomial interpretation substitutes its arguments into its
polynomial. -/
theorem polynomialInterpretation_apply (R : Type*) [CommRing R] [Algebra F R] (o : σ.Op)
    (x : Fin (σ.Arity o) → R) : polynomialInterpretation P R o x = aeval x (P o) :=
  rfl

/-- Evaluation of a program with polynomial operations commutes with algebra homomorphisms. -/
theorem map_trace_polynomialInterpretation {R S : Type*} [CommRing R] [Algebra F R] [CommRing S]
    [Algebra F S] (φ : R →ₐ[F] S) (p : Program σ n s) (x : Fin n → R) (w : Wire n s) :
    φ (p.trace (polynomialInterpretation P R) x w) =
      p.trace (polynomialInterpretation P S) (fun j => φ (x j)) w :=
  congrFun (p.map_trace ⟨φ, fun o y => comp_aeval_apply y φ (P o)⟩ x) w

end Polynomial

/-! ### First-order Taylor expansion -/

section Taylor

variable [CommRing F] {k : ℕ}

/-- The real part of a polynomial at a dual number is its value at the real parts. -/
theorem fst_aeval_dualNumber (P : MvPolynomial (Fin k) F) (u : Fin k → F[ε]) :
    (aeval u P).fst = eval (fun a => (u a).fst) P :=
  comp_aeval_apply u (fstHom F F F) P

/-- **Taylor expansion over the dual numbers.** The dual part of `P(z + ε v)` is
`∑_a ∂_a P(z) v_a`. -/
theorem snd_aeval_dualNumber (P : MvPolynomial (Fin k) F) (u : Fin k → F[ε]) :
    (aeval u P).snd = ∑ a, eval (fun b => (u b).fst) (pderiv a P) * (u a).snd := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [algebraMap_eq_inl]
  | add P Q hP hQ => simp [hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P i hP =>
    have hX (a : Fin k) :
        eval (fun b => (u b).fst) (pderiv a (X i : MvPolynomial (Fin k) F)) =
          (Pi.single i 1 : Fin k → F) a := by
      by_cases h : a = i <;> simp [h, Ne.symm]
    rw [map_mul, aeval_X, DualNumber.snd_mul, fst_aeval_dualNumber, hP, Finset.sum_mul]
    simp only [pderiv_mul, map_add, map_mul, eval_X, hX, add_mul, Finset.sum_add_distrib,
      Pi.single_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    rw [add_comm]
    exact congrArg (· + _) (Finset.sum_congr rfl fun a _ => mul_right_comm _ _ _)

/-- The affine operation computing the first-order Taylor expansion of `P` at `z`,
`y ↦ P(z) + ∑_a ∂_a P(z) (y_a - z_a)`. -/
noncomputable def taylorOp (P : MvPolynomial (Fin k) F) (z : Fin k → F) :
    (affineSignature F).Op :=
  ⟨k, fun a => eval z (pderiv a P), eval z P - ∑ a, eval z (pderiv a P) * z a⟩

/-- The value of the first-order Taylor expansion of `P` at `z`. -/
theorem affineInterpretation_taylorOp (P : MvPolynomial (Fin k) F) (z y : Fin k → F) :
    affineInterpretation F (taylorOp P z) y =
      eval z P + ∑ a, eval z (pderiv a P) * (y a - z a) := by
  change ∑ a, eval z (pderiv a P) * y a + (eval z P - ∑ a, eval z (pderiv a P) * z a) = _
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end Taylor

/-! ### Linearization -/

section Linearize

variable {σ : Signature} [CommRing F] (P : (o : σ.Op) → MvPolynomial (Fin (σ.Arity o)) F)

/-- The *linearization* of a program whose operations are the polynomials `P`: the program over
the affine basis with the same wires, in which each gate is replaced by its first-order Taylor
expansion at the point that its arguments take on the zero input. -/
noncomputable def linearize {s : ℕ} : Program σ n s → Program (affineSignature F) n s
  | .empty => .empty
  | .gate p line => (linearize p).gate
      ⟨taylorOp (P line.op) fun a => p.trace (polynomialInterpretation P F) 0 (line.wires a),
        line.wires⟩

/-- Linearization preserves the arity of every gate. -/
theorem arity_lines_linearize (p : Program σ n s) (g : Fin s) :
    (affineSignature F).Arity ((linearize P p).lines g).op = σ.Arity (p.lines g).op := by
  induction p with
  | empty => exact g.elim0
  | gate p line ih =>
    refine Fin.lastCases ?_ (fun g => ?_) g
    · simp only [linearize, Program.lines_gate_last, Line.mapWires_op]
      rfl
    · simp only [linearize, Program.lines_gate_castSucc, Line.mapWires_op]
      exact ih g

/-- Linearization preserves the inner gates. -/
theorem innerGates_linearize (p : Program σ n s) : (linearize P p).innerGates = p.innerGates :=
  Finset.filter_congr fun g _ => by rw [arity_lines_linearize]

/-- Linearization preserves fan-in. -/
theorem fanInAtMost_linearize (p : Program σ n s) (r : ℕ) :
    (linearize P p).FanInAtMost r ↔ p.FanInAtMost r := by
  induction p with
  | empty => exact Iff.rfl
  | gate p line ih => exact and_congr ih Iff.rfl

/-- The real part of the value of a wire at the input `ε x` is its value at the zero input. -/
theorem fst_trace_dualNumber (p : Program σ n s) (x : Fin n → F) (w : Wire n s) :
    (p.trace (polynomialInterpretation P F[ε]) (fun j => inr (x j)) w).fst =
      p.trace (polynomialInterpretation P F) 0 w :=
  map_trace_polynomialInterpretation P (fstHom F F F) p _ w

/-- **The linearized program.** Where the original program takes the value `a + ε b` at the
input `ε x`, the linearized program takes the value `a + b` at the input `x`. -/
theorem trace_linearize (p : Program σ n s) (x : Fin n → F) (w : Wire n s) :
    (linearize P p).trace (affineInterpretation F) x w =
      (p.trace (polynomialInterpretation P F[ε]) (fun j => inr (x j)) w).fst +
        (p.trace (polynomialInterpretation P F[ε]) (fun j => inr (x j)) w).snd := by
  induction p with
  | empty =>
    cases w with
    | input i => simp
    | gate g => exact g.elim0
  | gate p line ih =>
    refine Wire.lastCases ?_ (fun w => ?_) w
    · -- The new gate is the first-order Taylor expansion of the old one.
      refine (trace_gate_last _ _ _ _).trans ((affineInterpretation_taylorOp _ _ _).trans ?_)
      rw [trace_gate_last]
      simp only [ih, polynomialInterpretation_apply, fst_aeval_dualNumber, snd_aeval_dualNumber,
        fst_trace_dualNumber, add_sub_cancel_left]
    · simpa only [linearize, Program.trace_gate_castSucc] using ih w

/-- Over an infinite field, a circuit with polynomial operations that computes `x ↦ M x` takes
the value `ε (M x)_i` at its output `i` on the input `ε x`. -/
theorem trace_output_dualNumber [IsDomain F] [Infinite F] (c : Circuit σ n m)
    (M : Matrix (Fin m) (Fin n) F)
    (hc : c.Computes (polynomialInterpretation P F) fun x => M.mulVec x) (x : Fin n → F)
    (i : Fin m) :
    c.program.trace (polynomialInterpretation P F[ε]) (fun j => inr (x j)) (c.outputs i) =
      inr (M.mulVec x i) := by
  -- The polynomial computed at the output.
  have hQ : c.program.trace (polynomialInterpretation P (MvPolynomial (Fin n) F)) X
      (c.outputs i) = ∑ j, C (M i j) * X j := by
    refine MvPolynomial.funext fun y => ?_
    have h := map_trace_polynomialInterpretation P (aeval y) c.program X (c.outputs i)
    simp only [aeval_X, aeval_eq_eval] at h
    rw [h]
    exact (congrFun (hc y) i).trans (by simp [Matrix.mulVec, dotProduct])
  -- Its value at `ε x`.
  have h := map_trace_polynomialInterpretation P (aeval fun j => (inr (x j) : F[ε])) c.program X
    (c.outputs i)
  simp only [aeval_X] at h
  rw [← h, hQ]
  ext <;> simp [algebraMap_eq_inl, fst_sum, snd_sum, Matrix.mulVec, dotProduct]

end Linearize

/-- **Linearization.** Over an infinite field, a circuit with polynomial operations computing a
linear map is matched by a circuit over the affine basis computing the same map, with the same
number of gates, the same inner gates, and the same fan-in. -/
theorem exists_affine_circuit [Field F] [Infinite F] {σ : Signature} {I : Interpretation σ F}
    (hI : IsPolynomial I) (c : Circuit σ n m) (M : Matrix (Fin m) (Fin n) F)
    (hc : c.Computes I fun x => M.mulVec x) :
    ∃ c' : Circuit (affineSignature F) n m, c'.size = c.size ∧ c'.innerSize = c.innerSize ∧
      (∀ r, c.FanInAtMost r → c'.FanInAtMost r) ∧
      c'.Computes (affineInterpretation F) fun x => M.mulVec x := by
  choose P hP using hI
  obtain rfl : I = polynomialInterpretation P F := funext fun o => funext (hP o)
  refine ⟨⟨linearize P c.program, c.outputs⟩, rfl, congrArg Finset.card
    (innerGates_linearize P c.program), fun r => (fanInAtMost_linearize P c.program r).2,
    fun x => funext fun i => ?_⟩
  change (linearize P c.program).trace _ x (c.outputs i) = _
  rw [trace_linearize, trace_output_dualNumber P c M hc]
  simp

end Complexity.Frontier
