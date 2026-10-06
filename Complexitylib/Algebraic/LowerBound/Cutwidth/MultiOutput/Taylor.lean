/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Taylor.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Defs
public import Mathlib.Algebra.MvPolynomial.Funext
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Taylor.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Internal

/-!
# The Taylor cut lemma

Let a straight-line program have gates that are polynomials with coefficients in a commutative
ring `K`, of any degree and any arity, so that it computes a polynomial `f_w ∈ K[X₀, …, X_{n-1}]`
on every wire `w` (`wirePolynomial`). Fix a field `L` that is a `K`-algebra, a point
`a ∈ L ^ n`, and a set `S` of wires with complement `T`; let `X_S` and `X_T` be the inputs on
the two sides and `w(S) = |forward S| + |backward S|` the number of signals crossing the split.

**The Taylor cut lemma** (`exists_cut`). There are subspaces `V` of directions supported on
`X_S` and `W` of directions supported on `X_T`, with `dim V + dim W ≥ n - w(S)`, such that

* (a) every `v ∈ V` fixes every wire of `T` to first order: `∇f_t(a) · v = 0`;
* (b) every `u ∈ W` fixes every wire of `S` to first order: `∇f_s(a) · u = 0`;
* (c) for every wire, the Hessian at `a` pairs `V` with `W` to zero: `vᵀ ∇²f_w(a) u = 0`.

*Proof.* Run the program over the algebra `L[s, t] = L[s][t]` with `s² = t² = 0`, where at the
input `a + s v + t u` every wire carries `f(a) + s ∇f(a)·v + t ∇f(a)·u + s t vᵀ ∇²f(a) u`. Let
`Z` be the directions along which no crossing wire moves to first order; it is cut out by
`w(S)` linear equations. Two jets `a + s v` and `a + t u` with `v, u ∈ Z` give every crossing
wire the same value, so they have the same boundary key, and cut and paste
(`SingleCut.trace_mix`) and the vanishing mixed second difference
(`trace_add_trace_eq_trace_mix_add_trace_mix`) hold for them over `L[s, t]`. Comparing the
coefficients of `s`, `t` and `s t` shows that `Z` is the sum of its parts `V` on `X_S` and `W` on
`X_T`, and gives (a), (b) and (c).

**The Jacobian consequence** (`blockRank_jacobian_add_blockRank_le`). For the outputs `O_S`
carried in `S` and `O_T` carried in `T`, `rank J[O_T, X_S] + rank J[O_S, X_T] ≤ w(S)`, where `J`
is the Jacobian of the outputs at `a`: by (a) and (b), `V` and `W` lie in the kernels of the two
blocks.

**The Hessian consequence** (`blockRank_hessian_le`). For every combination `∑ₒ μₒ fₒ` of the
outputs, with coefficients in `L`, `rank H[X_S, X_T] ≤ w(S)`, where `H = ∑ₒ μₒ ∇²fₒ(a)`: by (c),
`V` and `W` are orthogonal through `H[X_S, X_T]`, which forces
`dim V + dim W ≤ n - rank H[X_S, X_T]`.

Both consequences hold over every field: no counting is involved, and the coefficients `μ` and
the point `a` may lie in an extension of the coefficient field. Over a finite field the
counting arguments of `MultiOutput.Rank` and `MultiOutput.Quadratic` give the same bounds for
arbitrary gate functions; here the gates must be polynomials and the polynomials are the formal
ones (`FormallyComputes`), which over an infinite field are determined by the functions
(`formallyComputes_of_computes`).

*Prior art.* The use of the rank of a Hessian block to bound the communication between two
parties evaluating a function of their inputs is due to Abelson (*Lower bounds on information
transfer in distributed computations*, JACM 1980). Here it is applied to every cut of a
circuit at once, as an algebraic counterpart of the single-cut criterion.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Taylor

open SingleCut Matrix MvPolynomial Module

variable {K : Type*} [CommRing K] {σ : Signature} {n s m : ℕ}
  (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)

/-! ## Formal evaluation -/

/-- Over every commutative `K`-algebra, a wire carries its wire polynomial evaluated at the
input. -/
theorem trace_eq_aeval_wirePolynomial {A : Type*} [CommSemiring A] [Algebra K A]
    (p : Program σ n s) (x : Fin n → A) (w : Wire n s) :
    p.trace (algebraInterpretation P A) x w = aeval x (wirePolynomial P p w) :=
  Internal.trace_eq_aeval_wirePolynomial P p x w

/-- A circuit formally computing polynomials computes them as functions over every commutative
`K`-algebra. -/
theorem FormallyComputes.computes {P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K}
    {c : Circuit σ n m} {f : Fin m → MvPolynomial (Fin n) K}
    (hc : FormallyComputes P c f) (A : Type*) [CommSemiring A] [Algebra K A] :
    c.Computes (algebraInterpretation P A) fun x o => aeval x (f o) := by
  intro x
  funext o
  change c.program.trace _ x (c.outputs o) = _
  rw [trace_eq_aeval_wirePolynomial, hc o]

/-- **Over an infinite field, computing is formal computing.** A circuit whose operations are
polynomial functions and which computes polynomial functions formally computes the
polynomials, for the polynomials chosen to represent its operations. -/
theorem formallyComputes_of_computes {F : Type*} [Field F] [Infinite F]
    {I : Interpretation σ F} (hI : Polynomial.IsPolynomial I) {c : Circuit σ n m}
    {f : Fin m → MvPolynomial (Fin n) F} (hc : c.Computes I fun x o => eval x (f o)) :
    FormallyComputes hI.gatePolynomial c f := by
  intro o
  apply MvPolynomial.funext
  intro x
  have h := Polynomial.Internal.wirePolynomial_eval hI c.program x (c.outputs o)
  exact h.trans (congrFun (hc x) o)

/-- Over every commutative `K`-algebra, the arithmetic gate polynomials interpret addition,
multiplication and the constants mapped into the algebra. -/
theorem algebraInterpretation_arithmeticPolynomial {Kc : Type*} (constant : Kc → K)
    (A : Type*) [CommSemiring A] [Algebra K A] :
    algebraInterpretation (arithmeticPolynomial constant) A =
      Arithmetic.interpretation fun k => algebraMap K A (constant k) := by
  funext op x
  cases op with
  | add =>
    have h : ∀ y : Fin 2 → A, aeval y (X 0 + X 1 : MvPolynomial (Fin 2) K) = y 0 + y 1 :=
      fun y => by simp
    exact h x
  | mul =>
    have h : ∀ y : Fin 2 → A, aeval y (X 0 * X 1 : MvPolynomial (Fin 2) K) = y 0 * y 1 :=
      fun y => by simp
    exact h x
  | constant k => exact aeval_C _ _

/-! ## The cut lemma -/

section Cut

variable {L : Type*} [Field L] [Algebra K L]

/-- **The directed Taylor cut lemma.** For every set `S` of wires of a program with polynomial
gates and every point `a`, there are subspaces `V` of directions on the inputs in `S` and `W` of
directions on the other inputs, with `|X_S| ≤ dim V + |forward S|` and
`|X_T| ≤ dim W + |backward S|` separately, such that every direction of `V` fixes every wire
outside `S` to first order, every direction of `W` fixes every wire in `S` to first order, and
the Hessian of every wire pairs `V` with `W` to zero. -/
theorem exists_cut_directed (p : Program σ n s) (S : Finset (Wire n s)) (a : Fin n → L) :
    ∃ V W : Submodule L (Fin n → L),
      (∀ v ∈ V, ∀ j, j ∉ inputsIn S → v j = 0) ∧ (∀ u ∈ W, ∀ j ∈ inputsIn S, u j = 0) ∧
      (inputsIn S).card ≤ finrank L V + (forward p S).card ∧
      (inputsIn S)ᶜ.card ≤ finrank L W + (backward p S).card ∧
      (∀ v ∈ V, ∀ w, w ∉ S → (jacobian (wirePolynomial P p) a *ᵥ v) w = 0) ∧
      (∀ u ∈ W, ∀ w ∈ S, (jacobian (wirePolynomial P p) a *ᵥ u) w = 0) ∧
      ∀ v ∈ V, ∀ u ∈ W, ∀ w, v ⬝ᵥ (hessian (wirePolynomial P p w) a *ᵥ u) = 0 :=
  Internal.exists_cut_directed P p S a

/-- **The Taylor cut lemma.** For every set `S` of wires of a program with polynomial gates and
every point `a`, there are subspaces `V` of directions on the inputs in `S` and `W` of
directions on the other inputs, of total dimension at least `n - |forward S| - |backward S|`,
such that every direction of `V` fixes every wire outside `S` to first order, every direction
of `W` fixes every wire in `S` to first order, and the Hessian of every wire pairs `V` with `W`
to zero. -/
theorem exists_cut (p : Program σ n s) (S : Finset (Wire n s)) (a : Fin n → L) :
    ∃ V W : Submodule L (Fin n → L),
      (∀ v ∈ V, ∀ j, j ∉ inputsIn S → v j = 0) ∧ (∀ u ∈ W, ∀ j ∈ inputsIn S, u j = 0) ∧
      n ≤ finrank L V + finrank L W + ((forward p S).card + (backward p S).card) ∧
      (∀ v ∈ V, ∀ w, w ∉ S → (jacobian (wirePolynomial P p) a *ᵥ v) w = 0) ∧
      (∀ u ∈ W, ∀ w ∈ S, (jacobian (wirePolynomial P p) a *ᵥ u) w = 0) ∧
      ∀ v ∈ V, ∀ u ∈ W, ∀ w, v ⬝ᵥ (hessian (wirePolynomial P p w) a *ᵥ u) = 0 :=
  Internal.exists_cut P p S a

/-- **The forward Jacobian consequence, for a program.** The block of the Jacobian of the outputs
at `a`, from the inputs in `S` to the outputs outside `S`, has rank at most `|forward S|`. -/
theorem blockRank_jacobian_le_forward_of_trace (p : Program σ n s)
    (out : Fin m → Wire n s) (S : Finset (Wire n s)) (a : Fin n → L) :
    blockRank (jacobian (fun o => wirePolynomial P p (out o)) a) (outputsIn out S)ᶜ
      (inputsIn S) ≤ (forward p S).card :=
  Internal.blockRank_jacobian_le_forward P p S a out

/-- **The backward Jacobian consequence, for a program.** Symmetrically, the block of the
Jacobian of the outputs at `a`, from the inputs outside `S` to the outputs in `S`, has rank at
most `|backward S|`. -/
theorem blockRank_jacobian_le_backward_of_trace (p : Program σ n s)
    (out : Fin m → Wire n s) (S : Finset (Wire n s)) (a : Fin n → L) :
    blockRank (jacobian (fun o => wirePolynomial P p (out o)) a) (outputsIn out S)
      (inputsIn S)ᶜ ≤ (backward p S).card :=
  Internal.blockRank_jacobian_le_backward P p S a out

/-- **The Jacobian consequence, for a program.** The blocks of the Jacobian of the outputs at
`a`, from the inputs in `S` to the outputs outside `S` and from the other inputs to the outputs
in `S`, have ranks summing to at most `|forward S| + |backward S|`. -/
theorem blockRank_jacobian_add_blockRank_le_of_trace (p : Program σ n s)
    (out : Fin m → Wire n s) (S : Finset (Wire n s)) (a : Fin n → L) :
    blockRank (jacobian (fun o => wirePolynomial P p (out o)) a) (outputsIn out S)ᶜ
        (inputsIn S) +
      blockRank (jacobian (fun o => wirePolynomial P p (out o)) a) (outputsIn out S)
        (inputsIn S)ᶜ ≤
        (forward p S).card + (backward p S).card :=
  Internal.blockRank_jacobian_add_blockRank_le P p S a out

/-- **The forward Jacobian consequence.** For a circuit with polynomial gates, every set `S` of
its wires and every point `a`, the Jacobian `J` of the outputs at `a` satisfies
`rank J[O_T, X_S] ≤ |forward S|`. -/
theorem blockRank_jacobian_le_forward (c : Circuit σ n m) (S : Finset (Wire n c.size))
    (a : Fin n → L) :
    blockRank (jacobian (fun o => wirePolynomial P c.program (c.outputs o)) a)
      (outputsIn c.outputs S)ᶜ (inputsIn S) ≤ (forward c.program S).card :=
  Internal.blockRank_jacobian_le_forward P c.program S a c.outputs

/-- **The backward Jacobian consequence.** Symmetrically, for a circuit with polynomial gates,
`rank J[O_S, X_T] ≤ |backward S|`. -/
theorem blockRank_jacobian_le_backward (c : Circuit σ n m) (S : Finset (Wire n c.size))
    (a : Fin n → L) :
    blockRank (jacobian (fun o => wirePolynomial P c.program (c.outputs o)) a)
      (outputsIn c.outputs S) (inputsIn S)ᶜ ≤ (backward c.program S).card :=
  Internal.blockRank_jacobian_le_backward P c.program S a c.outputs

/-- **The Jacobian consequence.** For a circuit with polynomial gates, every set `S` of its
wires and every point `a`, the Jacobian `J` of the outputs at `a` satisfies
`rank J[O_T, X_S] + rank J[O_S, X_T] ≤ |forward S| + |backward S|`, where `X_S` and `X_T` are the
inputs in and outside `S`, and `O_S` and `O_T` the outputs carried in and outside `S`. -/
theorem blockRank_jacobian_add_blockRank_le (c : Circuit σ n m) (S : Finset (Wire n c.size))
    (a : Fin n → L) :
    blockRank (jacobian (fun o => wirePolynomial P c.program (c.outputs o)) a)
        (outputsIn c.outputs S)ᶜ (inputsIn S) +
      blockRank (jacobian (fun o => wirePolynomial P c.program (c.outputs o)) a)
        (outputsIn c.outputs S) (inputsIn S)ᶜ ≤
        (forward c.program S).card + (backward c.program S).card :=
  Internal.blockRank_jacobian_add_blockRank_le P c.program S a c.outputs

/-- **The Hessian consequence, for a program.** For every combination `∑ₒ μₒ fₒ` of the outputs,
the block of its Hessian at `a` between the inputs in `S` and the other inputs has rank at most
`|forward S| + |backward S|`. -/
theorem blockRank_hessian_le_of_trace (p : Program σ n s) (out : Fin m → Wire n s)
    (S : Finset (Wire n s)) (a : Fin n → L) (μ : Fin m → L) :
    blockRank (∑ o, μ o • hessian (wirePolynomial P p (out o)) a) (inputsIn S) (inputsIn S)ᶜ ≤
      (forward p S).card + (backward p S).card :=
  Internal.blockRank_hessian_le P p S a out μ

/-- **The Hessian consequence.** For a circuit with polynomial gates, every set `S` of its wires,
every point `a` and all coefficients `μ`, the Hessian `H = ∑ₒ μₒ ∇² fₒ (a)` of the combination
`∑ₒ μₒ fₒ` of the outputs satisfies `rank H[X_S, X_T] ≤ |forward S| + |backward S|`. -/
theorem blockRank_hessian_le (c : Circuit σ n m) (S : Finset (Wire n c.size)) (a : Fin n → L)
    (μ : Fin m → L) :
    blockRank (∑ o, μ o • hessian (wirePolynomial P c.program (c.outputs o)) a) (inputsIn S)
        (inputsIn S)ᶜ ≤
      (forward c.program S).card + (backward c.program S).card :=
  Internal.blockRank_hessian_le P c.program S a c.outputs μ

/-- **The unified first-and-second-order jet cut bound, for a program.** At every point `a` and
for every combination `H = ∑ₒ μₒ ∇² fₒ(a)` of the output Hessians, the combined block matrix
formed by `H[X_S, X_T]`, `J[O_T, X_S]ᵀ`, and `J[O_S, X_T]` has rank at most
`|forward S| + |backward S|`. -/
theorem rank_fromBlocks_hessian_jacobian_le_of_trace (p : Program σ n s)
    (out : Fin m → Wire n s) (S : Finset (Wire n s)) (a : Fin n → L) (μ : Fin m → L) :
    (Matrix.fromBlocks
      ((∑ o, μ o • hessian (wirePolynomial P p (out o)) a).submatrix
        (fun i : ↥(inputsIn S) => (i : Fin n)) (fun j : ↥(inputsIn S)ᶜ => (j : Fin n)))
      ((jacobian (fun o => wirePolynomial P p (out o)) a).submatrix
        (fun o : ↥(outputsIn out S)ᶜ => (o : Fin m))
        (fun i : ↥(inputsIn S) => (i : Fin n))).transpose
      ((jacobian (fun o => wirePolynomial P p (out o)) a).submatrix
        (fun o : ↥(outputsIn out S) => (o : Fin m))
        (fun j : ↥(inputsIn S)ᶜ => (j : Fin n)))
      0).rank ≤ (forward p S).card + (backward p S).card :=
  Internal.rank_fromBlocks_hessian_jacobian_le P p S a out μ

/-- **The unified first-and-second-order jet cut bound.** For a circuit with polynomial gates,
every set `S` of its wires, every point `a` and all coefficients `μ`, the combined block matrix
formed by `H[X_S, X_T]`, `J[O_T, X_S]ᵀ`, and `J[O_S, X_T]` has rank at most
`|forward S| + |backward S|`. -/
theorem rank_fromBlocks_hessian_jacobian_le (c : Circuit σ n m) (S : Finset (Wire n c.size))
    (a : Fin n → L) (μ : Fin m → L) :
    (Matrix.fromBlocks
      ((∑ o, μ o • hessian (wirePolynomial P c.program (c.outputs o)) a).submatrix
        (fun i : ↥(inputsIn S) => (i : Fin n)) (fun j : ↥(inputsIn S)ᶜ => (j : Fin n)))
      ((jacobian (fun o => wirePolynomial P c.program (c.outputs o)) a).submatrix
        (fun o : ↥(outputsIn c.outputs S)ᶜ => (o : Fin m))
        (fun i : ↥(inputsIn S) => (i : Fin n))).transpose
      ((jacobian (fun o => wirePolynomial P c.program (c.outputs o)) a).submatrix
        (fun o : ↥(outputsIn c.outputs S) => (o : Fin m))
        (fun j : ↥(inputsIn S)ᶜ => (j : Fin n)))
      0).rank ≤ (forward c.program S).card + (backward c.program S).card :=
  Internal.rank_fromBlocks_hessian_jacobian_le P c.program S a c.outputs μ

end Cut

end Algebraic.Cutwidth.MultiOutput.Taylor
