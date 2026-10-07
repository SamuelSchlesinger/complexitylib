/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.CascadeWord
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Exact Fourier circuits: circuit extensions

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/CircuitExtensions.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier

theorem Program.eval_original {n k : ℕ} (p : Program n k) (x : Fin n → ℂ)
    (i : Fin (n+1)) : p.eval x (Fin.castAdd k i) = (Fin.snoc x 0 : Fin (n+1) → ℂ) i := by
  induction p with
  | nil => rfl
  | @step k p g ih =>
      change (Fin.snoc (p.eval x) (g.eval (p.eval x)) : Fin (n+1+k+1) → ℂ)
        (Fin.castSucc (Fin.castAdd k i)) = _
      rw [Fin.snoc_castSucc]
      exact ih

/-- Run two scalar circuits on a shared input and concatenate their outputs. -/
def LinearDAG.fanout {n a b : ℕ} (C : LinearDAG n a) (D : LinearDAG n b) :
    LinearDAG n (a+b) where
  size := C.size + D.size
  program := C.program.append (Fin.castAdd C.size) D.program
  outputs := Fin.addCases (fun i => keepIndex (C.outputs i))
    (fun j => appendIndex (Fin.castAdd C.size) (D.outputs j))

@[simp] theorem LinearDAG.size_fanout {n a b : ℕ}
    (C : LinearDAG n a) (D : LinearDAG n b) : (C.fanout D).size = C.size+D.size := rfl

theorem LinearDAG.eval_fanout {n a b : ℕ}
    (C : LinearDAG n a) (D : LinearDAG n b) (x : Fin n → ℂ) :
    (C.fanout D).eval x = Fin.addCases (C.eval x) (D.eval x) := by
  have h := C.program.eval_append D.program (Fin.castAdd C.size) x x
    (fun i => C.program.eval_original x i)
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [LinearDAG.eval, LinearDAG.fanout, Fin.addCases_left] using h.1 (C.outputs j)
  · simpa only [LinearDAG.eval, LinearDAG.fanout, Fin.addCases_right] using h.2 (D.outputs j)

/-- Select or duplicate arbitrary existing inputs; these are wire names, not gates. -/
noncomputable def LinearDAG.withInputs {m n a : ℕ} (C : LinearDAG n a)
    (f : Fin n → Fin m) : LinearDAG m a := C.comp (.wires (fun i => (f i).castSucc))

@[simp] theorem LinearDAG.size_withInputs {m n a : ℕ} (C : LinearDAG n a)
    (f : Fin n → Fin m) : (C.withInputs f).size = C.size := by
  simp [LinearDAG.withInputs, LinearDAG.comp, LinearDAG.wires]

theorem LinearDAG.eval_withInputs {m n a : ℕ} (C : LinearDAG n a)
    (f : Fin n → Fin m) (x : Fin m → ℂ) : (C.withInputs f).eval x = C.eval (x ∘ f) := by
  rw [LinearDAG.withInputs, LinearDAG.eval_comp, LinearDAG.eval_wires]
  congr 1
  funext i
  simp only [Fin.snoc_castSucc, Function.comp_apply]

/-- Change the ordered output list without performing an arithmetic operation. -/
def LinearDAG.withOutputs {n a b : ℕ} (C : LinearDAG n a) (f : Fin b → Fin a) :
    LinearDAG n b := ⟨C.size, C.program, C.outputs ∘ f⟩

@[simp] theorem LinearDAG.eval_withOutputs {n a b : ℕ} (C : LinearDAG n a)
    (f : Fin b → Fin a) (x : Fin n → ℂ) : (C.withOutputs f).eval x = C.eval x ∘ f := rfl

/-- One butterfly for each of m pairs: charge m scalar multiplications, m additions,
and m subtractions, retaining the scaled terms for both output signs. -/
def LinearDAG.butterflies {n m : ℕ} (C : LinearDAG n (m+m)) (c : Fin m → ℂ) :
    LinearDAG n (m+m) where
  size := (C.size + m) + (m+m)
  program :=
    let p := C.program.emit (fun i => Gate.scale (c i) (C.outputs (Fin.natAdd m i)))
    p.emit (Fin.addCases
      (fun i => Gate.add (keepIndex (C.outputs (Fin.castAdd m i))) (gateIndex i))
      (fun i => Gate.sub (keepIndex (C.outputs (Fin.castAdd m i))) (gateIndex i)))
  outputs := gateIndex

theorem LinearDAG.eval_butterflies {n m : ℕ} (C : LinearDAG n (m+m))
    (c : Fin m → ℂ) (x : Fin n → ℂ) :
    (C.butterflies c).eval x = Fin.addCases
      (fun i => C.eval x (Fin.castAdd m i) + c i * C.eval x (Fin.natAdd m i))
      (fun i => C.eval x (Fin.castAdd m i) - c i * C.eval x (Fin.natAdd m i)) := by
  let gs : Fin m → Gate (n+1+C.size) := fun i =>
    Gate.scale (c i) (C.outputs (Fin.natAdd m i))
  let gb : Fin (m+m) → Gate (n+1+(C.size+m)) := Fin.addCases
    (fun i => Gate.add (keepIndex (C.outputs (Fin.castAdd m i))) (gateIndex i))
    (fun i => Gate.sub (keepIndex (C.outputs (Fin.castAdd m i))) (gateIndex i))
  have hs := C.program.eval_emit gs x
  have hb := (C.program.emit gs).eval_emit gb x
  funext i
  change (C.program.emit gs |>.emit gb).eval x (gateIndex i) = _
  rw [hb.2]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [gb, Fin.addCases_left, Gate.eval, hs.1, hs.2, gs]
    rfl
  · simp only [gb, Fin.addCases_right, Gate.eval, hs.1, hs.2, gs]
    rfl

end ExactFourier

end

section
/- Finite-index wrappers for the exact charged DAG model. These are used for the
state-clearing tensor-axis maps in the cascade and coefficient boundary cost. -/
namespace ExactFourier
open scoped BigOperators Kronecker

/-- A scalar circuit whose finite input and output coordinates have named types. -/
structure TypedDAG (ι κ : Type) [Fintype ι] [Fintype κ] where
  /-- The underlying scalar circuit after enumerating the coordinate types. -/
  circuit : LinearDAG (Fintype.card ι) (Fintype.card κ)

namespace TypedDAG
variable {ι κ τ υ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]

/-- The number of charged scalar gates in the underlying circuit. -/
abbrev size (C : TypedDAG ι κ) : ℕ := C.circuit.size
/-- Evaluate the underlying circuit and restore the named output coordinates. -/
noncomputable def eval (C : TypedDAG ι κ) (x : ι → ℂ) : κ → ℂ :=
  fun j => C.circuit.eval (x ∘ (Fintype.equivFin ι).symm) (Fintype.equivFin κ j)

/-- Feed the outputs of `C` into `D`, retaining both circuits' gates. -/
noncomputable def comp (D : TypedDAG κ τ) (C : TypedDAG ι κ) : TypedDAG ι τ :=
  ⟨D.circuit.comp C.circuit⟩
@[simp] theorem size_comp (D : TypedDAG κ τ) (C : TypedDAG ι κ) :
    (D.comp C).size = C.size + D.size := rfl
@[simp] theorem eval_comp (D : TypedDAG κ τ) (C : TypedDAG ι κ) (x : ι → ℂ) :
    (D.comp C).eval x = D.eval (C.eval x) := by
  funext j
  simp [eval, comp, LinearDAG.eval_comp, Function.comp_def]

/-- Relabel or duplicate the input coordinates without adding gates. -/
noncomputable def inputs (C : TypedDAG ι κ) (f : ι → τ) : TypedDAG τ κ :=
  ⟨C.circuit.withInputs (fun i => Fintype.equivFin τ (f ((Fintype.equivFin ι).symm i)))⟩
@[simp] theorem size_inputs (C : TypedDAG ι κ) (f : ι → τ) :
    (C.inputs f).size = C.size := LinearDAG.size_withInputs _ _
@[simp] theorem eval_inputs (C : TypedDAG ι κ) (f : ι → τ) (x : τ → ℂ) :
    (C.inputs f).eval x = C.eval (x ∘ f) := by
  funext j
  simp [eval, inputs, LinearDAG.eval_withInputs, Function.comp_def]

/-- Select, reorder, or duplicate output coordinates without adding gates. -/
noncomputable def outputs (C : TypedDAG ι κ) (f : τ → κ) : TypedDAG ι τ :=
  ⟨C.circuit.withOutputs (fun i => Fintype.equivFin κ (f ((Fintype.equivFin τ).symm i)))⟩
@[simp] theorem size_outputs (C : TypedDAG ι κ) (f : τ → κ) :
    (C.outputs f).size = C.size := rfl
@[simp] theorem eval_outputs (C : TypedDAG ι κ) (f : τ → κ) (x : ι → ℂ) :
    (C.outputs f).eval x = C.eval x ∘ f := by
  funext j
  simp [eval, outputs, LinearDAG.eval_withOutputs, Function.comp_def]

/-- Run two typed circuits on a shared input and retain both output vectors. -/
noncomputable def fanout (C : TypedDAG ι κ) (D : TypedDAG ι τ) : TypedDAG ι (κ ⊕ τ) :=
  ⟨(C.circuit.fanout D.circuit).withOutputs (fun i =>
    finSumFinEquiv ((Equiv.sumCongr (Fintype.equivFin κ) (Fintype.equivFin τ))
      ((Fintype.equivFin (κ ⊕ τ)).symm i)))⟩
@[simp] theorem size_fanout (C : TypedDAG ι κ) (D : TypedDAG ι τ) :
    (C.fanout D).size = C.size + D.size := rfl
@[simp] theorem eval_fanout (C : TypedDAG ι κ) (D : TypedDAG ι τ) (x : ι → ℂ) :
    (C.fanout D).eval x = Sum.elim (C.eval x) (D.eval x) := by
  funext j
  cases j <;> simp [eval, fanout, LinearDAG.eval_fanout, Function.comp_def]

/-- A gate-free selection of input wires and the source model's zero wire. -/
noncomputable def wires (f : κ → Option ι) : TypedDAG ι κ :=
  ⟨LinearDAG.wires (fun j => (f ((Fintype.equivFin κ).symm j)).elim
    (Fin.last _) (fun i => (Fintype.equivFin ι i).castSucc))⟩
@[simp] theorem size_wires (f : κ → Option ι) : (wires f).size = 0 := rfl
@[simp] theorem eval_wires (f : κ → Option ι) (x : ι → ℂ) :
    (wires f).eval x = fun j => (f j).elim 0 x := by
  funext j
  simp only [eval, wires, LinearDAG.eval_wires, Equiv.symm_apply_apply]
  cases f j <;> simp

/-- Compute an arbitrary matrix by explicitly scaling and summing its entries. -/
noncomputable def matrix (A : Matrix κ ι ℂ) : TypedDAG ι κ :=
  ⟨LinearDAG.matrix _ _ (Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin ι) A)⟩
@[simp] theorem size_matrix (A : Matrix κ ι ℂ) :
    (matrix A).size = 2 * Fintype.card κ * Fintype.card ι := LinearDAG.size_matrix _
@[simp] theorem eval_matrix (A : Matrix κ ι ℂ) (x : ι → ℂ) :
    (matrix A).eval x = A.mulVec x := by
  funext j
  simp only [eval, matrix, LinearDAG.eval_matrix, Matrix.mulVec, dotProduct,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Function.comp_apply]
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => A j i * x i)

/-- Multiply each coordinate by its specified scalar using one gate per coordinate. -/
noncomputable def scale (c : κ → ℂ) : TypedDAG κ κ :=
  ⟨LinearDAG.layer (fun i => .scale (c ((Fintype.equivFin κ).symm i)) i.castSucc)⟩
@[simp] theorem size_scale (c : κ → ℂ) : (scale c).size = Fintype.card κ := by
  simp [size, scale, LinearDAG.layer]
@[simp] theorem eval_scale (c : κ → ℂ) (x : κ → ℂ) :
    (scale c).eval x = fun i => c i * x i := by
  funext i
  simp [eval, scale, LinearDAG.eval_layer, Gate.eval, Function.comp_def]

/-- Add two vectors coordinatewise using one addition gate per output. -/
noncomputable def addPair : TypedDAG (κ ⊕ κ) κ :=
  ⟨LinearDAG.layer (fun i => .add
    (Fintype.equivFin (κ ⊕ κ) (Sum.inl ((Fintype.equivFin κ).symm i))).castSucc
    (Fintype.equivFin (κ ⊕ κ) (Sum.inr ((Fintype.equivFin κ).symm i))).castSucc)⟩
@[simp] theorem size_addPair : (addPair (κ := κ)).size = Fintype.card κ := by
  simp [size, addPair, LinearDAG.layer]
@[simp] theorem eval_addPair (x : κ ⊕ κ → ℂ) :
    (addPair (κ := κ)).eval x = fun i => x (Sum.inl i) + x (Sum.inr i) := by
  funext i
  simp [eval, addPair, LinearDAG.eval_layer, Gate.eval, Function.comp_def]

/-- Stack a finite list of circuits that share their input and output types. -/
noncomputable def stackFin : (n : ℕ) → (Fin n → TypedDAG ι κ) → TypedDAG ι (Fin n × κ)
  | 0, _ => wires (fun _ => none)
  | n+1, C => ((C 0).fanout (stackFin n (fun i => C i.succ))).outputs
      (fun x => Fin.cases (Sum.inl x.2) (fun i => Sum.inr (i,x.2)) x.1)

theorem size_stackFin (n : ℕ) (C : Fin n → TypedDAG ι κ) :
    (stackFin n C).size = ∑ i, (C i).size := by
  induction n with
  | zero => simp [stackFin]
  | succ n ih => simp [stackFin, ih, Fin.sum_univ_succ]

theorem eval_stackFin (n : ℕ) (C : Fin n → TypedDAG ι κ) (x : ι → ℂ) :
    (stackFin n C).eval x = fun j => (C j.1).eval x j.2 := by
  induction n with
  | zero => funext ⟨i,j⟩; exact Fin.elim0 i
  | succ n ih =>
    funext ⟨i,j⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [stackFin, ih]

/-- Stack a finite family of circuits that share the same input. -/
noncomputable def stack (C : τ → TypedDAG ι κ) : TypedDAG ι (τ × κ) :=
  (stackFin (Fintype.card τ) (fun i => C ((Fintype.equivFin τ).symm i))).outputs
    (fun x => (Fintype.equivFin τ x.1,x.2))
@[simp] theorem size_stack (C : τ → TypedDAG ι κ) :
    (stack C).size = ∑ i, (C i).size := by
  rw [stack, size_outputs, size_stackFin]
  exact (Fintype.equivFin τ).symm.sum_comp (fun i => (C i).size)
@[simp] theorem eval_stack (C : τ → TypedDAG ι κ) (x : ι → ℂ) :
    (stack C).eval x = fun j => (C j.1).eval x j.2 := by
  simp [stack, eval_stackFin, Function.comp_def]

/-- Apply independent copies of a circuit to the indexed input vectors. -/
noncomputable def parallel (C : TypedDAG ι κ) (τ : Type) [Fintype τ] :
    TypedDAG (τ × ι) (τ × κ) := stack (fun t => C.inputs (fun i => (t,i)))
@[simp] theorem size_parallel (C : TypedDAG ι κ) :
    (C.parallel τ).size = Fintype.card τ * C.size := by simp [parallel]
@[simp] theorem eval_parallel (C : TypedDAG ι κ) (x : τ × ι → ℂ) :
    (C.parallel τ).eval x = fun j => C.eval (fun i => x (j.1,i)) j.2 := by
  simp [parallel, Function.comp_def]

/-- Compute the tensor product of two linear circuits by acting on each coordinate axis. -/
noncomputable def tensor (C : TypedDAG ι κ) (D : TypedDAG τ υ) :
    TypedDAG (ι × τ) (κ × υ) :=
  (((C.parallel υ).inputs Prod.swap).comp (D.parallel ι)).outputs Prod.swap
@[simp] theorem size_tensor (C : TypedDAG ι κ) (D : TypedDAG τ υ) :
    (C.tensor D).size = Fintype.card ι * D.size + Fintype.card υ * C.size := by
  simp [tensor]

theorem eval_tensor (C : TypedDAG ι κ) (D : TypedDAG τ υ)
    (A : Matrix κ ι ℂ) (B : Matrix υ τ ℂ)
    (hC : ∀ x, C.eval x = A.mulVec x) (hD : ∀ x, D.eval x = B.mulVec x)
    (x : ι × τ → ℂ) : (C.tensor D).eval x = (A ⊗ₖ B).mulVec x := by
  funext j
  simp only [tensor, eval_outputs, eval_comp, eval_inputs, eval_parallel, Function.comp_apply,
    Prod.swap, hC, hD, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end TypedDAG
end ExactFourier

end

section
/- Charged scalar DAGs for the tensor-axis local maps used in the cascade. -/
namespace ExactFourier
open scoped Kronecker
namespace TypedDAG
variable {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ]

/-- Add the outputs of two circuits acting on disjoint input blocks. -/
noncomputable def blockCols (C : TypedDAG ι κ) (D : TypedDAG τ κ) : TypedDAG (ι ⊕ τ) κ :=
  addPair.comp ((C.inputs Sum.inl).fanout (D.inputs Sum.inr))
@[simp] theorem size_blockCols (C : TypedDAG ι κ) (D : TypedDAG τ κ) :
    (blockCols C D).size = C.size+D.size+Fintype.card κ := by simp [blockCols]
theorem eval_blockCols (C : TypedDAG ι κ) (D : TypedDAG τ κ)
    (A : Matrix κ ι ℂ) (B : Matrix κ τ ℂ)
    (hC : ∀ x, C.eval x=A.mulVec x) (hD : ∀ x, D.eval x=B.mulVec x) (x : ι ⊕ τ → ℂ) :
    (blockCols C D).eval x = (Matrix.fromCols A B).mulVec x := by
  rw [blockCols,eval_comp,eval_fanout,eval_inputs,eval_inputs,eval_addPair,hC,hD,
    Matrix.fromCols_mulVec]
  rfl

/-- Scale every output of a circuit by one fixed complex scalar. -/
noncomputable def scalar (c : ℂ) (C : TypedDAG ι κ) : TypedDAG ι κ :=
  (scale (fun _ => c)).comp C
@[simp] theorem size_scalar (c : ℂ) (C : TypedDAG ι κ) :
    (scalar c C).size = C.size+Fintype.card κ := by simp [scalar]
theorem eval_scalar (c : ℂ) (C : TypedDAG ι κ) (A : Matrix κ ι ℂ)
    (hC : ∀ x, C.eval x=A.mulVec x) (x : ι → ℂ) :
    (scalar c C).eval x = (c • A).mulVec x := by
  simp only [scalar,eval_comp,eval_scale,hC,Matrix.smul_mulVec]
  rfl

/-- The identity circuit, using only direct input wires. -/
noncomputable def identity : TypedDAG ι ι := wires some
@[simp] theorem size_identity : (identity (ι := ι)).size=0 := rfl
@[simp] theorem eval_identity (x : ι → ℂ) : (identity (ι := ι)).eval x = x := by simp [identity]

variable {α : Type} [Fintype α] [DecidableEq α]
/-- A circuit for a tensor power, obtained by repeatedly tensoring matrix circuits. -/
noncomputable def tensorPower (A : Matrix α α ℂ) : (k : ℕ) → TypedDAG (TensorAxis.Space α k)
    (TensorAxis.Space α k)
  | 0 => identity
  | k+1 => (tensorPower A k).tensor (matrix A)

theorem eval_tensorPower
    {α : Type} [Fintype α]  (A : Matrix α α ℂ) (k : ℕ) (x : TensorAxis.Space α k → ℂ) :
    (tensorPower A k).eval x = (TensorAxis.power A k).mulVec x := by
  induction k with
  | zero => simp [tensorPower,TensorAxis.power]
  | succ k ih =>
    exact eval_tensor _ _ _ _ ih (eval_matrix A) x

omit [DecidableEq α] in
theorem size_tensorPower (A : Matrix α α ℂ) (k : ℕ) :
    (tensorPower A k).size = 2*Fintype.card α*k*Fintype.card α^k := by
  induction k with
  | zero => simp [tensorPower]
  | succ k ih =>
    rw [tensorPower,size_tensor,ih,size_matrix,TensorAxis.card_space,pow_succ]
    ring

end TypedDAG
end ExactFourier

end

section
/- Exact charged reconstruction of coefficient vectors from finitely many
scalar evaluations. All interpolation constants are prechosen and charged;
no pole avoidance or analytic limit is used. -/
namespace ExactFourier
open scoped BigOperators
namespace PolynomialDAG
variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- Distinct complex interpolation nodes given by the natural numbers below `m`. -/
noncomputable def nodes (m : ℕ) (i : Fin m) : ℂ := i.val
/-- Coefficients of the Lagrange basis at the chosen interpolation nodes. -/
noncomputable def weights (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => (Lagrange.basis Finset.univ (nodes m) j).coeff i.val

theorem nodes_injective (m : ℕ) : Function.Injective (nodes m) := by
  intro i j h
  apply Fin.ext
  dsimp [nodes] at h
  exact_mod_cast h

theorem coeff_interpolate (f : Polynomial ℂ) (m : ℕ) (hf : f.natDegree < m) (i : Fin m) :
    f.coeff i.val = ∑ j, weights m i j * f.eval (nodes m j) := by
  have hd : f.degree < (Finset.univ : Finset (Fin m)).card := by
    simp only [Finset.card_univ,Fintype.card_fin]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hf)
  have h := congrArg (fun q : Polynomial ℂ => q.coeff i.val)
    (Lagrange.eq_interpolate (nodes_injective m).injOn hd)
  simpa [Lagrange.interpolate_apply,weights,Polynomial.finsetSum_coeff,mul_comm] using h

/-- Stack the first `t` coefficient matrices as successive output blocks. -/
noncomputable def coefficients (A : Matrix κ ι (Polynomial ℂ)) (t : ℕ) : Matrix (Fin t × κ) ι ℂ :=
  fun i j => (A i.2 j).coeff i.1.val
/-- Evaluate each entry of a polynomial matrix at the same complex number. -/
noncomputable def evalMatrix (A : Matrix κ ι (Polynomial ℂ)) (z : ℂ) : Matrix κ ι ℂ :=
  A.map (Polynomial.evalRingHom z)

/-- Recover coefficient outputs by interpolating circuits at the chosen nodes. -/
noncomputable def reconstruct (m : ℕ) (C : Fin m → TypedDAG ι κ) : TypedDAG ι (Fin m × κ) :=
  ((((TypedDAG.matrix (weights m)).parallel κ).inputs Prod.swap).comp
    (TypedDAG.stackFin m C)).outputs Prod.swap

theorem size_reconstruct (m : ℕ) (C : Fin m → TypedDAG ι κ) :
    (reconstruct m C).size = (∑ i, (C i).size) + 2*m*m*Fintype.card κ := by
  simp [reconstruct,TypedDAG.size_stackFin]
  ring

theorem eval_reconstruct (A : Matrix κ ι (Polynomial ℂ)) (m : ℕ)
    (hA : ∀ i j, (A i j).natDegree < m) (C : Fin m → TypedDAG ι κ)
    (hC : ∀ j x, (C j).eval x = (evalMatrix A (nodes m j)).mulVec x) (x : ι → ℂ) :
    (reconstruct m C).eval x = (coefficients A m).mulVec x := by
  funext ⟨i,u⟩
  simp only [reconstruct,TypedDAG.eval_outputs,TypedDAG.eval_comp,TypedDAG.eval_inputs,
    TypedDAG.eval_parallel,TypedDAG.eval_matrix,TypedDAG.eval_stackFin,Function.comp_apply,
    Prod.swap,hC,Matrix.mulVec,dotProduct]
  change (∑ j, weights m i j * ∑ v, evalMatrix A (nodes m j) u v * x v) =
    ∑ v, (A u v).coeff i.val * x v
  simp_rw [coeff_interpolate _ m (hA _ _) i,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro j hj
  simp [evalMatrix,mul_assoc]

/-- Extend coefficient vectors with zero wires, or truncate them to the requested length. -/
noncomputable def pad (m t : ℕ) : TypedDAG (Fin m × κ) (Fin t × κ) :=
  TypedDAG.wires (fun i => if h : i.1.val < m then some (⟨i.1.val,h⟩,i.2) else none)
@[simp] theorem size_pad (m t : ℕ) : (pad (κ := κ) m t).size=0 := rfl

theorem eval_pad (A : Matrix κ ι (Polynomial ℂ)) (m t : ℕ)
    (hA : ∀ i j, (A i j).natDegree < m) (x : ι → ℂ) :
    (pad m t).eval ((coefficients A m).mulVec x) = (coefficients A t).mulVec x := by
  funext ⟨i,u⟩
  rw [pad,TypedDAG.eval_wires]
  by_cases hi : i.val < m
  · simp [hi,coefficients,Matrix.mulVec,dotProduct]
  · simp only [hi]
    symm
    apply Finset.sum_eq_zero
    intro v hv
    have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hA u v)
      (Nat.le_of_not_gt hi))
    simp [coefficients,hz]

theorem exists_coefficients (A : Matrix κ ι (Polynomial ℂ)) (m t s : ℕ)
    (hA : ∀ i j, (A i j).natDegree < m)
    (hC : ∀ z : ℂ, ∃ C : TypedDAG ι κ, C.size ≤ s ∧ ∀ x, C.eval x=(evalMatrix A z).mulVec x) :
    ∃ C : TypedDAG ι (Fin t × κ), C.size ≤ m*s+2*m*m*Fintype.card κ ∧
      ∀ x, C.eval x=(coefficients A t).mulVec x := by
  classical
  choose C hs he using fun j : Fin m => hC (nodes m j)
  refine ⟨(pad m t).comp (reconstruct m C),?_,?_⟩
  · rw [TypedDAG.size_comp,size_pad,Nat.add_zero,size_reconstruct]
    apply Nat.add_le_add_right
    simpa using (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hs j))
  · intro x
    rw [TypedDAG.eval_comp,eval_reconstruct A m hA C he,eval_pad A m t hA]

end PolynomialDAG
end ExactFourier

end

end Complexity
