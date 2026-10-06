/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Internal.Charge
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Ordering
public import Mathlib.Data.Matrix.Basis

/-!
# The terminals of matrix multiplication

* **Distinct terminals** (`terminal_injective`). The `3 n²` terminals lie on distinct wires,
  where `E i k` is the matrix unit: the outputs `C i k` and `C i' k'` differ on `A = 1`,
  `B = E i k`; an input `A i j` and an output differ on `A = E i j`, `B = 0`; an input `B j k`
  and an output differ on `A = 0`, `B = E j k`.
* **One component** (`mem_component_of_trace`). The component of the output `C 0 0` is closed,
  so it is crossed by no signal, and by `apply_eq_zero_of_closed_of_trace` the linear maps
  obtained by fixing one factor send vectors supported inside it to vectors vanishing outside
  it, and vice versa. With the factor `B = E j k` the unit vector at `A i j` moves the output
  `C i k`, and with `A = E i j` the unit vector at `B j k` moves `C i k`; spreading from
  `C 0 0`, the component holds the row `A 0 ·`, the row `C 0 ·`, all of `B`, all of `C` and all
  of `A`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.MatMul.Internal

open Algebraic.Cutwidth.MultiOutput.Internal

open SingleCut

variable {σ : Signature} {n s : Nat}

section Values

variable {F : Type*} [Field F]

theorem shiftLeft_single_single (i j k : Fin n) :
    shiftLeft (Matrix.single j k (1 : F)) (Pi.single (matMulLeft n i j) 1)
      (matMulOutput n i k) = 1 := by
  rw [shiftLeft_output]
  simp [Pi.single_apply, matMulLeft_inj, Matrix.single_apply]

theorem shiftRight_single_single (i j k : Fin n) :
    shiftRight (Matrix.single i j (1 : F)) (Pi.single (matMulRight n j k) 1)
      (matMulOutput n i k) = 1 := by
  rw [shiftRight_output]
  simp [Pi.single_apply, matMulRight_inj, Matrix.single_apply]

variable {p : Program σ (n * n + n * n) s} {I : Interpretation σ F}
  {out : Fin (n * n) → Wire (n * n + n * n) s}

/-- Distinct outputs lie on distinct wires. -/
theorem out_injective (hf : ∀ z o, p.trace I z (out o) = matMul n z o) :
    Function.Injective out := by
  intro o o' h
  rw [output_eq o, output_eq o'] at h ⊢
  set i := (finProdFinEquiv.symm o).1
  set k := (finProdFinEquiv.symm o).2
  set i' := (finProdFinEquiv.symm o').1
  set k' := (finProdFinEquiv.symm o').2
  have hv := (hf (matMulInput 1 (Matrix.single i k (1 : F))) (matMulOutput n i k)).symm.trans
    ((congrArg _ h).trans (hf _ (matMulOutput n i' k')))
  rw [matMul_matMulInput, matMul_matMulInput, one_mul, Matrix.single_apply,
    Matrix.single_apply, ite_eq_left ⟨rfl, rfl⟩] at hv
  by_contra hne
  rw [ite_eq_right fun h' => hne (by rw [h'.1, h'.2])] at hv
  exact one_ne_zero hv

/-- No output lies on the wire of an input `A i j`. -/
theorem out_ne_termA (hf : ∀ z o, p.trace I z (out o) = matMul n z o) (i j i' k' : Fin n) :
    out (matMulOutput n i' k') ≠ Wire.input (matMulLeft n i j) := by
  intro h
  have hv := (hf (matMulInput (Matrix.single i j (1 : F)) 0) (matMulOutput n i' k')).symm
  rw [h, Program.trace_input, matMul_matMulInput, mul_zero, Matrix.zero_apply,
    matMulInput_left, Matrix.single_apply, ite_eq_left ⟨rfl, rfl⟩] at hv
  exact zero_ne_one hv

/-- No output lies on the wire of an input `B j k`. -/
theorem out_ne_termB (hf : ∀ z o, p.trace I z (out o) = matMul n z o) (j k i' k' : Fin n) :
    out (matMulOutput n i' k') ≠ Wire.input (matMulRight n j k) := by
  intro h
  have hv := (hf (matMulInput 0 (Matrix.single j k (1 : F))) (matMulOutput n i' k')).symm
  rw [h, Program.trace_input, matMul_matMulInput, zero_mul, Matrix.zero_apply,
    matMulInput_right, Matrix.single_apply, ite_eq_left ⟨rfl, rfl⟩] at hv
  exact zero_ne_one hv

/-- **Distinct terminals.** The inputs `A i j`, `B j k` and the outputs `C i k` lie on `3 n²`
distinct wires. -/
theorem terminal_injective (hf : ∀ z o, p.trace I z (out o) = matMul n z o) :
    Function.Injective
      (Sum.elim (matMulTermA n s) (Sum.elim (matMulTermB n s) (matMulTermC out))) := by
  have hout := out_injective hf
  rintro (⟨i, j⟩ | ⟨j, k⟩ | ⟨i, k⟩) (⟨i', j'⟩ | ⟨j', k'⟩ | ⟨i', k'⟩) h
  all_goals simp only [Sum.elim_inl, Sum.elim_inr, matMulTermA, matMulTermB, matMulTermC] at h
  · injection h with h
    rw [matMulLeft_inj] at h
    rw [h.1, h.2]
  · injection h with h
    exact absurd h (matMulLeft_ne_matMulRight _ _ _ _)
  · exact absurd h.symm (out_ne_termA hf _ _ _ _)
  · injection h with h
    exact absurd h.symm (matMulLeft_ne_matMulRight _ _ _ _)
  · injection h with h
    rw [matMulRight_inj] at h
    rw [h.1, h.2]
  · exact absurd h.symm (out_ne_termB hf _ _ _ _)
  · exact absurd h (out_ne_termA hf _ _ _ _)
  · exact absurd h (out_ne_termB hf _ _ _ _)
  · have := matMulOutput_inj.mp (hout h)
    rw [this.1, this.2]

end Values

/-! ## One component -/

section Component

variable {F : Type*} [Field F]
  {p : Program σ (n * n + n * n) s} {I : Interpretation σ F}
  {out : Fin (n * n) → Wire (n * n + n * n) s}

/-- A unit vector is supported on any set containing its coordinate. -/
theorem single_supported {N : Nat} {x : Fin N} {P : Finset (Fin N)} (hx : x ∈ P) :
    ∀ y, y ∉ P → (Pi.single x (1 : F) : Fin N → F) y = 0 := fun y hy =>
  Pi.single_eq_of_ne (fun h : y = x => hy (h ▸ hx)) _

/-- **All terminals lie in one component.** If the wires `out` of a program over any field carry
`matMul n` and `n ≥ 1`, the component of the output `C 0 0` contains every input and every
output. -/
theorem mem_component_of_trace (hn : 0 < n) (hf : ∀ z o, p.trace I z (out o) = matMul n z o) :
    (∀ x, Wire.input x ∈ component p (out (matMulOutput n ⟨0, hn⟩ ⟨0, hn⟩))) ∧
      ∀ o, out o ∈ component p (out (matMulOutput n ⟨0, hn⟩ ⟨0, hn⟩)) := by
  set z₀ : Fin n := ⟨0, hn⟩
  set W := component p (out (matMulOutput n z₀ z₀)) with hW
  have hclosed := component_closed p (out (matMulOutput n z₀ z₀))
  have hfwd := forward_eq_empty_of_closed hclosed
  have hbwd := backward_eq_empty_of_closed hclosed
  have hleft := fun B₀ : Matrix (Fin n) (Fin n) F => apply_eq_zero_of_closed_of_trace p I out hf W
    (leftCoords n) (matMulInput 0 B₀) (shiftLeft B₀)
    (fun z z' hz hz' => matMul_sub_left B₀ z z' hz hz') hfwd hbwd
  have hright := fun A₀ : Matrix (Fin n) (Fin n) F => apply_eq_zero_of_closed_of_trace p I out hf
    W (rightCoords n) (matMulInput A₀ 0) (shiftRight A₀)
    (fun z z' hz hz' => matMul_sub_right A₀ z z' hz hz') hfwd hbwd
  have memOut : ∀ i k, matMulOutput n i k ∈ outputsIn out W ↔ out (matMulOutput n i k) ∈ W :=
    fun i k => by simp [outputsIn]
  have hC₀ : matMulOutput n z₀ z₀ ∈ outputsIn out W := (memOut _ _).mpr (mem_component_self _ _)
  -- The row `A 0 ·`.
  have hA₀ : ∀ j, matMulLeft n z₀ j ∈ inputsIn W := by
    intro j
    by_contra hj
    have h := (hleft (Matrix.single j z₀ 1)).2 _
      (single_supported (Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hj,
        matMulLeft_mem_leftCoords _ _⟩)) _ hC₀
    rw [shiftLeft_single_single] at h
    exact one_ne_zero h
  -- The row `C 0 ·`.
  have hC : ∀ k, matMulOutput n z₀ k ∈ outputsIn out W := by
    intro k
    by_contra hk
    have h := (hleft (Matrix.single z₀ k 1)).1 _
      (single_supported (Finset.mem_inter.mpr ⟨hA₀ z₀, matMulLeft_mem_leftCoords _ _⟩)) _ hk
    rw [shiftLeft_single_single] at h
    exact one_ne_zero h
  -- All of `B`.
  have hB : ∀ j k, matMulRight n j k ∈ inputsIn W := by
    intro j k
    by_contra hjk
    have h := (hright (Matrix.single z₀ j 1)).2 _
      (single_supported (Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hjk,
        matMulRight_mem_rightCoords _ _⟩)) _ (hC k)
    rw [shiftRight_single_single] at h
    exact one_ne_zero h
  -- All of `C`.
  have hCall : ∀ i k, matMulOutput n i k ∈ outputsIn out W := by
    intro i k
    by_contra hik
    have h := (hright (Matrix.single i z₀ 1)).1 _
      (single_supported (Finset.mem_inter.mpr ⟨hB z₀ k, matMulRight_mem_rightCoords _ _⟩)) _ hik
    rw [shiftRight_single_single] at h
    exact one_ne_zero h
  -- All of `A`.
  have hA : ∀ i j, matMulLeft n i j ∈ inputsIn W := by
    intro i j
    by_contra hij
    have h := (hleft (Matrix.single j z₀ 1)).2 _
      (single_supported (Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hij,
        matMulLeft_mem_leftCoords _ _⟩)) _ (hCall i z₀)
    rw [shiftLeft_single_single] at h
    exact one_ne_zero h
  refine ⟨fun x => ?_, fun o => ?_⟩
  · rcases input_cases x with ⟨i, j, rfl⟩ | ⟨j, k, rfl⟩
    · exact mem_inputsIn.mp (hA i j)
    · exact mem_inputsIn.mp (hB j k)
  · rw [output_eq o]
    exact (memOut _ _).mp (hCall _ _)

end Component

end Algebraic.Cutwidth.MultiOutput.MatMul.Internal
