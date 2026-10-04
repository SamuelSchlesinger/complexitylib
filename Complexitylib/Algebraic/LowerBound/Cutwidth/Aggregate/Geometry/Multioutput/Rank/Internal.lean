/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Rank.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Nonlinear generators span all circuit outputs

Modulo affine primary functions, every affine gate is a linear combination of
earlier values. The conjunction gates therefore span every output in this quotient.
Independent output components force at least as many conjunction gates as outputs.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

private theorem bitValue_xor (a b : Bool) :
    bitValue (a ^^ b) = bitValue a + bitValue b := by
  cases a <;> cases b <;> decide

private theorem bitValue_and (a b : Bool) :
    bitValue (a && b) = bitValue a * bitValue b := by
  cases a <;> cases b <;> decide

private theorem bitValue_xorSum {r : ℕ} (x : Fin r → Bool) :
    bitValue (xorSum x) = ∑ i, bitValue (x i) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [xorSum, bitValue_xor, ih, Fin.sum_univ_succ]
    rfl

/-- A linear subspace containing constants, primary bits, and conjunction outputs
contains every gate function, including gates that reuse nonlinear values. -/
theorem gateValues_mem {n g : ℕ} (p : Program signature n g)
    (S : Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2))
    (constants : ∀ b : ZMod 2, (fun _ => b) ∈ S)
    (inputs : ∀ i, (fun x => bitValue (x i)) ∈ S)
    (conjunctions : ∀ i, (p.lines i).op.isConjunction = true →
      (fun x => bitValue (p.gateFunction interpretation i x)) ∈ S) :
    ∀ i, (fun x => bitValue (p.gateFunction interpretation i x)) ∈ S := by
  induction p with
  | empty => exact fun i => Fin.elim0 i
  | @gate g p line ih =>
    have old := ih (fun i hi => by
      have hc : ((p.gate line).lines i.castSucc).op.isConjunction = true := by
        simpa only [Program.lines_gate_castSucc, Line.mapWires] using hi
      simpa only [Program.gateFunction_gate_castSucc] using conjunctions i.castSucc hc)
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · cases line with
      | mk op wires =>
        cases op with
        | conjunction r polarity negated =>
          exact conjunctions (Fin.last g) (by
            simp [Program.lines_gate_last, Line.mapWires, Op.isConjunction])
        | affine r bias coefficient =>
          have wire (slot : Fin r) :
              (fun x => bitValue (p.wireFunction interpretation (wires slot) x)) ∈ S := by
            cases wires slot with
            | input j => exact inputs j
            | gate j => exact old j
          have member := S.add_mem (constants (bitValue bias))
            (S.sum_mem (t := Finset.univ)
              fun slot _ => S.smul_mem (bitValue (coefficient slot)) (wire slot))
          convert member using 1
          ext x
          simp only [Program.gateFunction_gate_last, Line.eval, interpretation,
            bitValue_xor, bitValue_xorSum, bitValue_and, Pi.add_apply,
            Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rfl
    · simpa only [Program.gateFunction_gate_castSucc] using old j

/-- Independent nonlinear output coordinates require distinct nonlinear generators. -/
theorem output_rank_le_conjunctionCount {n m : ℕ} (c : Circuit signature n m)
    (independent : NonaffineComponents (c.eval interpretation)) :
    m ≤ conjunctionCount c.program := by
  classical
  let q := (affineFunctions n).mkQ
  let generator : {i : Fin c.size // (c.program.lines i).op.isConjunction = true} →
      (((Fin n → Bool) → ZMod 2) ⧸ affineFunctions n) :=
    fun i => q (fun x => bitValue (c.program.gateFunction interpretation i x))
  let T := Submodule.span (ZMod 2) (Set.range generator)
  have killed (f : (Fin n → Bool) → ZMod 2) (hf : f ∈ affineFunctions n) :
      q f = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hf
  have constants (b : ZMod 2) : (fun _ : Fin n → Bool => b) ∈ T.comap q := by
    change q (fun _ => b) ∈ T
    rw [killed _ ⟨b, 0, by ext; simp⟩]
    exact T.zero_mem
  have inputs (i : Fin n) : (fun x => bitValue (x i)) ∈ T.comap q := by
    change q (fun x => bitValue (x i)) ∈ T
    rw [killed _ ⟨0, LinearMap.proj i, by ext; simp [bitVector]⟩]
    exact T.zero_mem
  have gates := gateValues_mem c.program (T.comap q) constants inputs (by
    intro i hi
    exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
  have outputs (i : Fin m) : q (fun x => bitValue (c.eval interpretation x i)) ∈ T := by
    change (fun x => bitValue
      (c.program.wireFunction interpretation (c.outputs i) x)) ∈ T.comap q
    cases c.outputs i with
    | input j => exact inputs j
    | gate j => exact gates j
  let f := q.comp (Fintype.linearCombination (ZMod 2)
    (fun i : Fin m => fun x => bitValue (c.eval interpretation x i)))
  have injective : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    apply independent w
    change q (∑ i, w i • fun x => bitValue (c.eval interpretation x i)) = 0 at hw
    have member := (Submodule.Quotient.mk_eq_zero (affineFunctions n)).mp hw
    convert member using 1
    ext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have range : f.range ≤ T := by
    rintro _ ⟨w, rfl⟩
    change q (∑ i, w i • fun x => bitValue (c.eval interpretation x i)) ∈ T
    rw [map_sum]
    apply T.sum_mem
    intro i _
    rw [map_smul]
    exact T.smul_mem _ (outputs i)
  calc
    m = Module.finrank (ZMod 2) f.range := by
      rw [LinearMap.finrank_range_of_inj injective]
      simp
    _ ≤ Module.finrank (ZMod 2) T := Submodule.finrank_mono range
    _ ≤ Fintype.card {i : Fin c.size //
        (c.program.lines i).op.isConjunction = true} := finrank_range_le_card generator
    _ = conjunctionCount c.program := Fintype.card_subtype _

end Algebraic.Aggregate.Geometry
