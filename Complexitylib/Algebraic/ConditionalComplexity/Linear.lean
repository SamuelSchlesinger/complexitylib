/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.ConditionalComplexity
public import Complexitylib.Algebraic.Complexity.RelativeSupport
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Two

/-!
# Exact complexity of linear targets with linear helpers

Over `ZMod 2`, a nonzero linear form is computable from a set of linear
sources exactly when its coefficient vector lies in their span. A binary
circuit must touch enough sources, even if its gates are nonlinear. If XOR
can be computed in one gate, a minimum-weight representation gives a matching
XOR tree. All gates are charged one, including any constant gates.
-/

@[expose] public section

namespace Algebraic.ConditionalComplexity.Linear

open scoped Matrix

noncomputable section

/-- Hamming weight of a coefficient vector. -/
def weight (coefficients : Fin n → ZMod 2) : Nat :=
  (Finset.univ.filter fun i => coefficients i ≠ 0).card

/-- The family of linear forms given by the rows of a coefficient matrix. -/
def forms (rows : Fin k → Fin n → K) [Semiring K] : Target K n k :=
  fun input i => rows i ⬝ᵥ input

private theorem dual_as_dotProduct {K : Type} [Field K]
    (functional : (Fin n → K) →ₗ[K] K) (vector : Fin n → K) :
    functional vector = vector ⬝ᵥ
      (fun i => functional (fun j => if i = j then 1 else 0)) := by
  simpa [dotProduct, smul_eq_mul] using functional.pi_apply_eq_sum_univ vector

/-- If selected linear forms determine another linear form, their
coefficient vectors span its coefficient vector. -/
theorem mem_span_of_sourceSupport {K : Type} [Field K]
    (target : Fin n → K) (rows : Fin k → Fin n → K) (selected : Finset (Fin k))
    (determines : SourceSupport (fun input (_ : Fin 1) => target ⬝ᵥ input)
      (forms rows) selected) :
    target ∈ Submodule.span K (Set.range fun i : selected => rows i) := by
  classical
  by_contra absent
  obtain ⟨functional, nonzero, vanishes⟩ := Submodule.exists_le_ker_of_notMem absent
  let input : Fin n → K := fun i => functional (fun j => if i = j then 1 else 0)
  have agrees : ∀ i ∈ selected, forms rows input i = forms rows 0 i := by
    intro i present
    have zero_value : functional (rows i) = 0 := vanishes
      (Submodule.subset_span ⟨⟨i, present⟩, rfl⟩)
    change rows i ⬝ᵥ input = rows i ⬝ᵥ 0
    rw [dotProduct_zero, ← dual_as_dotProduct functional]
    exact zero_value
  have equal := congrFun (determines input 0 agrees) 0
  apply nonzero
  rw [dual_as_dotProduct]
  simpa only [dotProduct_zero] using equal

private theorem binary_eq_one (value : ZMod 2) (nonzero : value ≠ 0) : value = 1 := by
  exact (by decide : ∀ value : ZMod 2, value ≠ 0 → value = 1) value nonzero

/-- A determining source subset yields a representation using no more
nonzero coefficients than the number of selected sources. -/
theorem exists_representation_of_sourceSupport
    (target : Fin n → ZMod 2) (rows : Fin k → Fin n → ZMod 2)
    (selected : Finset (Fin k))
    (determines : SourceSupport (fun input (_ : Fin 1) => target ⬝ᵥ input)
      (forms rows) selected) :
    ∃ coefficients : Fin k → ZMod 2,
      (∑ i, coefficients i • rows i = target) ∧ weight coefficients ≤ selected.card := by
  classical
  have member : target ∈ Submodule.span (ZMod 2) (Set.range fun i : selected => rows i) :=
    mem_span_of_sourceSupport (K := ZMod 2) target rows selected determines
  obtain ⟨coefficients, represents⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (ZMod 2)
      (v := fun i : selected => rows i)).mp member
  let extended : Fin k → ZMod 2 := fun i => if present : i ∈ selected then
    coefficients ⟨i, present⟩ else 0
  refine ⟨extended, ?_, ?_⟩
  · have restrict : ∑ i, extended i • rows i = ∑ i ∈ selected, extended i • rows i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ selected)
      intro i _ absent
      simp [extended, absent]
    rw [restrict, ← Finset.sum_coe_sort selected]
    simpa [extended] using represents
  · apply Finset.card_le_card
    intro i present
    by_contra absent
    simp [extended, absent] at present

private theorem exists_sum_circuit {σ : Signature} {U : Type} [AddCommMonoid U]
    (interpretation : Interpretation σ U) (addition : Circuit σ 2 1 1)
    (addition_eval : ∀ input, addition.eval interpretation input 0 = input 0 + input 1)
    (selected : Finset (Fin N)) (nonempty : selected.Nonempty) :
    ∃ gates, ∃ circuit : Circuit σ N gates 1,
      circuit.size + 1 = selected.card ∧
        ∀ input, circuit.eval interpretation input 0 = ∑ i ∈ selected, input i := by
  classical
  induction selected using Finset.induction_on with
  | empty => simp at nonempty
  | @insert i selected absent ih =>
      let projection := (Circuit.id σ N).mapOutputs (fun _ : Fin 1 => i)
      by_cases empty : selected = ∅
      · subst selected
        refine ⟨0, projection, by simp [Circuit.size], ?_⟩
        intro input
        simp [projection]
      · obtain ⟨gates, circuit, size, evaluates⟩ := ih (Finset.nonempty_iff_ne_empty.mpr empty)
        refine ⟨_, addition.comp (projection.parallel circuit), ?_, ?_⟩
        · simpa [Circuit.size, Finset.card_insert_of_notMem absent] using size
        · intro input
          rw [Circuit.eval_comp, addition_eval]
          simp only [Circuit.eval_parallel]
          change projection.eval interpretation input 0 + circuit.eval interpretation input 0 = _
          simp [projection, evaluates, Finset.sum_insert absent]

/-- A nonzero represented linear target has an XOR implementation with one
fewer gates than the number of nonzero representation coefficients. -/
theorem relativeGateComplexity_le_weight
    (interpretation : Interpretation σ (ZMod 2)) (addition : Circuit σ 2 1 1)
    (addition_eval : ∀ input, addition.eval interpretation input 0 = input 0 + input 1)
    (target : Fin n → ZMod 2) (nonzero : target ≠ 0)
    (rows : Fin k → Fin n → ZMod 2) (coefficients : Fin k → ZMod 2)
    (represents : ∑ i, coefficients i • rows i = target) :
    Circuit.relativeGateComplexity interpretation
      (fun input (_ : Fin 1) => target ⬝ᵥ input) (forms rows) ≤
        ((weight coefficients - 1 : Nat) : ℕ∞) := by
  let selected := Finset.univ.filter fun i => coefficients i ≠ 0
  have nonempty : selected.Nonempty := by
    by_contra empty
    have zero_coefficients : ∀ i, coefficients i = 0 := by
      simpa [selected, Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] using empty
    apply nonzero
    rw [← represents]
    simp [zero_coefficients]
  obtain ⟨gates, circuit, size, evaluates⟩ :=
    exists_sum_circuit interpretation addition addition_eval selected nonempty
  have computes : circuit.ComputesFrom interpretation
      (fun input (_ : Fin 1) => target ⬝ᵥ input) (forms rows) := by
    intro input
    funext output
    have output_zero : output = 0 := Subsingleton.elim _ _
    subst output
    change circuit.eval interpretation (forms rows input) 0 = target ⬝ᵥ input
    rw [evaluates, ← represents, sum_dotProduct]
    simp only [selected, Finset.sum_filter, smul_dotProduct, forms, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases zero : coefficients i = 0
    · simp [zero]
    · simp [binary_eq_one _ zero]
  have bound := Circuit.relativeCostComplexity_le OperationCost.unit computes
  have size_eq : circuit.size = weight coefficients - 1 := by
    change circuit.size + 1 = weight coefficients at size
    omega
  simpa [Circuit.relativeGateComplexity, size_eq] using bound

/-- Even nonlinear binary gates cannot beat the sparsest linear
representation, and a one-gate XOR operation attains it. -/
theorem relativeGateComplexity_eq_min_weight
    (interpretation : Interpretation σ (ZMod 2))
    (bounded : ∀ op, σ.Arity op ≤ 2)
    (addition : Circuit σ 2 1 1)
    (addition_eval : ∀ input, addition.eval interpretation input 0 = input 0 + input 1)
    (target : Fin n → ZMod 2) (nonzero : target ≠ 0)
    (rows : Fin k → Fin n → ZMod 2) :
    Circuit.relativeGateComplexity interpretation
      (fun input (_ : Fin 1) => target ⬝ᵥ input) (forms rows) =
      ⨅ coefficients : Fin k → ZMod 2, ⨅ _ : ∑ i, coefficients i • rows i = target,
        ((weight coefficients - 1 : Nat) : ℕ∞) := by
  apply le_antisymm
  · exact le_iInf fun coefficients => le_iInf fun represents =>
      relativeGateComplexity_le_weight interpretation addition addition_eval
        target nonzero rows coefficients represents
  · apply Circuit.le_relativeCostComplexity
    intro gates circuit computes
    obtain ⟨coefficients, represents, small⟩ := exists_representation_of_sourceSupport
      target rows circuit.inputSupport computes.sourceSupport
    calc
      _ ≤ ((weight coefficients - 1 : Nat) : ℕ∞) :=
        iInf_le_of_le coefficients (iInf_le_of_le represents le_rfl)
      _ ≤ circuit.cost OperationCost.unit := ?_
    have support_bound := circuit.card_inputSupport_le_cost OperationCost.unit
      (by simpa [OperationCost.unit] using bounded)
    have lower : weight coefficients - 1 ≤ circuit.cost OperationCost.unit := by omega
    exact_mod_cast lower

/-- Hamming weight separates across the original-input and helper blocks. -/
theorem weight_append (left : Fin n → ZMod 2) (right : Fin k → ZMod 2) :
    weight (Fin.append left right) = weight left + weight right := by
  simp only [weight, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

private def withCoordinates (supplied : Fin k → Fin n → ZMod 2) :
    Fin (n + k) → Fin n → ZMod 2 :=
  Fin.append (fun i => Pi.single i 1) supplied

private theorem forms_withCoordinates (supplied : Fin k → Fin n → ZMod 2) :
    forms (withCoordinates supplied) = fun input => Fin.append input (forms supplied input) := by
  funext input i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp [forms, withCoordinates]
  · simp [forms, withCoordinates]

private theorem representation_split (supplied : Fin k → Fin n → ZMod 2)
    (coefficients : Fin (n + k) → ZMod 2) :
    ∑ i, coefficients i • withCoordinates supplied i =
      (fun i => coefficients (Fin.castAdd k i)) +
        ∑ j, coefficients (Fin.natAdd n j) • supplied j := by
  rw [Fin.sum_univ_add]
  simp only [withCoordinates, Fin.append_left, Fin.append_right]
  congr 1
  ext i
  simp [Pi.single_apply, Finset.sum_apply]

private theorem weight_split (coefficients : Fin (n + k) → ZMod 2) :
    weight coefficients = weight (fun i => coefficients (Fin.castAdd k i)) +
      weight (fun j => coefficients (Fin.natAdd n j)) := by
  have equal : coefficients = Fin.append
      (fun i => coefficients (Fin.castAdd k i))
      (fun j => coefficients (Fin.natAdd n j)) := by
    funext i
    exact Fin.addCases (fun _ => by simp) (fun _ => by simp) i
  conv_lhs => rw [equal]
  exact weight_append _ _

/-- Exact conditional complexity of a nonzero linear form. The infimum is
over a finite nonempty set, so it is a minimum. The basis may contain any
other unary or binary operations, including nonlinear ones. -/
theorem conditionalGateComplexity_eq_min_weight
    (interpretation : Interpretation σ (ZMod 2))
    (bounded : ∀ op, σ.Arity op ≤ 2)
    (addition : Circuit σ 2 1 1)
    (addition_eval : ∀ input, addition.eval interpretation input 0 = input 0 + input 1)
    (target : Fin n → ZMod 2) (nonzero : target ≠ 0)
    (supplied : Fin k → Fin n → ZMod 2) :
    Circuit.conditionalGateComplexity interpretation
      (fun input (_ : Fin 1) => target ⬝ᵥ input) (forms supplied) =
      ⨅ coefficients : Fin k → ZMod 2,
        ((weight coefficients + weight (target + ∑ j, coefficients j • supplied j) - 1 : Nat) : ℕ∞) := by
  change Circuit.relativeGateComplexity interpretation _
    (fun input => Fin.append input (forms supplied input)) = _
  rw [← forms_withCoordinates, relativeGateComplexity_eq_min_weight
    interpretation bounded addition addition_eval target nonzero]
  apply le_antisymm
  · refine le_iInf fun coefficients => ?_
    let combined := Fin.append (target + ∑ j, coefficients j • supplied j) coefficients
    have represents : ∑ i, combined i • withCoordinates supplied i = target := by
      rw [representation_split]
      simp only [combined, Fin.append_left, Fin.append_right]
      ext i
      exact CharTwo.add_cancel_right _ _
    calc
      _ ≤ ((weight combined - 1 : Nat) : ℕ∞) :=
        iInf_le_of_le combined (iInf_le_of_le represents le_rfl)
      _ = _ := by simp only [combined, weight_append, Nat.add_comm]
  · refine le_iInf fun coefficients => le_iInf fun represents => ?_
    let helpers : Fin k → ZMod 2 := fun j => coefficients (Fin.natAdd n j)
    have raw : (fun i => coefficients (Fin.castAdd k i)) =
        target + ∑ j, helpers j • supplied j := by
      rw [representation_split] at represents
      ext i
      have equal := congrFun represents i
      exact (CharTwo.add_eq_iff_eq_add).mp equal
    calc
      _ ≤ ((weight helpers + weight (target + ∑ j, helpers j • supplied j) - 1 : Nat) : ℕ∞) :=
        iInf_le_of_le helpers le_rfl
      _ = _ := by rw [weight_split, raw, Nat.add_comm]

end

end Algebraic.ConditionalComplexity.Linear
