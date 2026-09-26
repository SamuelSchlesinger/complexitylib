/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.AC0.Defs
public import Complexitylib.DescriptiveComplexity.Circuit.Validity
public import Complexitylib.DescriptiveComplexity.Definable
public import Complexitylib.Circuits.DepthClasses
public import Complexitylib.Asymptotics

/-!
# First-order queries have nonuniform AC0 circuit families

At an encoded length choose the validated circuit. At every other positive
length use a constant-false circuit. The empty input is also rejected. Monotone
evaluation of natural polynomials transfers the universe-size bound to input
length, and finite circuit witnesses assemble into the existing family model.
-/

public section

namespace Complexity.DescriptiveComplexity

theorem sentence_circuits_internal {V : Vocabulary} (φ : Sentence V) (N : Nat) [NeZero N] :
    ∃ gates, ∃ c : Circuit Basis.unboundedAndOr N 1 gates,
      c.size ≤ φ.validatedPolynomial.eval N ∧ c.depth ≤ φ.size + 5 ∧
        ∀ input, c.eval input 0 = queryFamily (fun A => Sentence.Models A φ) N input := by
  classical
  by_cases hlen : ∃ card, encodingLength V card = N
  · obtain ⟨card, rfl⟩ := hlen
    obtain ⟨gates, c, hsize, hdepth, heval⟩ := φ.exists_validated_circuit card
    refine ⟨gates, c, ?_, hdepth, ?_⟩
    · rw [hsize]
      exact polynomial_eval_mono_nat φ.validatedPolynomial (card_lt_encodingLength V card).le
    · intro input
      apply Bool.eq_iff_iff.mpr
      simpa only [queryFamily, decide_eq_true_eq] using heval input
  · obtain ⟨gates, c, hsize, hdepth, heval⟩ :=
      (AC0Formula.const false : AC0Formula N).exists_circuit
    refine ⟨gates, c, ?_, ?_, ?_⟩
    · change c.size = 1 at hsize
      rw [hsize]
      simp only [Sentence.validatedPolynomial, Polynomial.eval_add, Polynomial.eval_one]
      omega
    · change c.depth ≤ 0 + 1 at hdepth
      omega
    · intro input
      have hnot : List.ofFn input ∉ queryLanguage (fun A => Sentence.Models A φ) := by
        intro hm
        obtain ⟨A, hA, _⟩ := (mem_queryLanguage_iff_decodeStruct _ _).mp hm
        have he := (decodeStruct_eq_some_iff _ _).mp hA
        apply hlen
        refine ⟨A.card, ?_⟩
        simpa only [encodeStruct_length_eq, List.length_ofFn] using congrArg List.length he
      calc
        c.eval input 0 = false := heval input
        _ = queryFamily (fun A => Sentence.Models A φ) N input := by simp [queryFamily, hnot]

theorem sentence_mem_AC0_internal {V : Vocabulary} (φ : Sentence V) :
    queryFamily (fun A => Sentence.Models A φ) ∈ Complexity.AC0 := by
  classical
  let F : CircuitFamily Basis.unboundedAndOr :=
    { emptyOutput := false
      circuits := fun n _ =>
        ⟨(sentence_circuits_internal φ n).choose,
          (sentence_circuits_internal φ n).choose_spec.choose⟩ }
  apply mem_AC0_iff.mpr
  refine ⟨F, φ.size + 5, ?_, ⟨φ.validatedPolynomial, ?_⟩, ?_⟩
  · funext n input
    cases n with
    | zero =>
      simp [CircuitFamily.function, F, queryFamily,
        not_mem_queryLanguage_of_decodeStruct_eq_none _ [] (decodeStruct_nil V)]
    | succ n => exact (sentence_circuits_internal φ (n + 1)).choose_spec.choose_spec.2.2 input
  · intro n
    cases n with
    | zero => exact Nat.zero_le _
    | succ n => exact (sentence_circuits_internal φ (n + 1)).choose_spec.choose_spec.1
  · intro n
    cases n with
    | zero => exact Nat.zero_le _
    | succ n => exact (sentence_circuits_internal φ (n + 1)).choose_spec.choose_spec.2.1

theorem foDefinable_mem_AC0_internal {V : Vocabulary} {Q : BooleanQuery V}
    (hQ : FODefinable Q) : queryFamily Q ∈ Complexity.AC0 := by
  obtain ⟨φ, hφ⟩ := hQ
  have hlang : queryLanguage Q = queryLanguage (fun A => Sentence.Models A φ) := by
    ext bits
    simp only [mem_queryLanguage_iff_decodeStruct, hφ]
  have hf : queryFamily Q = queryFamily (fun A => Sentence.Models A φ) := by
    funext n input
    apply Bool.eq_iff_iff.mpr
    simpa only [queryFamily, decide_eq_true_eq] using Set.ext_iff.mp hlang (List.ofFn input)
  rw [hf]
  exact sentence_mem_AC0_internal φ

end Complexity.DescriptiveComplexity
