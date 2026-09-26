/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.Compilation
public import Complexitylib.DescriptiveComplexity.Circuit.Internal
public import Complexitylib.DescriptiveComplexity.Circuit.Input

/-!
# First-order model checking by constant-depth Boolean circuits

Finite quantifier expansion produces the existing `AC0Formula` representation.
For a fixed first-order formula, its tree size is exactly an explicit polynomial
in universe size, and its depth is at most the source formula's size plus one.
The same expansion handles every structure of the chosen size, including varying
constant interpretations; the constants are supplied by one-hot input blocks.
At positive input width, the expansion has an equivalent circuit with exactly
the same size and depth at most the source formula's size plus two.

This formalizes the finite expansion step in Immerman, Theorem 5.22, Section 5.4
of *Descriptive Complexity*. `DescriptiveComplexity.AC0` uses this expansion
and encoding validation to prove the induced binary language has an AC0 family.
-/

public section

namespace Complexity.DescriptiveComplexity

variable {V : Vocabulary} {card N n : Nat}

/-- The expansion computes first-order satisfaction on any represented structure. -/
theorem StructureInput.compile_sat (A : DecFinStruct V) (L : StructureInput V A.card N)
    (input : BitString N) (h : StructureInput.Represents A L input)
    (φ : Formula V n) (σ : Env A.card n) :
    (L.compile φ σ).eval input = true ↔ φ.Sat A.toFinStruct σ :=
  L.compile_sat_internal A input h φ σ

/-- Expansion has exact polynomial tree size, uniformly over assignments and layouts. -/
theorem StructureInput.compile_size (L : StructureInput V card N) (φ : Formula V n)
    (σ : Env card n) : (L.compile φ σ).size = φ.expansionPolynomial.eval card :=
  L.compile_size_internal φ σ

/-- For a fixed source formula, expansion depth is independent of the universe size. -/
theorem StructureInput.compile_depth (L : StructureInput V card N) (φ : Formula V n)
    (σ : Env card n) : (L.compile φ σ).depth ≤ φ.size + 1 :=
  L.compile_depth_internal φ σ

/-- At positive input width, one circuit realizes the expansion on every input.
Its choice depends only on the formula, layout, and free-variable assignment. -/
theorem StructureInput.exists_circuit [NeZero N] (L : StructureInput V card N)
    (φ : Formula V n) (σ : Env card n) :
    ∃ gates, ∃ c : Circuit Basis.unboundedAndOr N 1 gates,
      c.size = φ.expansionPolynomial.eval card ∧ c.depth ≤ φ.size + 2 ∧
        ∀ input, c.eval input 0 = (L.compile φ σ).eval input := by
  obtain ⟨gates, c, hsize, hdepth, heval⟩ := (L.compile φ σ).exists_circuit
  refine ⟨gates, c, hsize.trans (L.compile_size φ σ), ?_, heval⟩
  have := L.compile_depth φ σ
  omega

/-- The realized circuit decides satisfaction on every valid table input. -/
theorem StructureInput.exists_circuit_sat [NeZero N] (A : DecFinStruct V)
    (L : StructureInput V A.card N) (φ : Formula V n) (σ : Env A.card n) :
    ∃ gates, ∃ c : Circuit Basis.unboundedAndOr N 1 gates,
      c.size = φ.expansionPolynomial.eval A.card ∧ c.depth ≤ φ.size + 2 ∧
        ∀ input, StructureInput.Represents A L input →
          (c.eval input 0 = true ↔ φ.Sat A.toFinStruct σ) := by
  obtain ⟨gates, c, hsize, hdepth, heval⟩ := L.exists_circuit φ σ
  refine ⟨gates, c, hsize, hdepth, ?_⟩
  intro input hinput
  rw [heval input]
  exact L.compile_sat A input hinput φ σ

/-- Every finite structure supplies a valid input to the fixed table-layout expansion. -/
theorem Formula.table_expansion_sat (A : DecFinStruct V) (φ : Formula V n)
    (σ : Env A.card n) :
    ((tableLayout V A.card).compile φ σ).eval (tableInput A) = true ↔
      φ.Sat A.toFinStruct σ :=
  StructureInput.compile_sat A _ _ (tableInput_represents A) φ σ

/-- The sentence expansion decides the query on the structure's relation and constant tables. -/
theorem Sentence.table_expansion_models (A : DecFinStruct V) (φ : Sentence V) :
    ((tableLayout V A.card).compile φ (emptyEnv A.card)).eval (tableInput A) = true ↔
      Sentence.Models A.toFinStruct φ :=
  Formula.table_expansion_sat A φ (emptyEnv A.card)

end Complexity.DescriptiveComplexity
