/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Interpretation
public import Complexitylib.DescriptiveComplexity.Interpretation.Pullback.Internal
public import Complexitylib.DescriptiveComplexity.Definable

/-!
# The dual-interpretation theorem for tagged tuples

An FO formula over the interpreted structure can be pulled back to an FO formula
over the source. Free target variables supply their tags and coordinate tuples;
sentences need no such parameters. In particular, FO definability is closed under
tagged full-product interpretations.

This is the tagged variant of Immerman, *Descriptive Complexity*, Proposition 3.5
and Remark 3.6: <https://people.cs.umass.edu/~immerman/book/ch3.pdf>.
Our target constants are tuples of source constants; definable constants,
restricted universes, and quotients are not assumed by these statements.
-/

public section

namespace Complexity.DescriptiveComplexity

namespace TaggedFOInterpretation

variable {V W : Vocabulary} {tags dim n : Nat}

/-- Tagged formula transport under an arbitrary assignment of target variables. -/
theorem translate_sat (I : TaggedFOInterpretation V W tags dim) (A : FinStruct V)
    (φ : Formula W n) (σ : Env (I.apply A).card n) :
    (I.translate φ (fun i => (elementEquiv A.card tags dim (σ i)).1)).Sat A (relationEnv σ) ↔
      φ.Sat (I.apply A) σ := by
  rw [translate, pullbackWith_sat]
  have henv : coordEnv A (fun i => (elementEquiv A.card tags dim (σ i)).1)
      (fun i j => .var (finProdFinEquiv (i, j))) (relationEnv σ) = σ := by
    funext i
    apply (elementEquiv A.card tags dim).injective
    simp [coordEnv, Term.eval, relationEnv]
  rw [henv]

/-- A source structure models the translated sentence exactly when its image models it. -/
theorem translateSentence_models (I : TaggedFOInterpretation V W tags dim) (A : FinStruct V)
    (φ : Sentence W) :
    Sentence.Models A (I.translateSentence φ) ↔ Sentence.Models (I.apply A) φ := by
  unfold Sentence.Models translateSentence
  rw [pullbackWith_sat]
  have henv : coordEnv A (Fin.elim0 : Fin 0 → Fin tags) (fun i => i.elim0)
      (emptyEnv A.card) = emptyEnv (I.apply A).card := Subsingleton.elim _ _
  rw [henv]

end TaggedFOInterpretation

/-- FO-definable queries remain FO-definable under tagged tuple interpretations. -/
theorem FODefinable.pullQuery {V W : Vocabulary} {tags dim : Nat}
    {Q : BooleanQuery W} (hQ : FODefinable Q) (I : TaggedFOInterpretation V W tags dim) :
    FODefinable (I.pullQuery Q) := by
  obtain ⟨φ, hφ⟩ := hQ
  exact ⟨I.translateSentence φ, fun A =>
    (hφ (I.apply A)).trans (I.translateSentence_models A φ).symm⟩

end Complexity.DescriptiveComplexity
