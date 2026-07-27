/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

/-!
  # Vocabularies (Signatures)

  Following Immerman's "Descriptive Complexity", a vocabulary (also called a
  signature) is a tuple of relation symbols with arities, plus constant symbols.
  We represent this finitely: `numRels` relation symbols with arities given by
  `relArity`, and `numConsts` constant symbols.
-/@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

/-- A vocabulary (signature) consisting of finitely many relation symbols
    with specified arities and finitely many constant symbols. -/
structure Vocabulary where
  /-- Number of relation symbols -/
  numRels : Nat
  /-- Arity of each relation symbol -/
  relArity : Fin numRels → Nat
  /-- Number of constant symbols -/
  numConsts : Nat

namespace Vocabulary

/-- A vocabulary is relational if it has no constant symbols. -/
def IsRelational (V : Vocabulary) : Prop := V.numConsts = 0

/-- The empty vocabulary with no relation or constant symbols. -/
abbrev empty : Vocabulary := ⟨0, Fin.elim0, 0⟩

/-- Construct a vocabulary with a single relation of given arity and no constants. -/
abbrev ofRel (arity : Nat) : Vocabulary := ⟨1, fun _ => arity, 0⟩

/-- The vocabulary of directed graphs: one binary relation E. -/
abbrev graph : Vocabulary := ofRel 2

/-- The vocabulary of directed graphs with distinguished source and target:
    one binary relation E and two constants s, t. -/
abbrev graphST : Vocabulary := ⟨1, fun _ => 2, 2⟩

/-- The vocabulary for binary strings with built-in ordering (Proviso 1.14):
    one unary relation S (the "1-bit" predicate).
    The linear order ≤ and successor are built-in numeric predicates, not part
    of the vocabulary. -/
abbrev stringBuiltinOrder : Vocabulary := ofRel 1

theorem graph_isRelational : graph.IsRelational := rfl

theorem stringBuiltinOrder_isRelational : stringBuiltinOrder.IsRelational := rfl

end Vocabulary

end DescriptiveComplexity

end Complexity
