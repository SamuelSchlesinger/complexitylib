/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DecisionTree.Finite.Defs
public import Complexitylib.Circuits.NormalForm.Defs
public import Complexitylib.Circuits.NormalForm.Operations.Defs

/-!
# Compiling finite decision trees to CNF and DNF -- definitions

Each accepting root-to-leaf path becomes one DNF term. A false branch records
the negative query literal and a true branch records the positive literal.
The dual CNF is obtained by compiling the leaf-complemented tree and applying
De Morgan negation.
-/

@[expose] public section

namespace Complexity
namespace DecisionTree.On

/-- DNF terms corresponding to the accepting paths of a finite decision tree. -/
def toDNFTerms : DecisionTree.On N → List (List (Literal N))
  | .leaf false => []
  | .leaf true => [[]]
  | .node index ifFalse ifTrue =>
      ((toDNFTerms ifFalse).map fun term =>
        { var := index, polarity := false } :: term) ++
      ((toDNFTerms ifTrue).map fun term =>
        { var := index, polarity := true } :: term)

/-- Compile a finite decision tree to a DNF with one term per accepting path. -/
def toDNF (tree : DecisionTree.On N) : DNF N :=
  ⟨tree.toDNFTerms⟩

/-- Compile a finite decision tree to a CNF by De Morgan duality. -/
def toCNF (tree : DecisionTree.On N) : CNF N :=
  tree.neg.toDNF.neg

/-- Compile a disjunction of decision trees to one DNF. -/
def anyDNF (trees : List (DecisionTree.On N)) : DNF N :=
  DNF.disjoin (trees.map toDNF)

/-- Compile a conjunction of decision trees to one CNF. -/
def allCNF (trees : List (DecisionTree.On N)) : CNF N :=
  CNF.conjoin (trees.map toCNF)

end DecisionTree.On
end Complexity
