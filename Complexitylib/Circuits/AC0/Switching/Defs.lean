/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DecisionTree.Block.Defs
public import Complexitylib.Circuits.NormalForm.Restriction
public import Complexitylib.Circuits.RandomRestriction.Defs

/-!
# Switching-lemma substrate -- definitions

Two decision-tree constructions are provided. The elementary canonical tree
queries one variable at a time. The switching tree instead queries every
currently free variable of the first surviving term before it either accepts
or continues. This complete-block construction is the one needed by the
standard switching-lemma encoding.

The explicit fuel is a proof-engineering device. The public construction starts
with the number of variables in the DNF, and its correctness proof shows that
each recursive query removes its variable from support.
-/

@[expose] public section

namespace Complexity

namespace Switching

/-- Auxiliary information carried by the elementary deepest-path encoding:
the queried input coordinate and chosen branch bit at each path position. -/
abbrev PathCode (N queryCount : ℕ) :=
  (Fin queryCount → Fin N) × (Fin queryCount → Bool)

/-- Per-query advice for a width-sensitive switching encoding: a bounded
literal position, the original path bit, and an end-of-phase marker. -/
abbrev WidthPathCode (width queryCount : ℕ) :=
  Fin queryCount → (Fin (width + 1) × Bool × Bool)

end Switching

namespace DNF

/-- A term is consistent when repeated occurrences of one variable always
have the same polarity. Contradictory terms must be removed or excluded before
using their polarities as a satisfying assignment. -/
def TermConsistent (term : List (Literal N)) : Prop :=
  ∀ left ∈ term, ∀ right ∈ term,
    left.var = right.var → left.polarity = right.polarity

/-- Every term in the DNF is internally consistent. -/
def Consistent (formula : DNF N) : Prop :=
  ∀ term ∈ formula.terms, TermConsistent term

/-- Remove contradictory DNF terms. Such terms are identically false, so this
semantic cleanup does not change the represented function. -/
noncomputable def consistentPart (formula : DNF N) : DNF N :=
  by
    classical
    exact ⟨formula.terms.filter
      fun term => decide (TermConsistent term)⟩

/-- The first original term that survives a restriction, paired with its
reduced list of free literals. Keeping the original term supplies the
provenance needed by width-sensitive switching encodings. -/
def firstLiveTerm (formula : DNF N)
    (restriction : Restriction.On N) :
    Option (List (Literal N) × List (Literal N)) :=
  formula.terms.findSome? fun term =>
    (restrictTerm restriction term).map fun reduced =>
      (term, reduced)

/-- Fuelled canonical decision tree for a DNF. -/
def canonicalDecisionTreeAux :
    ℕ → DNF N → DecisionTree.On N
  | 0, formula =>
      .leaf (formula.eval fun _ => false)
  | _ + 1, ⟨[]⟩ => .leaf false
  | _ + 1, ⟨[] :: _⟩ => .leaf true
  | fuel + 1, formula@⟨(literal :: _) :: _⟩ =>
      .node literal.var
        (canonicalDecisionTreeAux fuel
          (formula.restrict
            (Restriction.On.single literal.var false)))
        (canonicalDecisionTreeAux fuel
          (formula.restrict
            (Restriction.On.single literal.var true)))

/-- The canonical finite decision tree for a DNF. -/
def canonicalDecisionTree (formula : DNF N) :
    DecisionTree.On N :=
  canonicalDecisionTreeAux formula.vars.card formula

/-- Fuelled block decision tree used by the switching lemma.

For the first surviving term, this tree queries every distinct variable in one
complete block. A satisfying block ends at `true`; every other block restricts
the DNF and continues with one less unit of fuel. -/
noncomputable def switchingDecisionTreeAux :
    ℕ → DNF N → DecisionTree.On N
  | 0, formula =>
      .leaf (formula.eval fun _ => false)
  | _ + 1, ⟨[]⟩ => .leaf false
  | _ + 1, ⟨[] :: _⟩ => .leaf true
  | fuel + 1, formula@⟨term :: _⟩ =>
      let queries := (Literal.vars term).toList
      DecisionTree.On.queryAll queries fun branch =>
        let assignment := DecisionTree.On.assignmentFor queries
          (branch.applyTo fun _ => false)
        if term.all (fun literal => literal.eval
            (assignment.applyTo fun _ => false)) then
          .leaf true
        else
          switchingDecisionTreeAux fuel
            (formula.restrict assignment)

/-- The canonical complete-block tree used in switching arguments. -/
noncomputable def switchingDecisionTree (formula : DNF N) :
    DecisionTree.On N :=
  switchingDecisionTreeAux formula.vars.card formula

/-- Fuelled complete-block switching tree that retains the original DNF and
accumulates a restriction separately. This is extensionally the same tree as
first simplifying the DNF, but it preserves original-term provenance. -/
noncomputable def switchingDecisionTreeUnderAux :
    ℕ → DNF N → Restriction.On N → DecisionTree.On N
  | 0, formula, restriction =>
      .leaf (formula.eval
        (restriction.applyTo fun _ => false))
  | fuel + 1, formula, restriction =>
      match formula.firstLiveTerm restriction with
      | none => .leaf false
      | some (_, []) => .leaf true
      | some (_, term@(_ :: _)) =>
          let queries := (Literal.vars term).toList
          DecisionTree.On.queryAll queries fun branch =>
            let assignment := DecisionTree.On.assignmentFor queries
              (branch.applyTo fun _ => false)
            if term.all (fun literal => literal.eval
                (assignment.applyTo fun _ => false)) then
              .leaf true
            else
              switchingDecisionTreeUnderAux fuel formula
                (Restriction.On.comp restriction assignment)

/-- Complete-block switching tree for an original DNF under an accumulated
restriction, with enough fuel for every surviving variable. -/
noncomputable def switchingDecisionTreeUnder
    (formula : DNF N) (restriction : Restriction.On N) :
    DecisionTree.On N :=
  switchingDecisionTreeUnderAux
    (formula.restrict restriction).vars.card
    formula restriction

/-- The bad event bounded by the switching lemma: after applying the decoded
random restriction, the complete-block DNF switching tree still has depth at
least `queryCount`. -/
noncomputable def switchingBad (formula : DNF N) (queryCount : ℕ)
    (restriction : Restriction.On N) : Prop :=
  queryCount ≤
    (formula.switchingDecisionTreeUnder restriction).depth

noncomputable instance switchingBadDecidable (formula : DNF N)
    (queryCount : ℕ) :
    DecidablePred (switchingBad formula queryCount) :=
  fun restriction => by
    unfold switchingBad
    infer_instance

end DNF

namespace CNF

/-- A CNF is consistent when no clause is tautological. Equivalently, every
term in its De Morgan dual DNF is internally consistent. -/
def Consistent (formula : CNF N) : Prop :=
  formula.neg.Consistent

/-- Delete tautological CNF clauses by cleaning the contradictory terms in
the De Morgan dual. This preserves the represented function. -/
noncomputable def consistentPart (formula : CNF N) : CNF N :=
  formula.neg.consistentPart.neg

/-- The canonical decision tree for a CNF, obtained by the De Morgan dual DNF
and leaf complementation. -/
def canonicalDecisionTree (formula : CNF N) :
    DecisionTree.On N :=
  formula.neg.canonicalDecisionTree.neg

/-- The complete-block switching tree for a CNF, obtained from its De Morgan
dual DNF by complementing the leaves. -/
noncomputable def switchingDecisionTree (formula : CNF N) :
    DecisionTree.On N :=
  formula.neg.switchingDecisionTree.neg

/-- Complete-block switching tree for a CNF under an accumulated restriction,
obtained by dualizing the provenance-preserving DNF construction. -/
noncomputable def switchingDecisionTreeUnder
    (formula : CNF N) (restriction : Restriction.On N) :
    DecisionTree.On N :=
  (formula.neg.switchingDecisionTreeUnder restriction).neg

/-- The CNF bad event for the switching lemma. -/
noncomputable def switchingBad (formula : CNF N) (queryCount : ℕ)
    (restriction : Restriction.On N) : Prop :=
  queryCount ≤
    (formula.switchingDecisionTreeUnder restriction).depth

noncomputable instance switchingBadDecidable (formula : CNF N)
    (queryCount : ℕ) :
    DecidablePred (switchingBad formula queryCount) :=
  fun restriction => by
    unfold switchingBad
    infer_instance

end CNF
end Complexity
