/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AC0.Switching.Defs
public import Complexitylib.Circuits.AC0.Switching.Internal

/-!
# Switching-lemma substrate

This module exposes both an elementary one-query-at-a-time decision tree and
the complete-block tree used in switching arguments. Its finite encoding
theorems include an elementary arity-dependent bound and a width-only bound for
consistent DNFs. The latter replays the canonical complete-block path from
bounded literal positions, branch bits, and phase markers.
-/

@[expose] public section

namespace Complexity

namespace Switching

/-- The elementary deepest-path code has exactly `(2 * N) ^ queryCount`
possible values. -/
theorem card_pathCode (N queryCount : ℕ) :
    Fintype.card (PathCode N queryCount) =
      (2 * N) ^ queryCount :=
  card_pathCode_internal N queryCount

/-- Width-sensitive per-query advice has exactly
`(4 * (width + 1)) ^ queryCount` possible values. -/
theorem card_widthPathCode (width queryCount : ℕ) :
    Fintype.card (WidthPathCode width queryCount) =
      (4 * (width + 1)) ^ queryCount :=
  card_widthPathCode_internal width queryCount

end Switching

namespace DNF

/-- Removing contradictory terms leaves a termwise-consistent DNF. -/
theorem consistent_consistentPart
    (formula : DNF N) :
    formula.consistentPart.Consistent :=
  consistent_consistentPart_internal formula

/-- Contradictory-term cleanup preserves the represented Boolean function. -/
theorem eval_consistentPart
    (formula : DNF N) (input : BitString N) :
    formula.consistentPart.eval input = formula.eval input :=
  eval_consistentPart_internal formula input

/-- Contradictory-term cleanup cannot increase DNF width. -/
theorem width_consistentPart_le
    (formula : DNF N) :
    formula.consistentPart.width ≤ formula.width :=
  width_consistentPart_le_internal formula

/-- The reduced component of the first surviving original term is exactly the
first term in the syntactically restricted DNF. -/
theorem firstLiveTerm_reduced
    (formula : DNF N) (restriction : Restriction.On N) :
    (formula.firstLiveTerm restriction).map Prod.snd =
      (formula.restrict restriction).terms.head? :=
  firstLiveTerm_reduced_internal formula restriction

/-- A successful first-live lookup provides an ordered-list decomposition:
the selected original term survives with the stated reduction, and every
earlier term is killed. -/
theorem firstLiveTerm_spec
    (formula : DNF N) (restriction : Restriction.On N)
    (original reduced : List (Literal N))
    (hfirst : formula.firstLiveTerm restriction =
      some (original, reduced)) :
    ∃ before after,
      formula.terms = before ++ original :: after ∧
      restrictTerm restriction original = some reduced ∧
      ∀ term ∈ before,
        restrictTerm restriction term = none :=
  firstLiveTerm_spec_internal
    formula restriction original reduced hfirst

/-- Extending a restriction preserves its first live term whenever that term's
reduced remainder survives the extension. -/
theorem firstLiveTerm_comp
    (formula : DNF N)
    (first second : Restriction.On N)
    (original reduced final : List (Literal N))
    (hfirst : formula.firstLiveTerm first =
      some (original, reduced))
    (hsecond : restrictTerm second reduced = some final) :
    formula.firstLiveTerm
        (Restriction.On.comp first second) =
      some (original, final) :=
  firstLiveTerm_comp_internal formula first second
    original reduced final hfirst hsecond

/-- Retaining the original DNF while accumulating a restriction gives exactly
the same complete-block tree as simplifying first. -/
theorem switchingDecisionTreeUnder_eq
    (formula : DNF N) (restriction : Restriction.On N) :
    formula.switchingDecisionTreeUnder restriction =
      (formula.restrict restriction).switchingDecisionTree :=
  switchingDecisionTreeUnder_eq_internal formula restriction

/-- The canonical DNF decision tree computes the same finite Boolean
function. -/
theorem eval_canonicalDecisionTree
    (formula : DNF N) (input : BitString N) :
    formula.canonicalDecisionTree.eval input =
      formula.eval input :=
  eval_canonicalDecisionTree_internal formula input

/-- Canonical decision-tree depth is bounded by the number of variables
actually occurring in the DNF. -/
theorem depth_canonicalDecisionTree_le_vars
    (formula : DNF N) :
    formula.canonicalDecisionTree.depth ≤
      formula.vars.card :=
  depth_canonicalDecisionTree_le_vars_internal formula

/-- In particular, canonical decision-tree depth never exceeds the declared
input arity. -/
theorem depth_canonicalDecisionTree_le_arity
    (formula : DNF N) :
    formula.canonicalDecisionTree.depth ≤ N :=
  depth_canonicalDecisionTree_le_arity_internal formula

/-- Every query in the canonical DNF tree occurs in the DNF itself. -/
theorem vars_canonicalDecisionTree_subset
    (formula : DNF N) :
    formula.canonicalDecisionTree.vars ⊆ formula.vars :=
  vars_canonicalDecisionTree_subset_internal formula

/-- The canonical DNF tree never repeats a variable along one path. -/
theorem pathReadOnce_canonicalDecisionTree
    (formula : DNF N) :
    formula.canonicalDecisionTree.PathReadOnce :=
  pathReadOnce_canonicalDecisionTree_internal formula

/-- The complete-block DNF switching tree computes the original formula. -/
theorem eval_switchingDecisionTree
    (formula : DNF N) (input : BitString N) :
    formula.switchingDecisionTree.eval input =
      formula.eval input :=
  eval_switchingDecisionTree_internal formula input

/-- Every query in the complete-block tree occurs in the DNF itself. -/
theorem vars_switchingDecisionTree_subset
    (formula : DNF N) :
    formula.switchingDecisionTree.vars ⊆ formula.vars :=
  vars_switchingDecisionTree_subset_internal formula

/-- The complete-block DNF tree never repeats a variable along one path. -/
theorem pathReadOnce_switchingDecisionTree
    (formula : DNF N) :
    formula.switchingDecisionTree.PathReadOnce :=
  pathReadOnce_switchingDecisionTree_internal formula

/-- Complete-block switching-tree depth is bounded by actual support size. -/
theorem depth_switchingDecisionTree_le_vars
    (formula : DNF N) :
    formula.switchingDecisionTree.depth ≤
      formula.vars.card :=
  depth_switchingDecisionTree_le_vars_internal formula

/-- Complete-block switching-tree depth never exceeds the declared arity. -/
theorem depth_switchingDecisionTree_le_arity
    (formula : DNF N) :
    formula.switchingDecisionTree.depth ≤ N :=
  depth_switchingDecisionTree_le_arity_internal formula

/-- Width-only finite counting form of the DNF switching lemma.

For a consistent width-`w` DNF, every bad restriction together with one of
`q ^ queryCount` copy-label choices injects into a seed and
`queryCount` advice symbols, each drawn from a set of size `4 * (w + 1)`.
This is the combinatorial form needed to derive the corresponding probability
bound under `RandomRestriction`. -/
theorem switchingBad_width_encoding_bound
    (formula : DNF N) (hconsistent : formula.Consistent)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingBad formula queryCount) *
        q ^ queryCount ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) ^ queryCount :=
  switchingBad_width_encoding_bound_internal
    formula hconsistent q queryCount

/-- Every DNF has an equivalent consistent sub-DNF to which the width-only
encoding applies without increasing the original width. -/
theorem switchingBad_consistentPart_width_encoding_bound
    (formula : DNF N) (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingBad formula.consistentPart queryCount) *
        q ^ queryCount ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) ^ queryCount :=
  switchingBad_consistentPart_width_encoding_bound_internal
    formula q queryCount

/-- Elementary arity-dependent counting bound for the DNF switching bad event.

The proof injectively records the first `queryCount` coordinates and branch
values of a complete-block deepest path. Consequently the auxiliary factor is
`(2 * N) ^ queryCount`. A genuine switching lemma must replace this ambient
arity factor by a bound in the DNF width. -/
theorem switchingBad_arity_encoding_bound
    (formula : DNF N) (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingBad formula queryCount) *
        q ^ queryCount ≤
      (2 * q + 1) ^ N * (2 * N) ^ queryCount :=
  switchingBad_arity_encoding_bound_internal formula q queryCount

end DNF

namespace CNF

/-- Removing tautological clauses leaves a consistent CNF. -/
theorem consistent_consistentPart
    (formula : CNF N) :
    formula.consistentPart.Consistent :=
  consistent_consistentPart_internal formula

/-- Tautological-clause cleanup preserves the represented Boolean function. -/
theorem eval_consistentPart
    (formula : CNF N) (input : BitString N) :
    formula.consistentPart.eval input = formula.eval input :=
  eval_consistentPart_internal formula input

/-- Tautological-clause cleanup cannot increase CNF width. -/
theorem width_consistentPart_le
    (formula : CNF N) :
    formula.consistentPart.width ≤ formula.width :=
  width_consistentPart_le_internal formula

/-- Accumulating the restriction in the dual DNF gives the same CNF
switching tree as syntactically restricting the CNF first. -/
theorem switchingDecisionTreeUnder_eq
    (formula : CNF N) (restriction : Restriction.On N) :
    formula.switchingDecisionTreeUnder restriction =
      (formula.restrict restriction).switchingDecisionTree :=
  switchingDecisionTreeUnder_eq_internal formula restriction

/-- The CNF bad event is exactly the DNF bad event for its De Morgan dual. -/
theorem switchingBad_eq_neg
    (formula : CNF N) (queryCount : ℕ)
    (restriction : Restriction.On N) :
    switchingBad formula queryCount restriction ↔
      DNF.switchingBad formula.neg queryCount restriction :=
  switchingBad_eq_neg_internal
    formula queryCount restriction

/-- Width-only finite counting form of the CNF switching lemma, obtained
without loss from the corresponding theorem for the dual DNF. -/
theorem switchingBad_width_encoding_bound
    (formula : CNF N) (hconsistent : formula.Consistent)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingBad formula queryCount) *
        q ^ queryCount ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) ^ queryCount :=
  switchingBad_width_encoding_bound_internal
    formula hconsistent q queryCount

/-- Every CNF has an equivalent consistent sub-CNF to which the width-only
encoding applies without increasing the original width. -/
theorem switchingBad_consistentPart_width_encoding_bound
    (formula : CNF N) (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingBad formula.consistentPart queryCount) *
        q ^ queryCount ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) ^ queryCount :=
  switchingBad_consistentPart_width_encoding_bound_internal
    formula q queryCount

/-- The canonical CNF decision tree computes the same finite Boolean
function. -/
theorem eval_canonicalDecisionTree
    (formula : CNF N) (input : BitString N) :
    formula.canonicalDecisionTree.eval input =
      formula.eval input :=
  eval_canonicalDecisionTree_internal formula input

/-- Canonical CNF decision-tree depth is bounded by actual support size. -/
theorem depth_canonicalDecisionTree_le_vars
    (formula : CNF N) :
    formula.canonicalDecisionTree.depth ≤
      formula.vars.card :=
  depth_canonicalDecisionTree_le_vars_internal formula

/-- Canonical CNF decision-tree depth never exceeds the declared arity. -/
theorem depth_canonicalDecisionTree_le_arity
    (formula : CNF N) :
    formula.canonicalDecisionTree.depth ≤ N :=
  depth_canonicalDecisionTree_le_arity_internal formula

/-- The complete-block CNF switching tree computes the original formula. -/
theorem eval_switchingDecisionTree
    (formula : CNF N) (input : BitString N) :
    formula.switchingDecisionTree.eval input =
      formula.eval input :=
  eval_switchingDecisionTree_internal formula input

/-- Every query in the complete-block CNF tree occurs in the CNF itself. -/
theorem vars_switchingDecisionTree_subset
    (formula : CNF N) :
    formula.switchingDecisionTree.vars ⊆ formula.vars :=
  vars_switchingDecisionTree_subset_internal formula

/-- The complete-block CNF tree never repeats a variable along one path. -/
theorem pathReadOnce_switchingDecisionTree
    (formula : CNF N) :
    formula.switchingDecisionTree.PathReadOnce :=
  pathReadOnce_switchingDecisionTree_internal formula

/-- Complete-block CNF switching-tree depth is bounded by actual support. -/
theorem depth_switchingDecisionTree_le_vars
    (formula : CNF N) :
    formula.switchingDecisionTree.depth ≤
      formula.vars.card :=
  depth_switchingDecisionTree_le_vars_internal formula

/-- Complete-block CNF switching-tree depth never exceeds declared arity. -/
theorem depth_switchingDecisionTree_le_arity
    (formula : CNF N) :
    formula.switchingDecisionTree.depth ≤ N :=
  depth_switchingDecisionTree_le_arity_internal formula

end CNF
end Complexity
