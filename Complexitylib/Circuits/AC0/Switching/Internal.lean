/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.Switching.Defs
public import Complexitylib.Circuits.DecisionTree.Finite
public import Complexitylib.Circuits.RandomRestriction.Internal
public import Complexitylib.Circuits.DecisionTree.Block.Internal
public import Complexitylib.Circuits.DecisionTree.Path.Internal

/-!
# Switching-lemma substrate -- proof internals
-/


public section

namespace Complexity

namespace Switching

theorem card_pathCode_internal (N queryCount : ℕ) :
    Fintype.card (PathCode N queryCount) =
      (2 * N) ^ queryCount := by
  simp [PathCode, Nat.mul_pow, Nat.mul_comm]

theorem card_widthPathCode_internal (width queryCount : ℕ) :
    Fintype.card (WidthPathCode width queryCount) =
      (4 * (width + 1)) ^ queryCount := by
  simp [WidthPathCode, Fintype.card_prod,
    Nat.mul_pow, Nat.mul_comm]

end Switching

namespace DNF

private theorem evalTerm_eq_false_of_not_consistent
    (term : List (Literal N)) (input : BitString N)
    (hinconsistent : ¬TermConsistent term) :
    term.all (fun literal => literal.eval input) = false := by
  classical
  simp only [Bool.eq_false_iff]
  intro hall
  rw [TermConsistent] at hinconsistent
  apply hinconsistent
  intro left hleft right hright hvar
  have hleftEval := (List.all_eq_true.mp hall) left hleft
  have hrightEval := (List.all_eq_true.mp hall) right hright
  rcases left with ⟨leftVar, leftPolarity⟩
  rcases right with ⟨rightVar, rightPolarity⟩
  simp only at hvar
  subst rightVar
  cases hinput : input leftVar <;>
    cases leftPolarity <;> cases rightPolarity <;>
    simp [Literal.eval, hinput] at hleftEval hrightEval ⊢

theorem consistent_consistentPart_internal
    (formula : DNF N) :
    formula.consistentPart.Consistent := by
  classical
  simp [Consistent, consistentPart]

theorem eval_consistentPart_internal
    (formula : DNF N) (input : BitString N) :
    formula.consistentPart.eval input = formula.eval input := by
  classical
  rcases formula with ⟨terms⟩
  simp only [consistentPart, eval]
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      by_cases hconsistent : TermConsistent term
      · simp [hconsistent, ih]
      · have hfalse :=
          evalTerm_eq_false_of_not_consistent
            term input hconsistent
        simp [hconsistent, hfalse, ih]

theorem width_consistentPart_le_internal
    (formula : DNF N) :
    formula.consistentPart.width ≤ formula.width := by
  classical
  rcases formula with ⟨terms⟩
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      by_cases hconsistent : TermConsistent term
      · simp only [consistentPart, List.filter_cons,
          hconsistent, decide_true, ite_true,
          width, List.foldr_cons]
        exact max_le_max (le_refl _) ih
      · simp only [consistentPart, List.filter_cons,
          hconsistent, decide_false, width,
          List.foldr_cons]
        exact ih.trans (le_max_right _ _)

theorem firstLiveTerm_reduced_internal
    (formula : DNF N) (restriction : Restriction.On N) :
    (formula.firstLiveTerm restriction).map Prod.snd =
      (formula.restrict restriction).terms.head? := by
  rcases formula with ⟨terms⟩
  rw [show (restrict restriction { terms := terms }).terms.head? =
      List.findSome? (restrictTerm restriction) terms by
    exact List.head?_filterMap]
  change Option.map Prod.snd
      (List.findSome? (fun term =>
        Option.map (fun reduced => (term, reduced))
          (restrictTerm restriction term)) terms) =
    List.findSome? (restrictTerm restriction) terms
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      cases hterm : restrictTerm restriction term with
      | none => simp [hterm, ih]
      | some reduced => simp [hterm]

theorem firstLiveTerm_spec_internal
    (formula : DNF N) (restriction : Restriction.On N)
    (original reduced : List (Literal N))
    (hfirst : formula.firstLiveTerm restriction =
      some (original, reduced)) :
    ∃ before after,
      formula.terms = before ++ original :: after ∧
      restrictTerm restriction original = some reduced ∧
      ∀ term ∈ before,
        restrictTerm restriction term = none := by
  rw [firstLiveTerm, List.findSome?_eq_some_iff] at hfirst
  obtain ⟨before, found, after, hterms, hfound,
    hbefore⟩ := hfirst
  cases hrestrict : restrictTerm restriction found with
  | none => simp [hrestrict] at hfound
  | some actual =>
      simp [hrestrict] at hfound
      rcases hfound with ⟨rfl, rfl⟩
      refine ⟨before, after, hterms, hrestrict, ?_⟩
      intro term hterm
      have hnone := hbefore term hterm
      cases hrestrictTerm : restrictTerm restriction term with
      | none => rfl
      | some value => simp [hrestrictTerm] at hnone

theorem firstLiveTerm_comp_internal
    (formula : DNF N)
    (first second : Restriction.On N)
    (original reduced final : List (Literal N))
    (hfirst : formula.firstLiveTerm first =
      some (original, reduced))
    (hsecond : restrictTerm second reduced = some final) :
    formula.firstLiveTerm
        (Restriction.On.comp first second) =
      some (original, final) := by
  obtain ⟨before, after, hterms, hrestrict, hbefore⟩ :=
    firstLiveTerm_spec_internal formula first
      original reduced hfirst
  rw [firstLiveTerm, List.findSome?_eq_some_iff]
  refine ⟨before, original, after, hterms, ?_, ?_⟩
  · rw [restrictTerm_comp, hrestrict]
    simp [hsecond]
  · intro term hterm
    rw [restrictTerm_comp, hbefore term hterm]
    rfl

theorem switchingDecisionTreeUnderAux_eq_internal
    (fuel : ℕ) (formula : DNF N)
    (restriction : Restriction.On N) :
    switchingDecisionTreeUnderAux fuel formula restriction =
      switchingDecisionTreeAux fuel
        (formula.restrict restriction) := by
  induction fuel generalizing formula restriction with
  | zero =>
      simp [switchingDecisionTreeUnderAux,
        switchingDecisionTreeAux, DNF.eval_restrict]
  | succ fuel ih =>
      generalize hrestricted : formula.restrict restriction =
        restricted
      rcases restricted with ⟨terms⟩
      have hmap :=
        firstLiveTerm_reduced_internal formula restriction
      rw [hrestricted] at hmap
      cases terms with
      | nil =>
          have hfirst :
              formula.firstLiveTerm restriction = none := by
            cases h : formula.firstLiveTerm restriction <;>
              simp_all
          simp [switchingDecisionTreeUnderAux,
            switchingDecisionTreeAux, hfirst]
      | cons reduced rest =>
          have hfirst : ∃ original,
              formula.firstLiveTerm restriction =
                some (original, reduced) := by
            cases h : formula.firstLiveTerm restriction with
            | none => simp [h] at hmap
            | some pair =>
                rcases pair with ⟨original, found⟩
                rw [h] at hmap
                have hfound : found = reduced := by
                  simpa using hmap
                subst found
                exact ⟨original, rfl⟩
          obtain ⟨original, hfirst⟩ := hfirst
          cases reduced with
          | nil =>
              simp [switchingDecisionTreeUnderAux,
                switchingDecisionTreeAux, hfirst]
          | cons literal tail =>
              simp only [switchingDecisionTreeUnderAux,
                switchingDecisionTreeAux, hfirst]
              apply congrArg
                (DecisionTree.On.queryAll
                  (Literal.vars (literal :: tail)).toList)
              funext branch
              split
              · rfl
              · rw [ih, ← hrestricted,
                  DNF.restrict_comp]

theorem switchingDecisionTreeUnder_eq_internal
    (formula : DNF N) (restriction : Restriction.On N) :
    formula.switchingDecisionTreeUnder restriction =
      (formula.restrict restriction).switchingDecisionTree := by
  exact switchingDecisionTreeUnderAux_eq_internal
    (formula.restrict restriction).vars.card
    formula restriction

private noncomputable def switchingPhasesAux :
    ℕ → DNF N → Restriction.On N →
      List (List (Literal N) × List (Fin N × Bool))
  | 0, _, _ => []
  | fuel + 1, formula, restriction =>
      match formula.firstLiveTerm restriction with
      | none => []
      | some (_, []) => []
      | some (original, term@(_ :: _)) =>
          let queries := (Literal.vars term).toList
          let continuation : Restriction.On N →
              DecisionTree.On N := fun branch =>
            let assignment :=
              DecisionTree.On.assignmentFor queries
                (branch.applyTo fun _ => false)
            if term.all (fun literal => literal.eval
                (assignment.applyTo fun _ => false)) then
              .leaf true
            else
              switchingDecisionTreeUnderAux fuel formula
                (Restriction.On.comp restriction assignment)
          let block :=
            DecisionTree.On.deepBlockPath queries continuation
          let branch :=
            DecisionTree.On.deepBranch queries continuation
          if term.all (fun literal => literal.eval
              (branch.applyTo fun _ => false)) then
            [(original, block)]
          else
            (original, block) ::
              switchingPhasesAux fuel formula
                (Restriction.On.comp restriction branch)

/-- A phase list is recoverable when each phase records all free variables of
the first live term, and its tail is recoverable after applying the recorded
path assignment. -/
private inductive RecoverablePhases (formula : DNF N) :
    Restriction.On N →
      List (List (Literal N) × List (Fin N × Bool)) → Prop
  | nil (restriction) :
      RecoverablePhases formula restriction []
  | cons (restriction : Restriction.On N)
      (original reduced : List (Literal N))
      (block : List (Fin N × Bool))
      (phases :
        List (List (Literal N) × List (Fin N × Bool)))
      (hfirst : formula.firstLiveTerm restriction =
        some (original, reduced))
      (hnonempty : reduced ≠ [])
      (hqueries : block.map Prod.fst =
        (Literal.vars reduced).toList)
      (htail : RecoverablePhases formula
        (Restriction.On.comp restriction
          (DecisionTree.On.assignmentOfPath block))
        phases) :
      RecoverablePhases formula restriction
        ((original, block) :: phases)

private theorem recoverable_switchingPhasesAux
    (fuel : ℕ) (formula : DNF N)
    (restriction : Restriction.On N) :
    RecoverablePhases formula restriction
      (switchingPhasesAux fuel formula restriction) := by
  induction fuel generalizing restriction with
  | zero =>
      exact RecoverablePhases.nil restriction
  | succ fuel ih =>
      cases hfirst : formula.firstLiveTerm restriction with
      | none =>
          simp only [switchingPhasesAux, hfirst]
          exact RecoverablePhases.nil restriction
      | some pair =>
          rcases pair with ⟨original, reduced⟩
          cases reduced with
          | nil =>
              simp only [switchingPhasesAux, hfirst]
              exact RecoverablePhases.nil restriction
          | cons literal tail =>
              let term := literal :: tail
              let queries := (Literal.vars term).toList
              let continuation : Restriction.On N →
                  DecisionTree.On N := fun branch =>
                let assignment :=
                  DecisionTree.On.assignmentFor queries
                    (branch.applyTo fun _ => false)
                if term.all (fun found => found.eval
                    (assignment.applyTo fun _ => false)) then
                  .leaf true
                else
                  switchingDecisionTreeUnderAux fuel formula
                    (Restriction.On.comp restriction assignment)
              let block :=
                DecisionTree.On.deepBlockPath queries continuation
              let branch :=
                DecisionTree.On.deepBranch queries continuation
              have hqueries : block.map Prod.fst =
                  (Literal.vars (literal :: tail)).toList := by
                simpa [block, queries, term] using
                  DecisionTree.On.map_fst_deepBlockPath_internal
                    queries continuation
              have hassignment :
                  DecisionTree.On.assignmentOfPath block =
                    branch := by
                simpa [block, branch] using
                  DecisionTree.On.assignmentOfPath_deepBlockPath_internal
                    queries continuation
              simp only [switchingPhasesAux, hfirst]
              change RecoverablePhases formula restriction
                (if term.all (fun found => found.eval
                    (branch.applyTo fun _ => false)) then
                  [(original, block)]
                else
                  (original, block) ::
                    switchingPhasesAux fuel formula
                      (Restriction.On.comp restriction branch))
              by_cases hterm : term.all (fun found =>
                  found.eval
                    (branch.applyTo fun _ => false)) = true
              · rw [ite_eq_left hterm]
                apply RecoverablePhases.cons restriction
                  original (literal :: tail) block []
                    hfirst (by simp) hqueries
                rw [hassignment]
                exact RecoverablePhases.nil _
              · rw [ite_eq_right hterm]
                apply RecoverablePhases.cons restriction
                  original (literal :: tail) block
                    (switchingPhasesAux fuel formula
                      (Restriction.On.comp restriction branch))
                    hfirst (by simp) hqueries
                rw [hassignment]
                exact ih
                  (Restriction.On.comp restriction branch)

private theorem deepPath_switchingDecisionTreeUnderAux
    (fuel : ℕ) (formula : DNF N)
    (restriction : Restriction.On N) :
    (switchingDecisionTreeUnderAux fuel formula
        restriction).deepPath =
      (switchingPhasesAux fuel formula restriction).flatMap
        Prod.snd := by
  induction fuel generalizing formula restriction with
  | zero => rfl
  | succ fuel ih =>
      cases hfirst : formula.firstLiveTerm restriction with
      | none =>
          simp [switchingDecisionTreeUnderAux,
            switchingPhasesAux, hfirst,
            DecisionTree.On.deepPath]
      | some pair =>
          rcases pair with ⟨original, reduced⟩
          cases reduced with
          | nil =>
              simp [switchingDecisionTreeUnderAux,
                switchingPhasesAux, hfirst,
                DecisionTree.On.deepPath]
          | cons literal tail =>
              let term := literal :: tail
              let queries := (Literal.vars term).toList
              let continuation : Restriction.On N →
                  DecisionTree.On N := fun branch =>
                let assignment :=
                  DecisionTree.On.assignmentFor queries
                    (branch.applyTo fun _ => false)
                if term.all (fun found => found.eval
                    (assignment.applyTo fun _ => false)) then
                  .leaf true
                else
                  switchingDecisionTreeUnderAux fuel formula
                    (Restriction.On.comp restriction assignment)
              let block :=
                DecisionTree.On.deepBlockPath queries continuation
              let branch :=
                DecisionTree.On.deepBranch queries continuation
              have hcanonical :
                  DecisionTree.On.assignmentFor queries
                      (branch.applyTo fun _ => false) = branch := by
                exact
                  DecisionTree.On.assignmentFor_deepBranch_internal
                    queries continuation (Finset.nodup_toList _)
                      (fun _ => false)
              simp only [switchingDecisionTreeUnderAux,
                switchingPhasesAux, hfirst]
              rw [DecisionTree.On.deepPath_queryAll_internal]
              change block ++ (continuation branch).deepPath =
                (if term.all (fun found => found.eval
                    (branch.applyTo fun _ => false)) then
                  [(original, block)]
                else
                  (original, block) ::
                    switchingPhasesAux fuel formula
                      (Restriction.On.comp restriction branch)).flatMap
                        Prod.snd
              by_cases hterm : term.all (fun found =>
                  found.eval
                    (branch.applyTo fun _ => false)) = true
              · rw [ite_eq_left hterm]
                dsimp only [continuation]
                rw [hcanonical, ite_eq_left hterm]
                rfl
              · rw [ite_eq_right hterm]
                dsimp only [continuation]
                rw [hcanonical, ite_eq_right hterm]
                simp only [List.flatMap_cons]
                rw [ih]

private theorem firstLiveTerm_of_switchingDepth_pos
    (fuel : ℕ) (formula : DNF N)
    (restriction : Restriction.On N)
    (hpositive :
      0 < (switchingDecisionTreeUnderAux fuel
        formula restriction).depth) :
    ∃ original literal tail,
      formula.firstLiveTerm restriction =
        some (original, literal :: tail) := by
  cases fuel with
  | zero =>
      simp [switchingDecisionTreeUnderAux,
        DecisionTree.On.depth] at hpositive
  | succ fuel =>
      cases hfirst : formula.firstLiveTerm restriction with
      | none =>
          simp [switchingDecisionTreeUnderAux, hfirst,
            DecisionTree.On.depth] at hpositive
      | some pair =>
          rcases pair with ⟨original, reduced⟩
          cases reduced with
          | nil =>
              simp [switchingDecisionTreeUnderAux, hfirst,
                DecisionTree.On.depth] at hpositive
          | cons literal tail =>
              exact ⟨original, literal, tail, rfl⟩

private theorem switchingPhasesAux_first_spec
    (fuel : ℕ) (formula : DNF N)
    (restriction : Restriction.On N)
    (hpositive :
      0 < (switchingDecisionTreeUnderAux fuel
        formula restriction).depth) :
    ∃ original literal tail block phases,
      formula.firstLiveTerm restriction =
          some (original, literal :: tail) ∧
        switchingPhasesAux fuel formula restriction =
          (original, block) :: phases ∧
        block.map Prod.fst =
          (Literal.vars (literal :: tail)).toList ∧
        block ≠ [] := by
  cases fuel with
  | zero =>
      simp [switchingDecisionTreeUnderAux,
        DecisionTree.On.depth] at hpositive
  | succ fuel =>
      cases hfirst : formula.firstLiveTerm restriction with
      | none =>
          simp [switchingDecisionTreeUnderAux, hfirst,
            DecisionTree.On.depth] at hpositive
      | some pair =>
          rcases pair with ⟨original, reduced⟩
          cases reduced with
          | nil =>
              simp [switchingDecisionTreeUnderAux, hfirst,
                DecisionTree.On.depth] at hpositive
          | cons literal tail =>
              let term := literal :: tail
              let queries := (Literal.vars term).toList
              let continuation : Restriction.On N →
                  DecisionTree.On N := fun branch =>
                let assignment :=
                  DecisionTree.On.assignmentFor queries
                    (branch.applyTo fun _ => false)
                if term.all (fun found => found.eval
                    (assignment.applyTo fun _ => false)) then
                  .leaf true
                else
                  switchingDecisionTreeUnderAux fuel formula
                    (Restriction.On.comp restriction assignment)
              let block :=
                DecisionTree.On.deepBlockPath queries continuation
              let branch :=
                DecisionTree.On.deepBranch queries continuation
              have hmap : block.map Prod.fst =
                  (Literal.vars (literal :: tail)).toList := by
                simpa [block, queries, term] using
                  DecisionTree.On.map_fst_deepBlockPath_internal
                    queries continuation
              have hblock : block ≠ [] := by
                intro hempty
                have hqueries :
                    (Literal.vars
                      (literal :: tail)).toList ≠ [] := by
                  have hmem : literal.var ∈
                      (Literal.vars
                        (literal :: tail)).toList := by
                    simp [Literal.mem_vars_iff]
                  exact List.ne_nil_of_mem hmem
                rw [hempty] at hmap
                exact hqueries hmap.symm
              have hphases : ∃ phases,
                  switchingPhasesAux (fuel + 1) formula
                      restriction =
                    (original, block) :: phases := by
                simp only [switchingPhasesAux, hfirst]
                change ∃ phases,
                  (if term.all (fun found => found.eval
                      ((DecisionTree.On.deepBranch queries
                        continuation).applyTo fun _ => false)) then
                    [(original, block)]
                  else
                    (original, block) ::
                      switchingPhasesAux fuel formula
                        (Restriction.On.comp restriction
                          (DecisionTree.On.deepBranch
                            queries continuation))) =
                      (original, block) :: phases
                split
                · exact ⟨[], rfl⟩
                · exact ⟨switchingPhasesAux fuel formula
                      (Restriction.On.comp restriction
                        (DecisionTree.On.deepBranch
                          queries continuation)),
                    rfl⟩
              obtain ⟨phases, hphases⟩ := hphases
              exact ⟨original, literal, tail, block, phases,
                rfl, hphases, hmap, hblock⟩

private structure PhaseEntry (N : ℕ) where
  original : List (Literal N)
  query : Fin N × Bool
  endPhase : Bool

private def annotateBlock (original : List (Literal N))
    (block : List (Fin N × Bool)) : List (PhaseEntry N) :=
  block.mapIdx fun index query =>
    ⟨original, query, decide (index + 1 = block.length)⟩

private def annotatePhases
    (phases :
      List (List (Literal N) × List (Fin N × Bool))) :
    List (PhaseEntry N) :=
  phases.flatMap fun phase =>
    annotateBlock phase.1 phase.2

private theorem annotatePhases_cons_getElem_zero_original
    (original : List (Literal N))
    (block : List (Fin N × Bool))
    (phases :
      List (List (Literal N) × List (Fin N × Bool)))
    (hblock : block ≠ []) :
    ((annotatePhases ((original, block) :: phases))[0]'(by
      cases block with
      | nil => contradiction
      | cons query rest =>
          simp [annotatePhases, annotateBlock])).original =
        original := by
  cases block with
  | nil => contradiction
  | cons query rest =>
      simp [annotatePhases, annotateBlock]

private theorem map_query_annotateBlock
    (original : List (Literal N))
    (block : List (Fin N × Bool)) :
    (annotateBlock original block).map PhaseEntry.query =
      block := by
  apply List.ext_getElem
  · simp [annotateBlock]
  · intro index hleft hright
    simp [annotateBlock, List.getElem_mapIdx]

private theorem map_query_annotatePhases
    (phases :
      List (List (Literal N) × List (Fin N × Bool))) :
    (annotatePhases phases).map PhaseEntry.query =
      phases.flatMap Prod.snd := by
  induction phases with
  | nil => rfl
  | cons phase phases ih =>
      rcases phase with ⟨original, block⟩
      change
        (annotateBlock original block ++
          annotatePhases phases).map PhaseEntry.query =
        block ++ phases.flatMap Prod.snd
      rw [List.map_append, map_query_annotateBlock, ih]

private theorem eq_of_mem_of_mem_of_map_nodup
    {α β : Type} (items : List α) (project : α → β)
    (left right : α)
    (hleft : left ∈ items) (hright : right ∈ items)
    (hnodup : (items.map project).Nodup)
    (hproject : project left = project right) :
    left = right := by
  induction items with
  | nil => simp at hleft
  | cons head tail ih =>
      have hparts := List.nodup_cons.mp hnodup
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft
      · rcases hright with rfl | hright
        · rfl
        · exfalso
          apply hparts.1
          rw [List.mem_map]
          exact ⟨right, hright, hproject.symm⟩
      · rcases hright with rfl | hright
        · exfalso
          apply hparts.1
          rw [List.mem_map]
          exact ⟨left, hleft, hproject⟩
        · exact ih hleft hright hparts.2

private theorem original_eq_of_mem_annotateBlock
    (original : List (Literal N))
    (block : List (Fin N × Bool))
    (entry : PhaseEntry N)
    (hentry : entry ∈ annotateBlock original block) :
    entry.original = original := by
  obtain ⟨position, hposition⟩ :=
    List.get_of_mem hentry
  have hproject :=
    congrArg PhaseEntry.original hposition
  simp only [annotateBlock] at hproject
  erw [List.get_eq_getElem, List.getElem_mapIdx] at hproject
  exact hproject.symm

private theorem map_query_annotatedSwitchingPhases
    (fuel : ℕ) (formula : DNF N)
    (restriction : Restriction.On N) :
    (annotatePhases
      (switchingPhasesAux fuel formula restriction)).map
        PhaseEntry.query =
      (switchingDecisionTreeUnderAux fuel formula
        restriction).deepPath := by
  rw [map_query_annotatePhases,
    deepPath_switchingDecisionTreeUnderAux]

private theorem switchingPhasesAux_valid
    (fuel : ℕ) (formula : DNF N)
    (restriction : Restriction.On N)
    (phase :
      List (Literal N) × List (Fin N × Bool))
    (hphase :
      phase ∈ switchingPhasesAux fuel formula restriction) :
    phase.1 ∈ formula.terms ∧
      ∀ query ∈ phase.2,
        query.1 ∈ Literal.vars phase.1 := by
  induction fuel generalizing restriction phase with
  | zero =>
      simp [switchingPhasesAux] at hphase
  | succ fuel ih =>
      cases hfirst : formula.firstLiveTerm restriction with
      | none =>
          simp [switchingPhasesAux, hfirst] at hphase
      | some pair =>
          rcases pair with ⟨original, reduced⟩
          cases reduced with
          | nil =>
              simp [switchingPhasesAux, hfirst] at hphase
          | cons literal tail =>
              let term := literal :: tail
              let queries := (Literal.vars term).toList
              let continuation : Restriction.On N →
                  DecisionTree.On N := fun branch =>
                let assignment :=
                  DecisionTree.On.assignmentFor queries
                    (branch.applyTo fun _ => false)
                if term.all (fun found => found.eval
                    (assignment.applyTo fun _ => false)) then
                  .leaf true
                else
                  switchingDecisionTreeUnderAux fuel formula
                    (Restriction.On.comp restriction assignment)
              let block :=
                DecisionTree.On.deepBlockPath queries continuation
              let branch :=
                DecisionTree.On.deepBranch queries continuation
              obtain
                ⟨before, after, hterms, hrestrict, hbefore⟩ :=
                firstLiveTerm_spec_internal formula restriction
                  original (literal :: tail) hfirst
              have horiginal :
                  original ∈ formula.terms := by
                rw [hterms]
                simp
              have hblock : ∀ query ∈ block,
                  query.1 ∈ Literal.vars original := by
                intro query hquery
                have hqueryList : query.1 ∈ queries := by
                  rw [←
                    DecisionTree.On.map_fst_deepBlockPath_internal
                      queries continuation]
                  exact List.mem_map_of_mem hquery
                have hqueryReduced :
                    query.1 ∈
                      Literal.vars (literal :: tail) := by
                  simpa [queries, term] using hqueryList
                rw [Literal.mem_vars_iff] at hqueryReduced
                rw [Literal.mem_vars_iff]
                obtain ⟨found, hfound, hvar⟩ :=
                  hqueryReduced
                have horiginalLiteral :=
                  (DNF.mem_of_mem_restrictTerm restriction
                    hrestrict hfound).1
                exact ⟨found, horiginalLiteral, hvar⟩
              simp only [switchingPhasesAux, hfirst] at hphase
              change phase ∈
                (if term.all (fun found => found.eval
                    (branch.applyTo fun _ => false)) then
                  [(original, block)]
                else
                  (original, block) ::
                    switchingPhasesAux fuel formula
                      (Restriction.On.comp restriction branch))
                  at hphase
              by_cases hterm : term.all (fun found =>
                  found.eval
                    (branch.applyTo fun _ => false)) = true
              · rw [ite_eq_left hterm] at hphase
                simp only [List.mem_singleton] at hphase
                subst phase
                exact ⟨horiginal, hblock⟩
              · rw [ite_eq_right hterm] at hphase
                simp only [List.mem_cons] at hphase
                rcases hphase with hhead | htailPhase
                · subst phase
                  exact ⟨horiginal, hblock⟩
                · exact ih _ _ htailPhase

private theorem phaseEntry_valid
    (fuel : ℕ) (formula : DNF N)
    (restriction : Restriction.On N)
    (entry : PhaseEntry N)
    (hentry : entry ∈ annotatePhases
      (switchingPhasesAux fuel formula restriction)) :
    entry.original ∈ formula.terms ∧
      entry.query.1 ∈ Literal.vars entry.original := by
  rw [annotatePhases, List.mem_flatMap] at hentry
  obtain ⟨phase, hphase, hentry⟩ := hentry
  have hvalid :=
    switchingPhasesAux_valid fuel formula restriction
      phase hphase
  rcases phase with ⟨original, block⟩
  have horiginal : entry.original = original := by
    obtain ⟨position, hposition⟩ :=
      List.get_of_mem hentry
    have hproject :=
      congrArg PhaseEntry.original hposition
    simp only [annotateBlock] at hproject
    erw [List.get_eq_getElem, List.getElem_mapIdx] at hproject
    exact hproject.symm
  have hquery : entry.query ∈ block := by
    rw [← map_query_annotateBlock original block]
    exact List.mem_map_of_mem hentry
  constructor
  · simpa [horiginal] using hvalid.1
  · simpa [horiginal] using hvalid.2 entry.query hquery

private noncomputable def literalPosition
    (term : List (Literal N)) (index : Fin N)
    (hindex : index ∈ Literal.vars term) :
    Fin term.length :=
  let witness :=
    (Literal.mem_vars_iff term index).mp hindex
  Classical.choose
    (List.get_of_mem (Classical.choose_spec witness).1)

private theorem literalPosition_var
    (term : List (Literal N)) (index : Fin N)
    (hindex : index ∈ Literal.vars term) :
    (term.get (literalPosition term index hindex)).var =
      index := by
  unfold literalPosition
  let witness :=
    (Literal.mem_vars_iff term index).mp hindex
  have hposition := Classical.choose_spec
    (List.get_of_mem (Classical.choose_spec witness).1)
  have hvar := (Classical.choose_spec witness).2
  exact (congrArg Literal.var hposition).trans hvar

/-- Canonical satisfying value of a variable occurring in a term. The fallback
is irrelevant for query blocks whose variables are proved to occur. -/
private noncomputable def satisfyingValue
    (term : List (Literal N)) (index : Fin N) : Bool :=
  if hindex : index ∈ Literal.vars term then
    (term.get (literalPosition term index hindex)).polarity
  else
    false

private theorem satisfyingValue_eq_polarity
    (term : List (Literal N)) (hconsistent : TermConsistent term)
    (literal : Literal N) (hliteral : literal ∈ term) :
    satisfyingValue term literal.var =
      literal.polarity := by
  have hindex : literal.var ∈ Literal.vars term := by
    rw [Literal.mem_vars_iff]
    exact ⟨literal, hliteral, rfl⟩
  rw [satisfyingValue, dite_eq_left hindex]
  apply hconsistent
    (term.get (literalPosition term literal.var hindex))
      (List.get_mem _ _) literal hliteral
  exact literalPosition_var term literal.var hindex

/-- Width-bounded literal position used in generic phase advice. Malformed
phase data falls back to position zero; recoverable phases take the proved
branch. -/
private noncomputable def widthPosition
    (formula : DNF N) (term : List (Literal N))
    (index : Fin N) : Fin (formula.width + 1) :=
  if h : index ∈ Literal.vars term ∧
      term.length ≤ formula.width then
    Fin.castLE (Nat.le_succ_of_le h.2)
      (literalPosition term index h.1)
  else
    0

private def decodeWidthEntry {width : ℕ}
    (term : List (Literal N))
    (entry : Fin (width + 1) × Bool × Bool) :
    Option (Fin N × Bool × Bool) :=
  term[entry.1.val]?.map fun literal =>
    (literal.var, entry.2.1, literal.polarity)

private noncomputable def phaseGamma
    (original : List (Literal N))
    (block : List (Fin N × Bool)) :
    Restriction.On N :=
  DecisionTree.On.assignmentFor
    (block.map Prod.fst) (satisfyingValue original)

private noncomputable def phaseAdvice
    (formula : DNF N) (original : List (Literal N))
    (block : List (Fin N × Bool)) :
    List (Fin (formula.width + 1) × Bool × Bool) :=
  block.mapIdx fun position query =>
    (widthPosition formula original query.1, query.2,
      decide (position + 1 = block.length))

private noncomputable def phaseTranscript
    (original : List (Literal N))
    (block : List (Fin N × Bool)) :
    List (Fin N × Bool × Bool) :=
  block.map fun query =>
    (query.1, query.2,
      satisfyingValue original query.1)

/-- Hybrid target restriction obtained by replacing the first `budget`
switching-path queries by satisfying values, phase by phase. -/
private noncomputable def widthTargetRestriction
    (base : Restriction.On N) :
    List (List (Literal N) × List (Fin N × Bool)) →
      ℕ → Restriction.On N
  | [], _ => base
  | _, 0 => base
  | (original, block) :: phases, budget + 1 =>
      if budget + 1 ≤ block.length then
        Restriction.On.comp
          (phaseGamma original (block.take (budget + 1)))
          base
      else
        Restriction.On.comp
          (phaseGamma original block)
          (widthTargetRestriction
            (Restriction.On.comp base
              (DecisionTree.On.assignmentOfPath block))
            phases (budget + 1 - block.length))

/-- Width advice for the first `budget` queries of a phase list. -/
private noncomputable def widthAdvice
    (formula : DNF N) :
    List (List (Literal N) × List (Fin N × Bool)) →
      ℕ → List (Fin (formula.width + 1) × Bool × Bool)
  | [], _ => []
  | _, 0 => []
  | (original, block) :: phases, budget + 1 =>
      if budget + 1 ≤ block.length then
        phaseAdvice formula original
          (block.take (budget + 1))
      else
        phaseAdvice formula original block ++
          widthAdvice formula phases
            (budget + 1 - block.length)

/-- Query, original branch value, and satisfying value for the first `budget`
queries of a phase list. -/
private noncomputable def widthTranscript :
    List (List (Literal N) × List (Fin N × Bool)) →
      ℕ → List (Fin N × Bool × Bool)
  | [], _ => []
  | _, 0 => []
  | (original, block) :: phases, budget + 1 =>
      if budget + 1 ≤ block.length then
        phaseTranscript original
          (block.take (budget + 1))
      else
        phaseTranscript original block ++
          widthTranscript phases
            (budget + 1 - block.length)

private theorem decodeWidthEntry_widthPosition
    (formula : DNF N) (term : List (Literal N))
    (hterm : term ∈ formula.terms)
    (index : Fin N) (hindex : index ∈ Literal.vars term)
    (path endPhase : Bool) :
    decodeWidthEntry term
        (widthPosition formula term index, path, endPhase) =
      some (index, path, satisfyingValue term index) := by
  have hlength := DNF.length_le_width formula term hterm
  simp [decodeWidthEntry, widthPosition, hindex, hlength,
    satisfyingValue]
  exact literalPosition_var term index hindex

private theorem phaseAdvice_cons
    (formula : DNF N) (original : List (Literal N))
    (query : Fin N × Bool)
    (block : List (Fin N × Bool)) :
    phaseAdvice formula original (query :: block) =
      (widthPosition formula original query.1, query.2,
        decide (block = [])) ::
        phaseAdvice formula original block := by
  apply List.ext_getElem
  · simp [phaseAdvice]
  · intro index hleft hright
    cases index with
    | zero =>
        simp [phaseAdvice, eq_comm,
          List.length_eq_zero_iff]
    | succ index =>
        simp only [phaseAdvice, List.getElem_mapIdx,
          List.getElem_cons_succ]
        congr 2
        simp

/-- Deterministic replay of width advice against the encoded restriction. The
current term is cached within a phase; an end marker causes the next term to be
recovered as the first survivor after overwriting the processed query with its
original branch value. -/
private def decodeWidthPathAux (formula : DNF N) :
    Restriction.On N →
      Option (List (Literal N)) →
      List (Fin (formula.width + 1) × Bool × Bool) →
      List (Fin N × Bool × Bool)
  | _, _, [] => []
  | restriction, current, entry :: entries =>
      let selected := current.orElse fun _ =>
        (formula.firstLiveTerm restriction).map Prod.fst
      match selected.bind fun term =>
          (decodeWidthEntry term entry).map fun query =>
            (term, query) with
      | none => []
      | some (term, query) =>
          query :: decodeWidthPathAux formula
            (Restriction.On.comp
              (Restriction.On.single query.1 query.2.1)
              restriction)
            (if entry.2.2 then none else some term) entries

private theorem decodeWidthPathAux_none_eq_some
    (formula : DNF N) (restriction : Restriction.On N)
    (original reduced : List (Literal N))
    (hfirst : formula.firstLiveTerm restriction =
      some (original, reduced))
    (entry : Fin (formula.width + 1) × Bool × Bool)
    (entries :
      List (Fin (formula.width + 1) × Bool × Bool)) :
    decodeWidthPathAux formula restriction none
        (entry :: entries) =
      decodeWidthPathAux formula restriction (some original)
        (entry :: entries) := by
  simp [decodeWidthPathAux, hfirst]

private theorem decodeWidthPathAux_none_eq_some_of_ne_nil
    (formula : DNF N) (restriction : Restriction.On N)
    (original reduced : List (Literal N))
    (hfirst : formula.firstLiveTerm restriction =
      some (original, reduced))
    (entries :
      List (Fin (formula.width + 1) × Bool × Bool))
    (hnonempty : entries ≠ []) :
    decodeWidthPathAux formula restriction none entries =
      decodeWidthPathAux formula restriction
        (some original) entries := by
  cases entries with
  | nil => contradiction
  | cons entry entries =>
      exact decodeWidthPathAux_none_eq_some
        formula restriction original reduced hfirst
          entry entries

private theorem decodeWidthPathAux_phase
    (formula : DNF N) (original : List (Literal N))
    (hterm : original ∈ formula.terms)
    (block : List (Fin N × Bool))
    (hnonempty : block ≠ [])
    (hvars : ∀ query ∈ block,
      query.1 ∈ Literal.vars original)
    (hnodup : (block.map Prod.fst).Nodup)
    (restriction : Restriction.On N)
    (following :
      List (Fin (formula.width + 1) × Bool × Bool)) :
    decodeWidthPathAux formula restriction (some original)
        (phaseAdvice formula original block ++ following) =
      phaseTranscript original block ++
        decodeWidthPathAux formula
          (Restriction.On.comp
            (DecisionTree.On.assignmentOfPath block)
            restriction)
          none following := by
  induction block generalizing restriction with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons query block ih =>
      have hparts := List.nodup_cons.mp hnodup
      have hqueryVar : query.1 ∈
          Literal.vars original :=
        hvars query (by simp)
      have htailVars : ∀ found ∈ block,
          found.1 ∈ Literal.vars original := by
        intro found hfound
        exact hvars found (by simp [hfound])
      rw [phaseAdvice_cons]
      simp only [List.cons_append, decodeWidthPathAux]
      simp only [Option.orElse, Option.bind_some]
      rw [decodeWidthEntry_widthPosition
        formula original hterm query.1 hqueryVar
          query.2 (decide (block = []))]
      simp only [Option.map_some]
      cases block with
      | nil =>
          simp [phaseTranscript,
            phaseAdvice,
            DecisionTree.On.assignmentOfPath]
      | cons next rest =>
          have hmarker :
              decide (next :: rest = []) = false := by
            simp
          rw [hmarker]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [ih (by simp) htailVars hparts.2]
          simp only [phaseTranscript, List.map_cons,
            List.cons_append]
          congr 1
          congr 1
          congr 1
          apply congrArg (fun updated : Restriction.On N =>
            decodeWidthPathAux formula updated none following)
          rw [← Restriction.On.comp_assoc]
          congr 1
          apply Restriction.On.comp_comm_of_disjoint
          intro index
          by_cases heq : index = query.1
          · subst index
            left
            apply
              DecisionTree.On.assignmentOfPath_apply_of_not_mem_internal
            exact hparts.1
          · right
            exact Restriction.On.single_apply_of_ne
              heq query.2

private theorem firstLiveBlock_original_mem
    (formula : DNF N) (restriction : Restriction.On N)
    (original reduced : List (Literal N))
    (hfirst : formula.firstLiveTerm restriction =
      some (original, reduced)) :
    original ∈ formula.terms := by
  obtain ⟨before, after, hterms, hrestrict, hbefore⟩ :=
    firstLiveTerm_spec_internal formula restriction
      original reduced hfirst
  rw [hterms]
  simp

private theorem firstLiveBlock_free
    (formula : DNF N) (restriction : Restriction.On N)
    (original reduced : List (Literal N))
    (block : List (Fin N × Bool))
    (hfirst : formula.firstLiveTerm restriction =
      some (original, reduced))
    (hqueries : block.map Prod.fst =
      (Literal.vars reduced).toList)
    (query : Fin N × Bool) (hquery : query ∈ block) :
    restriction query.1 = none := by
  obtain ⟨before, after, hterms, hrestrict, hbefore⟩ :=
    firstLiveTerm_spec_internal formula restriction
      original reduced hfirst
  have hindex : query.1 ∈ Literal.vars reduced := by
    have hmem : query.1 ∈ block.map Prod.fst :=
      List.mem_map_of_mem hquery
    rw [hqueries] at hmem
    simpa using hmem
  rw [Literal.mem_vars_iff] at hindex
  obtain ⟨literal, hliteral, hvar⟩ := hindex
  have hfree :=
    (mem_of_mem_restrictTerm restriction
      hrestrict hliteral).2
  exact hvar ▸ hfree

private theorem firstLiveBlock_var_mem_original
    (formula : DNF N) (restriction : Restriction.On N)
    (original reduced : List (Literal N))
    (block : List (Fin N × Bool))
    (hfirst : formula.firstLiveTerm restriction =
      some (original, reduced))
    (hqueries : block.map Prod.fst =
      (Literal.vars reduced).toList)
    (query : Fin N × Bool) (hquery : query ∈ block) :
    query.1 ∈ Literal.vars original := by
  obtain ⟨before, after, hterms, hrestrict, hbefore⟩ :=
    firstLiveTerm_spec_internal formula restriction
      original reduced hfirst
  have hindex : query.1 ∈ Literal.vars reduced := by
    have hmem : query.1 ∈ block.map Prod.fst :=
      List.mem_map_of_mem hquery
    rw [hqueries] at hmem
    simpa using hmem
  rw [Literal.mem_vars_iff] at hindex ⊢
  obtain ⟨literal, hliteral, hvar⟩ := hindex
  have horiginal :=
    (mem_of_mem_restrictTerm restriction
      hrestrict hliteral).1
  exact ⟨literal, horiginal, hvar⟩

private theorem firstLiveBlock_nodup
    (reduced : List (Literal N))
    (block : List (Fin N × Bool))
    (hqueries : block.map Prod.fst =
      (Literal.vars reduced).toList) :
    (block.map Prod.fst).Nodup := by
  rw [hqueries]
  exact Finset.nodup_toList _

private theorem firstLiveBlock_nonempty
    (reduced : List (Literal N))
    (block : List (Fin N × Bool))
    (hnonempty : reduced ≠ [])
    (hqueries : block.map Prod.fst =
      (Literal.vars reduced).toList) :
    block ≠ [] := by
  rcases reduced with _ | ⟨literal, tail⟩
  · contradiction
  · intro hblock
    have hmem :
        literal.var ∈ Literal.vars (literal :: tail) := by
      simp [Literal.mem_vars_iff]
    have hlist :
        literal.var ∈
          (Literal.vars (literal :: tail)).toList := by
      rw [Finset.mem_toList]
      exact hmem
    rw [← hqueries, hblock] at hlist
    simp at hlist

private def RestrictionExtends
    (target base : Restriction.On N) : Prop :=
  ∀ index value, base index = some value →
    target index = some value

private theorem restrictionExtends_refl
    (restriction : Restriction.On N) :
    RestrictionExtends restriction restriction :=
  fun _ _ hvalue => hvalue

private theorem restrictionExtends_trans
    {first second third : Restriction.On N}
    (hfirst : RestrictionExtends second first)
    (hsecond : RestrictionExtends third second) :
    RestrictionExtends third first := by
  intro index value hvalue
  exact hsecond index value
    (hfirst index value hvalue)

private theorem restrictionExtends_comp_left
    (first second : Restriction.On N) :
    RestrictionExtends
      (Restriction.On.comp first second) first := by
  intro index value hvalue
  simp [Restriction.On.comp, hvalue]

private theorem comp_eq_second_of_extends
    (first second : Restriction.On N)
    (hextends : RestrictionExtends second first) :
    Restriction.On.comp first second = second := by
  funext index
  cases hfirst : first index with
  | none => simp [Restriction.On.comp, hfirst]
  | some value =>
      rw [hextends index value hfirst]
      simp [Restriction.On.comp, hfirst]

private theorem phaseGamma_eq_none_of_base_fixed
    (formula : DNF N) (base : Restriction.On N)
    (original reduced : List (Literal N))
    (block used : List (Fin N × Bool))
    (hfirst : formula.firstLiveTerm base =
      some (original, reduced))
    (hqueries : block.map Prod.fst =
      (Literal.vars reduced).toList)
    (hused : ∀ query ∈ used, query ∈ block)
    (index : Fin N) (value : Bool)
    (hfixed : base index = some value) :
    phaseGamma original used index = none := by
  by_cases hindex : index ∈ used.map Prod.fst
  · rw [List.mem_map] at hindex
    obtain ⟨query, hquery, hqueryIndex⟩ := hindex
    have hfree := firstLiveBlock_free formula base
      original reduced block hfirst hqueries query
        (hused query hquery)
    rw [hqueryIndex, hfixed] at hfree
    simp at hfree
  · exact
      DecisionTree.On.assignmentFor_apply_of_not_mem_internal
        (used.map Prod.fst) (satisfyingValue original)
          index hindex

private theorem widthTargetRestriction_extends
    (formula : DNF N) (base : Restriction.On N)
    (phases :
      List (List (Literal N) × List (Fin N × Bool)))
    (hrecoverable :
      RecoverablePhases formula base phases)
    (budget : ℕ) :
    RestrictionExtends
      (widthTargetRestriction base phases budget) base := by
  induction hrecoverable generalizing budget with
  | nil restriction =>
      exact restrictionExtends_refl restriction
  | cons restriction original reduced block phases
      hfirst hnonempty hqueries htail ih =>
      cases budget with
      | zero =>
          exact restrictionExtends_refl restriction
      | succ budget =>
          by_cases hwithin : budget + 1 ≤ block.length
          · simp only [widthTargetRestriction, hwithin,
              ↓reduceIte]
            intro index value hfixed
            have hnone :=
              phaseGamma_eq_none_of_base_fixed
                formula restriction original reduced
                block (block.take (budget + 1))
                hfirst hqueries
                (fun query hquery =>
                  List.mem_of_mem_take hquery)
                index value hfixed
            simp [Restriction.On.comp, hnone, hfixed]
          · simp only [widthTargetRestriction, hwithin,
              ↓reduceIte]
            have hnext :
                RestrictionExtends
                  (Restriction.On.comp restriction
                    (DecisionTree.On.assignmentOfPath block))
                  restriction :=
              restrictionExtends_comp_left _ _
            have htailTarget :=
              ih (budget + 1 - block.length)
            have hbaseTarget :=
              restrictionExtends_trans hnext htailTarget
            intro index value hfixed
            have hnone :=
              phaseGamma_eq_none_of_base_fixed
                formula restriction original reduced
                block block hfirst hqueries
                (fun _ hquery => hquery)
                index value hfixed
            simp [Restriction.On.comp, hnone,
              hbaseTarget index value hfixed]

private theorem widthTarget_first_reduced_survives
    (formula : DNF N) (hconsistent : formula.Consistent)
    (base : Restriction.On N)
    (original reduced : List (Literal N))
    (block : List (Fin N × Bool))
    (phases :
      List (List (Literal N) × List (Fin N × Bool)))
    (hfirst : formula.firstLiveTerm base =
      some (original, reduced))
    (hqueries : block.map Prod.fst =
      (Literal.vars reduced).toList)
    (budget : ℕ) :
    ∃ final,
      restrictTerm
          (widthTargetRestriction base
            ((original, block) :: phases) (budget + 1))
          reduced =
        some final := by
  have horiginalMem :=
    firstLiveBlock_original_mem formula base
      original reduced hfirst
  have htermConsistent :=
    hconsistent original horiginalMem
  obtain ⟨before, after, hterms, hrestrict, hbefore⟩ :=
    firstLiveTerm_spec_internal formula base
      original reduced hfirst
  let target :=
    widthTargetRestriction base
      ((original, block) :: phases) (budget + 1)
  have hsatisfies : ∀ literal ∈ reduced,
      target literal.var = none ∨
        target literal.var = some literal.polarity := by
    intro literal hliteral
    have horiginalLiteral :
        literal ∈ original :=
      (mem_of_mem_restrictTerm base
        hrestrict hliteral).1
    have hbaseFree :
        base literal.var = none :=
      (mem_of_mem_restrictTerm base
        hrestrict hliteral).2
    have hpolarity :
        satisfyingValue original literal.var =
          literal.polarity :=
      satisfyingValue_eq_polarity original
        htermConsistent literal horiginalLiteral
    have hblock : literal.var ∈ block.map Prod.fst := by
      rw [hqueries]
      simpa using
        (Literal.mem_vars_iff reduced literal.var).mpr
          ⟨literal, hliteral, rfl⟩
    by_cases hwithin : budget + 1 ≤ block.length
    · by_cases hused :
          literal.var ∈
            (block.take (budget + 1)).map Prod.fst
      · right
        have hgamma :=
          DecisionTree.On.assignmentFor_apply_of_mem_internal
            ((block.take (budget + 1)).map Prod.fst)
            (satisfyingValue original) literal.var hused
        simp only [target, widthTargetRestriction, hwithin,
          ↓reduceIte, phaseGamma, Restriction.On.comp]
        rw [hgamma, hpolarity]
        rfl
      · left
        have hgamma :=
          DecisionTree.On.assignmentFor_apply_of_not_mem_internal
            ((block.take (budget + 1)).map Prod.fst)
            (satisfyingValue original) literal.var hused
        simp only [target, widthTargetRestriction, hwithin,
          ↓reduceIte, phaseGamma, Restriction.On.comp]
        rw [hgamma, hbaseFree]
        rfl
    · right
      have hgamma :=
        DecisionTree.On.assignmentFor_apply_of_mem_internal
          (block.map Prod.fst)
          (satisfyingValue original) literal.var hblock
      simp [target, widthTargetRestriction, hwithin,
        phaseGamma, hgamma, Restriction.On.comp,
        hpolarity]
  refine ⟨reduced.filter fun literal =>
    target literal.var = none, ?_⟩
  exact (restrictTerm_eq_some_filter_iff
    target reduced).mpr hsatisfies

private theorem widthTarget_firstLiveTerm
    (formula : DNF N) (hconsistent : formula.Consistent)
    (base : Restriction.On N)
    (original reduced : List (Literal N))
    (block : List (Fin N × Bool))
    (phases :
      List (List (Literal N) × List (Fin N × Bool)))
    (hfirst : formula.firstLiveTerm base =
      some (original, reduced))
    (hnonempty : reduced ≠ [])
    (hqueries : block.map Prod.fst =
      (Literal.vars reduced).toList)
    (htail : RecoverablePhases formula
      (Restriction.On.comp base
        (DecisionTree.On.assignmentOfPath block))
      phases)
    (budget : ℕ) :
    ∃ final,
      formula.firstLiveTerm
          (widthTargetRestriction base
            ((original, block) :: phases) (budget + 1)) =
        some (original, final) := by
  let target :=
    widthTargetRestriction base
      ((original, block) :: phases) (budget + 1)
  have hrecoverable :
      RecoverablePhases formula base
        ((original, block) :: phases) :=
    RecoverablePhases.cons base original reduced
      block phases hfirst hnonempty hqueries htail
  have hextends :
      RestrictionExtends target base :=
    widthTargetRestriction_extends formula base
      ((original, block) :: phases) hrecoverable
      (budget + 1)
  obtain ⟨final, hsecond⟩ :=
    widthTarget_first_reduced_survives
      formula hconsistent base original reduced
      block phases hfirst hqueries budget
  have hresult :=
    firstLiveTerm_comp_internal formula base target
      original reduced final hfirst hsecond
  rw [comp_eq_second_of_extends base target
    hextends] at hresult
  exact ⟨final, hresult⟩

private theorem assignmentOfPath_comp_widthTarget_eq_tail
    (formula : DNF N) (base : Restriction.On N)
    (original reduced : List (Literal N))
    (block : List (Fin N × Bool))
    (phases :
      List (List (Literal N) × List (Fin N × Bool)))
    (hfirst : formula.firstLiveTerm base =
      some (original, reduced))
    (hqueries : block.map Prod.fst =
      (Literal.vars reduced).toList)
    (htail : RecoverablePhases formula
      (Restriction.On.comp base
        (DecisionTree.On.assignmentOfPath block))
      phases)
    (budget : ℕ) (hbeyond : ¬budget + 1 ≤ block.length) :
    Restriction.On.comp
        (DecisionTree.On.assignmentOfPath block)
        (widthTargetRestriction base
          ((original, block) :: phases) (budget + 1)) =
      widthTargetRestriction
        (Restriction.On.comp base
          (DecisionTree.On.assignmentOfPath block))
        phases (budget + 1 - block.length) := by
  let path := DecisionTree.On.assignmentOfPath block
  let nextBase := Restriction.On.comp base path
  let tailTarget :=
    widthTargetRestriction nextBase phases
      (budget + 1 - block.length)
  have hnodup : (block.map Prod.fst).Nodup := by
    rw [hqueries]
    exact Finset.nodup_toList _
  have htailExtends :
      RestrictionExtends tailTarget nextBase :=
    widthTargetRestriction_extends formula
      nextBase phases htail
        (budget + 1 - block.length)
  funext index
  by_cases hindex : index ∈ block.map Prod.fst
  · obtain ⟨value, hpath⟩ :=
      DecisionTree.On.assignmentOfPath_apply_eq_some_of_mem_internal
        block hnodup index hindex
    rw [List.mem_map] at hindex
    obtain ⟨query, hquery, hqueryIndex⟩ := hindex
    have hbaseFree :=
      firstLiveBlock_free formula base original reduced
        block hfirst hqueries query hquery
    rw [hqueryIndex] at hbaseFree
    have hnext : nextBase index = some value := by
      simp [nextBase, Restriction.On.comp,
        hbaseFree, path, hpath]
    have htailValue :
        tailTarget index = some value :=
      htailExtends index value hnext
    have hpathValue : path index = some value := by
      simpa [path] using hpath
    simp only [widthTargetRestriction, hbeyond,
      ↓reduceIte, Restriction.On.comp]
    change (path index).or
      ((phaseGamma original block index).or
        (tailTarget index)) = tailTarget index
    rw [hpathValue, htailValue]
    rfl
  · have hpath :
        path index = none := by
      exact
        DecisionTree.On.assignmentOfPath_apply_of_not_mem_internal
          block index hindex
    have hgamma :
        phaseGamma original block index = none := by
      exact
        DecisionTree.On.assignmentFor_apply_of_not_mem_internal
          (block.map Prod.fst) (satisfyingValue original)
            index hindex
    simp only [widthTargetRestriction, hbeyond,
      ↓reduceIte, Restriction.On.comp]
    change (path index).or
      ((phaseGamma original block index).or
        (tailTarget index)) = tailTarget index
    rw [hpath, hgamma]
    rfl

private theorem decodeWidthPathAux_widthTarget
    (formula : DNF N) (hconsistent : formula.Consistent)
    (base : Restriction.On N)
    (phases :
      List (List (Literal N) × List (Fin N × Bool)))
    (hrecoverable :
      RecoverablePhases formula base phases)
    (budget : ℕ)
    (hbudget :
      budget ≤ (phases.flatMap Prod.snd).length) :
    decodeWidthPathAux formula
        (widthTargetRestriction base phases budget) none
        (widthAdvice formula phases budget) =
      widthTranscript phases budget := by
  induction hrecoverable generalizing budget with
  | nil restriction =>
      have hzero : budget = 0 := by
        simpa using hbudget
      subst budget
      rfl
  | cons restriction original reduced block phases
      hfirst hnonempty hqueries htail ih =>
      cases budget with
      | zero => rfl
      | succ budget =>
          have horiginalMem :=
            firstLiveBlock_original_mem formula restriction
              original reduced hfirst
          have hblockNonempty :=
            firstLiveBlock_nonempty reduced block
              hnonempty hqueries
          have hblockVars : ∀ query ∈ block,
              query.1 ∈ Literal.vars original :=
            firstLiveBlock_var_mem_original
              formula restriction original reduced
                block hfirst hqueries
          have hblockNodup :=
            firstLiveBlock_nodup reduced block hqueries
          by_cases hwithin :
              budget + 1 ≤ block.length
          · let used := block.take (budget + 1)
            have husedLength :
                used.length = budget + 1 := by
              simp [used, List.length_take, hwithin]
            have husedNonempty : used ≠ [] := by
              intro hempty
              rw [hempty] at husedLength
              simp at husedLength
            have husedVars : ∀ query ∈ used,
                query.1 ∈ Literal.vars original := by
              intro query hquery
              exact hblockVars query
                (List.mem_of_mem_take hquery)
            have husedNodup :
                (used.map Prod.fst).Nodup := by
              have htake :
                  ((block.map Prod.fst).take
                    (budget + 1)).Nodup :=
                hblockNodup.take
              simpa [used, List.map_take] using htake
            obtain ⟨final, htargetFirst⟩ :=
              widthTarget_firstLiveTerm formula hconsistent
                restriction original reduced block phases
                hfirst hnonempty hqueries htail budget
            have hadviceNonempty :
                phaseAdvice formula original used ≠ [] := by
              intro hempty
              have hlength := congrArg List.length hempty
              simp [phaseAdvice, husedLength] at hlength
            calc
              decodeWidthPathAux formula
                  (widthTargetRestriction restriction
                    ((original, block) :: phases)
                    (budget + 1)) none
                  (widthAdvice formula
                    ((original, block) :: phases)
                    (budget + 1)) =
                decodeWidthPathAux formula
                  (widthTargetRestriction restriction
                    ((original, block) :: phases)
                    (budget + 1)) (some original)
                  (phaseAdvice formula original used) := by
                    simp only [widthAdvice, hwithin,
                      ↓reduceIte]
                    exact
                      decodeWidthPathAux_none_eq_some_of_ne_nil
                        formula _ original final htargetFirst
                          _ hadviceNonempty
              _ = phaseTranscript original used := by
                simpa [decodeWidthPathAux] using
                  decodeWidthPathAux_phase formula original
                    horiginalMem used husedNonempty husedVars
                    husedNodup
                    (widthTargetRestriction restriction
                      ((original, block) :: phases)
                      (budget + 1)) []
              _ = widthTranscript
                  ((original, block) :: phases)
                    (budget + 1) := by
                simp [widthTranscript, hwithin, used]
          · have hremaining :
                budget + 1 - block.length ≤
                  (phases.flatMap Prod.snd).length := by
              have htotal :
                  (((original, block) :: phases).flatMap
                    Prod.snd).length =
                    block.length +
                      (phases.flatMap Prod.snd).length := by
                simp
              rw [htotal] at hbudget
              omega
            obtain ⟨final, htargetFirst⟩ :=
              widthTarget_firstLiveTerm formula hconsistent
                restriction original reduced block phases
                hfirst hnonempty hqueries htail budget
            have hadviceNonempty :
                (phaseAdvice formula original block ++
                  widthAdvice formula phases
                    (budget + 1 - block.length)) ≠ [] := by
              intro hempty
              have hlength := congrArg List.length hempty
              simp [phaseAdvice] at hlength
              exact hblockNonempty hlength.1
            have htailDecode :=
              ih (budget + 1 - block.length) hremaining
            calc
              decodeWidthPathAux formula
                  (widthTargetRestriction restriction
                    ((original, block) :: phases)
                    (budget + 1)) none
                  (widthAdvice formula
                    ((original, block) :: phases)
                    (budget + 1)) =
                decodeWidthPathAux formula
                  (widthTargetRestriction restriction
                    ((original, block) :: phases)
                    (budget + 1)) (some original)
                  (phaseAdvice formula original block ++
                    widthAdvice formula phases
                      (budget + 1 - block.length)) := by
                    simp only [widthAdvice, hwithin,
                      ↓reduceIte]
                    exact
                      decodeWidthPathAux_none_eq_some_of_ne_nil
                        formula _ original final htargetFirst
                          _ hadviceNonempty
              _ = phaseTranscript original block ++
                  decodeWidthPathAux formula
                    (Restriction.On.comp
                      (DecisionTree.On.assignmentOfPath block)
                      (widthTargetRestriction restriction
                        ((original, block) :: phases)
                        (budget + 1)))
                    none
                    (widthAdvice formula phases
                      (budget + 1 - block.length)) := by
                exact decodeWidthPathAux_phase formula original
                  horiginalMem block hblockNonempty hblockVars
                    hblockNodup
                    (widthTargetRestriction restriction
                      ((original, block) :: phases)
                      (budget + 1))
                    (widthAdvice formula phases
                      (budget + 1 - block.length))
              _ = phaseTranscript original block ++
                  widthTranscript phases
                    (budget + 1 - block.length) := by
                rw [
                  assignmentOfPath_comp_widthTarget_eq_tail
                    formula restriction original reduced
                      block phases hfirst hqueries htail
                        budget hwithin,
                  htailDecode]
              _ = widthTranscript
                  ((original, block) :: phases)
                    (budget + 1) := by
                simp [widthTranscript, hwithin]

private theorem assignmentOfPath_map_satisfying
    (path : List (Fin N × Bool)) (input : BitString N) :
    DecisionTree.On.assignmentOfPath
        (path.map fun query => (query.1, input query.1)) =
      DecisionTree.On.assignmentFor (path.map Prod.fst) input := by
  induction path with
  | nil => rfl
  | cons query path ih =>
      simp [DecisionTree.On.assignmentOfPath,
        DecisionTree.On.assignmentFor, ih]

private theorem assignmentFor_overwrites_path
    (path : List (Fin N × Bool)) (input : BitString N)
    (tail base : Restriction.On N) :
    Restriction.On.comp
        (DecisionTree.On.assignmentFor
          (path.map Prod.fst) input)
        (Restriction.On.comp tail
          (Restriction.On.comp base
            (DecisionTree.On.assignmentOfPath path))) =
      Restriction.On.comp
        (DecisionTree.On.assignmentFor
          (path.map Prod.fst) input)
        (Restriction.On.comp tail base) := by
  funext index
  by_cases hindex : index ∈ path.map Prod.fst
  · have hvalue :=
      DecisionTree.On.assignmentFor_apply_of_mem_internal
        (path.map Prod.fst) input index hindex
    simp [Restriction.On.comp, hvalue]
  · have hgamma :=
      DecisionTree.On.assignmentFor_apply_of_not_mem_internal
        (path.map Prod.fst) input index hindex
    have hpath :=
      DecisionTree.On.assignmentOfPath_apply_of_not_mem_internal
        path index hindex
    simp [Restriction.On.comp, hgamma, hpath]

private theorem assignmentOfPath_ofFn_embedding
    (queries : Fin s ↪ Fin N) (values : Fin s → Bool) :
    DecisionTree.On.assignmentOfPath
        (List.ofFn fun position => (queries position, values position)) =
      RandomRestriction.assignmentAlong queries values := by
  let path :=
    List.ofFn fun position => (queries position, values position)
  change DecisionTree.On.assignmentOfPath path =
    RandomRestriction.assignmentAlong queries values
  have hvars : path.map Prod.fst = List.ofFn queries := by
    simp [path, List.map_ofFn, Function.comp_def]
  have hnodup : (path.map Prod.fst).Nodup := by
    rw [hvars, List.nodup_ofFn]
    exact queries.injective
  funext index
  cases hposition :
      RandomRestriction.positionOf queries index with
  | none =>
      have hnot : index ∉ path.map Prod.fst := by
        rw [hvars, List.mem_ofFn]
        intro hexists
        obtain ⟨position, hquery⟩ := hexists
        have hsome :=
          RandomRestriction.positionOf_apply_internal
            queries position
        rw [hquery, hposition] at hsome
        simp at hsome
      rw [
        DecisionTree.On.assignmentOfPath_apply_of_not_mem_internal
          path index hnot]
      simp [RandomRestriction.assignmentAlong, hposition]
  | some position =>
      have hquery :=
        RandomRestriction.positionOf_eq_some_internal
          queries index position hposition
      have hmem :
          (queries position, values position) ∈ path := by
        simp [path, List.mem_ofFn]
      have hpath :=
        DecisionTree.On.assignmentOfPath_apply_of_mem_internal
          path hnodup (queries position, values position) hmem
      rw [← hquery, hpath]
      simp [RandomRestriction.assignmentAlong,
        RandomRestriction.positionOf_apply_internal]

private theorem length_widthAdvice
    (formula : DNF N)
    (phases :
      List (List (Literal N) × List (Fin N × Bool)))
    (budget : ℕ)
    (hbudget :
      budget ≤ (phases.flatMap Prod.snd).length) :
    (widthAdvice formula phases budget).length = budget := by
  induction phases generalizing budget with
  | nil =>
      have hzero : budget = 0 := by
        simpa using hbudget
      subst budget
      rfl
  | cons phase phases ih =>
      rcases phase with ⟨original, block⟩
      cases budget with
      | zero => rfl
      | succ budget =>
          by_cases hwithin : budget + 1 ≤ block.length
          · simp [widthAdvice, hwithin, phaseAdvice,
              List.length_take]
          · have hremaining :
                budget + 1 - block.length ≤
                  (phases.flatMap Prod.snd).length := by
              simp only [List.flatMap_cons,
                List.length_append] at hbudget
              omega
            simp [widthAdvice, hwithin, phaseAdvice,
              ih _ hremaining]
            omega

private theorem length_widthTranscript
    (phases :
      List (List (Literal N) × List (Fin N × Bool)))
    (budget : ℕ)
    (hbudget :
      budget ≤ (phases.flatMap Prod.snd).length) :
    (widthTranscript phases budget).length = budget := by
  induction phases generalizing budget with
  | nil =>
      have hzero : budget = 0 := by
        simpa using hbudget
      subst budget
      rfl
  | cons phase phases ih =>
      rcases phase with ⟨original, block⟩
      cases budget with
      | zero => rfl
      | succ budget =>
          by_cases hwithin : budget + 1 ≤ block.length
          · simp [widthTranscript, hwithin, phaseTranscript,
              List.length_take]
          · have hremaining :
                budget + 1 - block.length ≤
                  (phases.flatMap Prod.snd).length := by
              simp only [List.flatMap_cons,
                List.length_append] at hbudget
              omega
            simp [widthTranscript, hwithin, phaseTranscript,
              ih _ hremaining]
            omega

private theorem map_query_widthTranscript
    (phases :
      List (List (Literal N) × List (Fin N × Bool)))
    (budget : ℕ) :
    (widthTranscript phases budget).map
        (fun entry => (entry.1, entry.2.1)) =
      (phases.flatMap Prod.snd).take budget := by
  induction phases generalizing budget with
  | nil => simp [widthTranscript]
  | cons phase phases ih =>
      rcases phase with ⟨original, block⟩
      cases budget with
      | zero => rfl
      | succ budget =>
          by_cases hwithin : budget + 1 ≤ block.length
          · simp [widthTranscript, hwithin, phaseTranscript,
              List.map_map, Function.comp_def,
              List.take_append_of_le_length hwithin]
          · have hlength : block.length ≤ budget + 1 := by
              omega
            simp [widthTranscript, hwithin, phaseTranscript,
              List.map_map, Function.comp_def, ih,
              List.take_append, hlength]

/-- The recursive hybrid target is exactly the base restriction with the
query coordinates in its transcript overwritten by their satisfying values. -/
private theorem widthTargetRestriction_eq_transcript
    (formula : DNF N) (base : Restriction.On N)
    (phases :
      List (List (Literal N) × List (Fin N × Bool)))
    (hrecoverable :
      RecoverablePhases formula base phases)
    (budget : ℕ) :
    widthTargetRestriction base phases budget =
      Restriction.On.comp
        (DecisionTree.On.assignmentOfPath
          ((widthTranscript phases budget).map fun entry =>
            (entry.1, entry.2.2)))
        base := by
  induction hrecoverable generalizing budget with
  | nil restriction =>
      simp [widthTargetRestriction, widthTranscript,
        DecisionTree.On.assignmentOfPath]
  | cons restriction original reduced block phases
      hfirst hnonempty hqueries htail ih =>
      cases budget with
      | zero =>
          simp [widthTargetRestriction, widthTranscript,
            DecisionTree.On.assignmentOfPath]
      | succ budget =>
          by_cases hwithin : budget + 1 ≤ block.length
          · simpa [widthTargetRestriction, widthTranscript, hwithin,
              phaseTranscript, phaseGamma, List.map_map,
              Function.comp_def] using (congrArg
                (fun target : Restriction.On N =>
                  Restriction.On.comp target restriction)
                (assignmentOfPath_map_satisfying
                  (block.take (budget + 1))
                  (satisfyingValue original))).symm
          · have hgamma :
                DecisionTree.On.assignmentOfPath
                    ((phaseTranscript original block).map fun entry =>
                      (entry.1, entry.2.2)) =
                  phaseGamma original block := by
              simpa [phaseTranscript, phaseGamma, List.map_map,
                Function.comp_def] using
                  assignmentOfPath_map_satisfying block
                    (satisfyingValue original)
            simp only [widthTargetRestriction, hwithin, ↓reduceIte,
              widthTranscript, List.map_append,
              DecisionTree.On.assignmentOfPath_append_internal]
            rw [ih, hgamma]
            simpa only [phaseGamma, Restriction.On.comp_assoc] using
              assignmentFor_overwrites_path block
                (satisfyingValue original)
                (DecisionTree.On.assignmentOfPath
                  ((widthTranscript phases
                    (budget + 1 - block.length)).map fun entry =>
                      (entry.1, entry.2.2))) restriction

private theorem evalTerm_eq_of_agree
    (term : List (Literal N)) (left right : BitString N)
    (hagree : ∀ literal ∈ term,
      left literal.var = right literal.var) :
    (term.all fun literal => literal.eval left) =
      term.all fun literal => literal.eval right := by
  induction term with
  | nil => rfl
  | cons literal term ih =>
      simp only [List.all_cons]
      have hhead := hagree literal (by simp)
      have htail : ∀ found ∈ term,
          left found.var = right found.var :=
        fun found hfound => hagree found (by simp [hfound])
      have hliteral :
          literal.eval left = literal.eval right := by
        simp only [Literal.eval]
        rw [hhead]
      rw [hliteral, ih htail]

private theorem eval_eq_of_agree_internal
    (formula : DNF N) (left right : BitString N)
    (hagree : ∀ index ∈ formula.vars,
      left index = right index) :
    formula.eval left = formula.eval right := by
  rcases formula with ⟨terms⟩
  simp only [DNF.eval]
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      simp only [List.any_cons]
      have hterm : ∀ literal ∈ term,
          left literal.var = right literal.var := by
        intro literal hliteral
        apply hagree
        rw [DNF.mem_vars_iff]
        exact ⟨term, by simp, literal, hliteral, rfl⟩
      have hterms :
          (⟨terms⟩ : DNF N).eval left =
            (⟨terms⟩ : DNF N).eval right := by
        apply ih
        intro index hindex
        apply hagree
        rw [DNF.mem_vars_iff] at hindex ⊢
        obtain ⟨found, hfound, literal, hliteral, hvar⟩ :=
          hindex
        exact ⟨found, by simp [hfound], literal, hliteral, hvar⟩
      rw [evalTerm_eq_of_agree term left right hterm]
      simpa only [DNF.eval] using
        congrArg
          (fun value =>
            (term.all fun literal => literal.eval right) || value)
          hterms

private theorem selected_mem_vars
    (literal : Literal N) (term : List (Literal N))
    (terms : List (List (Literal N))) :
    literal.var ∈
      (⟨(literal :: term) :: terms⟩ : DNF N).vars := by
  rw [DNF.mem_vars_iff]
  exact ⟨literal :: term, by simp, literal, by simp, rfl⟩

private theorem filter_single_eq_erase
    (support : Finset (Fin N)) (index : Fin N)
    (value : Bool) :
    support.filter (fun other =>
      Restriction.On.single index value other = none) =
        support.erase index := by
  ext other
  by_cases heq : other = index
  · subst other
    simp
  · simp [Restriction.On.single, heq]

private theorem card_vars_restrict_single_lt
    (formula : DNF N) (index : Fin N)
    (hindex : index ∈ formula.vars) (value : Bool) :
    (formula.restrict
      (Restriction.On.single index value)).vars.card <
        formula.vars.card := by
  have hsubset :=
    DNF.vars_restrict_subset_filter
      (Restriction.On.single index value) formula
  have hcard :
      (formula.restrict
        (Restriction.On.single index value)).vars.card ≤
          (formula.vars.filter fun other =>
            Restriction.On.single index value other = none).card :=
    Finset.card_le_card hsubset
  rw [filter_single_eq_erase formula.vars index value,
    Finset.card_erase_of_mem hindex] at hcard
  have hpositive : 0 < formula.vars.card :=
    Finset.card_pos.mpr ⟨index, hindex⟩
  omega

theorem vars_canonicalDecisionTreeAux_subset_internal
    (fuel : ℕ) (formula : DNF N) :
    (canonicalDecisionTreeAux fuel formula).vars ⊆
      formula.vars := by
  induction fuel generalizing formula with
  | zero =>
      simp [canonicalDecisionTreeAux, DecisionTree.On.vars]
  | succ fuel ih =>
      rcases formula with ⟨terms⟩
      cases terms with
      | nil =>
          simp [canonicalDecisionTreeAux,
            DecisionTree.On.vars]
      | cons term terms =>
          cases term with
          | nil =>
              simp [canonicalDecisionTreeAux,
                DecisionTree.On.vars]
          | cons literal tail =>
              let formula : DNF N :=
                ⟨(literal :: tail) :: terms⟩
              simp only [canonicalDecisionTreeAux,
                DecisionTree.On.vars]
              intro queried hqueried
              simp only [Finset.mem_insert,
                Finset.mem_union] at hqueried
              rcases hqueried with hroot | hfalse | htrue
              · subst queried
                exact selected_mem_vars literal tail terms
              · have hchild := ih
                  (formula.restrict
                    (Restriction.On.single
                      literal.var false)) hfalse
                have hsurvives :=
                  DNF.vars_restrict_subset_filter
                    (Restriction.On.single literal.var false)
                    formula hchild
                exact (Finset.mem_filter.mp hsurvives).1
              · have hchild := ih
                  (formula.restrict
                    (Restriction.On.single
                      literal.var true)) htrue
                have hsurvives :=
                  DNF.vars_restrict_subset_filter
                    (Restriction.On.single literal.var true)
                    formula hchild
                exact (Finset.mem_filter.mp hsurvives).1

theorem pathReadOnce_canonicalDecisionTreeAux_internal
    (fuel : ℕ) (formula : DNF N) :
    (canonicalDecisionTreeAux fuel formula).PathReadOnce := by
  induction fuel generalizing formula with
  | zero =>
      simp [canonicalDecisionTreeAux,
        DecisionTree.On.PathReadOnce]
  | succ fuel ih =>
      rcases formula with ⟨terms⟩
      cases terms with
      | nil =>
          simp [canonicalDecisionTreeAux,
            DecisionTree.On.PathReadOnce]
      | cons term terms =>
          cases term with
          | nil =>
              simp [canonicalDecisionTreeAux,
                DecisionTree.On.PathReadOnce]
          | cons literal tail =>
              let formula : DNF N :=
                ⟨(literal :: tail) :: terms⟩
              simp only [canonicalDecisionTreeAux,
                DecisionTree.On.PathReadOnce]
              refine ⟨?_, ?_, ih _, ih _⟩
              · intro hmem
                have hsub :=
                  vars_canonicalDecisionTreeAux_subset_internal fuel
                    (formula.restrict
                      (Restriction.On.single
                        literal.var false)) hmem
                have hfree :=
                  DNF.vars_restrict_subset_filter
                    (Restriction.On.single literal.var false)
                    formula hsub
                have hnone := (Finset.mem_filter.mp hfree).2
                simp [Restriction.On.single] at hnone
              · intro hmem
                have hsub :=
                  vars_canonicalDecisionTreeAux_subset_internal fuel
                    (formula.restrict
                      (Restriction.On.single
                        literal.var true)) hmem
                have hfree :=
                  DNF.vars_restrict_subset_filter
                    (Restriction.On.single literal.var true)
                    formula hsub
                have hnone := (Finset.mem_filter.mp hfree).2
                simp [Restriction.On.single] at hnone

theorem eval_canonicalDecisionTreeAux_internal
    (fuel : ℕ) (formula : DNF N)
    (hcard : formula.vars.card ≤ fuel)
    (input : BitString N) :
    (canonicalDecisionTreeAux fuel formula).eval input =
      formula.eval input := by
  induction fuel generalizing formula with
  | zero =>
      have hzero : formula.vars = ∅ := by
        apply Finset.card_eq_zero.mp
        omega
      rw [canonicalDecisionTreeAux]
      apply eval_eq_of_agree_internal
      intro index hindex
      simp [hzero] at hindex
  | succ fuel ih =>
      rcases formula with ⟨terms⟩
      cases terms with
      | nil => rfl
      | cons term terms =>
          cases term with
          | nil =>
              simp [canonicalDecisionTreeAux, DNF.eval,
                DecisionTree.On.eval]
          | cons literal tail =>
              let formula : DNF N :=
                ⟨(literal :: tail) :: terms⟩
              have hselected :
                  literal.var ∈ formula.vars :=
                selected_mem_vars literal tail terms
              have hformulaCard :
                  formula.vars.card ≤ fuel + 1 := by
                simpa [formula] using hcard
              have hfalse :
                  (formula.restrict
                    (Restriction.On.single literal.var false)).vars.card ≤
                      fuel := by
                have hlt :=
                  card_vars_restrict_single_lt formula literal.var
                    hselected false
                omega
              have htrue :
                  (formula.restrict
                    (Restriction.On.single literal.var true)).vars.card ≤
                      fuel := by
                have hlt :=
                  card_vars_restrict_single_lt formula literal.var
                    hselected true
                omega
              cases hinput : input literal.var
              · simp only [canonicalDecisionTreeAux,
                  DecisionTree.On.eval, hinput, Bool.false_eq_true,
                  ↓reduceIte]
                rw [ih _ hfalse, DNF.eval_restrict,
                  Restriction.On.applyTo_single]
                apply congrArg formula.eval
                funext index
                by_cases heq : index = literal.var
                · subst index
                  simp [Function.update, hinput]
                · simp [Function.update, heq]
              · simp only [canonicalDecisionTreeAux,
                  DecisionTree.On.eval, hinput, ↓reduceIte]
                rw [ih _ htrue, DNF.eval_restrict,
                  Restriction.On.applyTo_single]
                apply congrArg formula.eval
                funext index
                by_cases heq : index = literal.var
                · subst index
                  simp [Function.update, hinput]
                · simp [Function.update, heq]

theorem depth_canonicalDecisionTreeAux_le_internal
    (fuel : ℕ) (formula : DNF N) :
    (canonicalDecisionTreeAux fuel formula).depth ≤ fuel := by
  induction fuel generalizing formula with
  | zero =>
      simp [canonicalDecisionTreeAux, DecisionTree.On.depth]
  | succ fuel ih =>
      rcases formula with ⟨terms⟩
      cases terms with
      | nil =>
          simp [canonicalDecisionTreeAux, DecisionTree.On.depth]
      | cons term terms =>
          cases term with
          | nil =>
              simp [canonicalDecisionTreeAux, DecisionTree.On.depth]
          | cons literal tail =>
              simp only [canonicalDecisionTreeAux,
                DecisionTree.On.depth]
              exact Nat.add_le_add_right
                (max_le (ih _) (ih _)) 1

theorem eval_canonicalDecisionTree_internal
    (formula : DNF N) (input : BitString N) :
    formula.canonicalDecisionTree.eval input =
      formula.eval input := by
  exact eval_canonicalDecisionTreeAux_internal
    formula.vars.card formula (le_refl _) input

theorem depth_canonicalDecisionTree_le_vars_internal
    (formula : DNF N) :
    formula.canonicalDecisionTree.depth ≤
      formula.vars.card :=
  depth_canonicalDecisionTreeAux_le_internal
    formula.vars.card formula

theorem depth_canonicalDecisionTree_le_arity_internal
    (formula : DNF N) :
    formula.canonicalDecisionTree.depth ≤ N := by
  exact (depth_canonicalDecisionTree_le_vars_internal formula).trans
    ((Finset.card_le_univ formula.vars).trans_eq
      (Fintype.card_fin N))

theorem vars_canonicalDecisionTree_subset_internal
    (formula : DNF N) :
    formula.canonicalDecisionTree.vars ⊆ formula.vars :=
  vars_canonicalDecisionTreeAux_subset_internal
    formula.vars.card formula

theorem pathReadOnce_canonicalDecisionTree_internal
    (formula : DNF N) :
    formula.canonicalDecisionTree.PathReadOnce :=
  pathReadOnce_canonicalDecisionTreeAux_internal
    formula.vars.card formula

theorem vars_switchingDecisionTreeAux_subset_internal
    (fuel : ℕ) (formula : DNF N) :
    (switchingDecisionTreeAux fuel formula).vars ⊆
      formula.vars := by
  induction fuel generalizing formula with
  | zero =>
      simp [switchingDecisionTreeAux, DecisionTree.On.vars]
  | succ fuel ih =>
      rcases formula with ⟨terms⟩
      cases terms with
      | nil =>
          simp [switchingDecisionTreeAux, DecisionTree.On.vars]
      | cons term terms =>
          cases term with
          | nil =>
              simp [switchingDecisionTreeAux, DecisionTree.On.vars]
          | cons literal tail =>
              let formula : DNF N :=
                ⟨(literal :: tail) :: terms⟩
              let queries :=
                (Literal.vars (literal :: tail)).toList
              let continuation : Restriction.On N →
                  DecisionTree.On N := fun branch =>
                let assignment :=
                  DecisionTree.On.assignmentFor queries
                    (branch.applyTo fun _ => false)
                if (literal :: tail).all (fun found =>
                    found.eval
                      (assignment.applyTo fun _ => false)) then
                  .leaf true
                else
                  switchingDecisionTreeAux fuel
                    (formula.restrict assignment)
              have hcontinuation : ∀ branch,
                  (continuation branch).vars ⊆ formula.vars := by
                intro branch
                dsimp only [continuation]
                split
                · simp [DecisionTree.On.vars]
                · exact (ih _).trans
                    ((DNF.vars_restrict_subset_filter _ formula).trans
                      (Finset.filter_subset _ _))
              have hblock :=
                DecisionTree.On.vars_queryAll_subset_internal
                  queries continuation formula.vars hcontinuation
              have hunion :
                  queries.toFinset ∪ formula.vars = formula.vars := by
                apply Finset.union_eq_right.mpr
                intro index hindex
                have hterm :
                    index ∈ Literal.vars (literal :: tail) := by
                  simpa [queries] using hindex
                rw [DNF.mem_vars_iff]
                rw [Literal.mem_vars_iff] at hterm
                obtain ⟨found, hfound, hvar⟩ := hterm
                exact ⟨literal :: tail, by simp [formula], found,
                  hfound, hvar⟩
              simpa [formula, queries, continuation,
                switchingDecisionTreeAux, hunion] using hblock

theorem pathReadOnce_switchingDecisionTreeAux_internal
    (fuel : ℕ) (formula : DNF N) :
    (switchingDecisionTreeAux fuel formula).PathReadOnce := by
  induction fuel generalizing formula with
  | zero =>
      simp [switchingDecisionTreeAux,
        DecisionTree.On.PathReadOnce]
  | succ fuel ih =>
      rcases formula with ⟨terms⟩
      cases terms with
      | nil =>
          simp [switchingDecisionTreeAux,
            DecisionTree.On.PathReadOnce]
      | cons term terms =>
          cases term with
          | nil =>
              simp [switchingDecisionTreeAux,
                DecisionTree.On.PathReadOnce]
          | cons literal tail =>
              let formula : DNF N :=
                ⟨(literal :: tail) :: terms⟩
              let queries :=
                (Literal.vars (literal :: tail)).toList
              let continuation : Restriction.On N →
                  DecisionTree.On N := fun branch =>
                let assignment :=
                  DecisionTree.On.assignmentFor queries
                    (branch.applyTo fun _ => false)
                if (literal :: tail).all (fun found =>
                    found.eval
                      (assignment.applyTo fun _ => false)) then
                  .leaf true
                else
                  switchingDecisionTreeAux fuel
                    (formula.restrict assignment)
              have hreadOnce : ∀ branch,
                  (continuation branch).PathReadOnce := by
                intro branch
                dsimp only [continuation]
                split
                · simp [DecisionTree.On.PathReadOnce]
                · exact ih _
              have hdisjoint : ∀ branch,
                  Disjoint queries.toFinset
                    (continuation branch).vars := by
                intro branch
                dsimp only [continuation]
                split
                · simp [DecisionTree.On.vars]
                · rw [Finset.disjoint_left]
                  intro index hquery hchild
                  have hsub :=
                    vars_switchingDecisionTreeAux_subset_internal
                      fuel _ hchild
                  have hfree :=
                    DNF.vars_restrict_subset_filter
                      (DecisionTree.On.assignmentFor queries
                        (branch.applyTo fun _ => false))
                      formula hsub
                  have hnone := (Finset.mem_filter.mp hfree).2
                  have hmem : index ∈ queries := by
                    simpa using hquery
                  have hsome :=
                    DecisionTree.On.assignmentFor_apply_of_mem_internal
                      queries (branch.applyTo fun _ => false)
                      index hmem
                  rw [hsome] at hnone
                  simp at hnone
              simpa [formula, queries, continuation,
                switchingDecisionTreeAux] using
                DecisionTree.On.pathReadOnce_queryAll_internal
                  queries continuation (Finset.nodup_toList _)
                    hreadOnce hdisjoint

private theorem evalTerm_assignmentFor_vars
    (term : List (Literal N)) (input fallback : BitString N) :
    term.all (fun literal => literal.eval
        ((DecisionTree.On.assignmentFor
          (Literal.vars term).toList input).applyTo fallback)) =
      term.all (fun literal => literal.eval input) := by
  apply evalTerm_eq_of_agree
  intro literal hliteral
  have hmem : literal.var ∈ Literal.vars term := by
    rw [Literal.mem_vars_iff]
    exact ⟨literal, hliteral, rfl⟩
  have hlist :
      literal.var ∈ (Literal.vars term).toList := by
    simpa using hmem
  unfold Restriction.On.applyTo
  rw [DecisionTree.On.assignmentFor_apply_of_mem_internal
    (Literal.vars term).toList input literal.var hlist]
  rfl

private theorem card_vars_restrict_assignmentFor_lt
    (formula : DNF N) (queries : List (Fin N))
    (input : BitString N) (index : Fin N)
    (hformula : index ∈ formula.vars)
    (hqueries : index ∈ queries) :
    (formula.restrict
      (DecisionTree.On.assignmentFor queries input)).vars.card <
        formula.vars.card := by
  have hsubset :
      (formula.restrict
        (DecisionTree.On.assignmentFor queries input)).vars ⊆
          formula.vars.erase index := by
    intro found hfound
    have hfree :=
      DNF.vars_restrict_subset_filter
        (DecisionTree.On.assignmentFor queries input)
        formula hfound
    have horiginal := (Finset.mem_filter.mp hfree).1
    have hnone := (Finset.mem_filter.mp hfree).2
    have hne : found ≠ index := by
      intro heq
      subst found
      have hsome :=
        DecisionTree.On.assignmentFor_apply_of_mem_internal
          queries input index hqueries
      rw [hsome] at hnone
      simp at hnone
    exact Finset.mem_erase.mpr ⟨hne, horiginal⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_erase_of_mem hformula] at hcard
  have hpositive : 0 < formula.vars.card :=
    Finset.card_pos.mpr ⟨index, hformula⟩
  omega

theorem eval_switchingDecisionTreeAux_internal
    (fuel : ℕ) (formula : DNF N)
    (hcard : formula.vars.card ≤ fuel)
    (input : BitString N) :
    (switchingDecisionTreeAux fuel formula).eval input =
      formula.eval input := by
  induction fuel generalizing formula with
  | zero =>
      have hzero : formula.vars = ∅ := by
        apply Finset.card_eq_zero.mp
        omega
      rw [switchingDecisionTreeAux]
      apply eval_eq_of_agree_internal
      intro index hindex
      simp [hzero] at hindex
  | succ fuel ih =>
      rcases formula with ⟨terms⟩
      cases terms with
      | nil => rfl
      | cons term terms =>
          cases term with
          | nil =>
              simp [switchingDecisionTreeAux, DNF.eval,
                DecisionTree.On.eval]
          | cons literal tail =>
              let formula : DNF N :=
                ⟨(literal :: tail) :: terms⟩
              let queries :=
                (Literal.vars (literal :: tail)).toList
              let assignment :=
                DecisionTree.On.assignmentFor queries input
              have hselected :
                  literal.var ∈ formula.vars := by
                exact selected_mem_vars literal tail terms
              have hquery : literal.var ∈ queries := by
                simp [queries, Literal.mem_vars_iff]
              have hformulaCard :
                  formula.vars.card ≤ fuel + 1 := by
                simpa [formula] using hcard
              have hchild :
                  (formula.restrict assignment).vars.card ≤ fuel := by
                have hlt :
                    (formula.restrict assignment).vars.card <
                      formula.vars.card := by
                  simpa [assignment] using
                    card_vars_restrict_assignmentFor_lt
                      formula queries input literal.var
                        hselected hquery
                omega
              simp only [switchingDecisionTreeAux]
              rw [DecisionTree.On.eval_queryAll_internal]
              simp only [
                DecisionTree.On.assignmentFor_reapply_internal,
                evalTerm_assignmentFor_vars]
              by_cases hterm : (literal :: tail).all
                  (fun found => found.eval input) = true
              · simp [hterm, DecisionTree.On.eval, DNF.eval]
              · simp only [hterm]
                change (switchingDecisionTreeAux fuel
                  (formula.restrict assignment)).eval input =
                    formula.eval input
                rw [ih _ hchild, DNF.eval_restrict,
                  DecisionTree.On.assignmentFor_applyTo_internal]

theorem eval_switchingDecisionTree_internal
    (formula : DNF N) (input : BitString N) :
    formula.switchingDecisionTree.eval input =
      formula.eval input :=
  eval_switchingDecisionTreeAux_internal
    formula.vars.card formula (le_refl _) input

theorem vars_switchingDecisionTree_subset_internal
    (formula : DNF N) :
    formula.switchingDecisionTree.vars ⊆ formula.vars :=
  vars_switchingDecisionTreeAux_subset_internal
    formula.vars.card formula

theorem pathReadOnce_switchingDecisionTree_internal
    (formula : DNF N) :
    formula.switchingDecisionTree.PathReadOnce :=
  pathReadOnce_switchingDecisionTreeAux_internal
    formula.vars.card formula

theorem depth_switchingDecisionTree_le_vars_internal
    (formula : DNF N) :
    formula.switchingDecisionTree.depth ≤
      formula.vars.card := by
  exact (DecisionTree.On.depth_le_card_vars_of_pathReadOnce_internal
    formula.switchingDecisionTree
    (pathReadOnce_switchingDecisionTree_internal formula)).trans
      (Finset.card_le_card
        (vars_switchingDecisionTree_subset_internal formula))

theorem depth_switchingDecisionTree_le_arity_internal
    (formula : DNF N) :
    formula.switchingDecisionTree.depth ≤ N := by
  exact (depth_switchingDecisionTree_le_vars_internal formula).trans
    ((Finset.card_le_univ formula.vars).trans_eq
      (Fintype.card_fin N))

private noncomputable def badTree
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    DecisionTree.On N :=
  formula.switchingDecisionTreeUnder
    (RandomRestriction.decode bad.1)

private theorem queryCount_le_badTree
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    queryCount ≤ (badTree formula bad).depth := by
  simpa [badTree, switchingBad] using bad.property

private theorem badTree_pathReadOnce
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    (badTree formula bad).PathReadOnce := by
  simpa [badTree,
    switchingDecisionTreeUnder_eq_internal] using
    pathReadOnce_switchingDecisionTree_internal
      (formula.restrict (RandomRestriction.decode bad.1))

private noncomputable def badQueries
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    Fin queryCount ↪ Fin N :=
  DecisionTree.On.deepPrefixEmbeddingInternal
    (badTree formula bad) queryCount
    (queryCount_le_badTree formula bad)
    (badTree_pathReadOnce formula bad)

private noncomputable def badValues
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    Fin queryCount → Bool :=
  DecisionTree.On.deepPrefixValuesInternal
    (badTree formula bad) queryCount
    (queryCount_le_badTree formula bad)

private noncomputable def badPhaseEntries
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    List (PhaseEntry N) :=
  let restriction := RandomRestriction.decode bad.1
  annotatePhases
    (switchingPhasesAux
      (formula.restrict restriction).vars.card
      formula restriction)

private noncomputable def badPhases
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    List (List (Literal N) × List (Fin N × Bool)) :=
  let restriction := RandomRestriction.decode bad.1
  switchingPhasesAux
    (formula.restrict restriction).vars.card
    formula restriction

private theorem badPhaseEntries_eq_annotate
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    badPhaseEntries formula bad =
      annotatePhases (badPhases formula bad) := by
  rfl

private theorem recoverable_badPhases
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    RecoverablePhases formula
      (RandomRestriction.decode bad.1)
      (badPhases formula bad) := by
  exact recoverable_switchingPhasesAux
    (formula.restrict
      (RandomRestriction.decode bad.1)).vars.card
    formula (RandomRestriction.decode bad.1)

private theorem flatMap_badPhases_eq_deepPath
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    (badPhases formula bad).flatMap Prod.snd =
      (badTree formula bad).deepPath := by
  simpa [badPhases, badTree,
    switchingDecisionTreeUnder] using
      (deepPath_switchingDecisionTreeUnderAux
        (formula.restrict
          (RandomRestriction.decode bad.1)).vars.card
        formula (RandomRestriction.decode bad.1)).symm

private theorem map_query_badPhaseEntries
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    (badPhaseEntries formula bad).map PhaseEntry.query =
      (badTree formula bad).deepPath := by
  simpa [badPhaseEntries, badTree,
    switchingDecisionTreeUnder] using
    map_query_annotatedSwitchingPhases
      (formula.restrict
        (RandomRestriction.decode bad.1)).vars.card
      formula (RandomRestriction.decode bad.1)

private theorem nodup_badPhaseEntry_vars
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    ((badPhaseEntries formula bad).map fun entry =>
      entry.query.1).Nodup := by
  have hmap := congrArg (List.map Prod.fst)
    (map_query_badPhaseEntries formula bad)
  have heq :
      (badPhaseEntries formula bad).map
          (fun entry => entry.query.1) =
        (badTree formula bad).deepPathVars := by
    simpa [DecisionTree.On.deepPathVars,
      List.map_map, Function.comp_def] using hmap
  rw [heq]
  exact DecisionTree.On.nodup_deepPathVars_internal
    (badTree formula bad)
    (badTree_pathReadOnce formula bad)

private theorem queryCount_le_badPhaseEntries_length
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    queryCount ≤ (badPhaseEntries formula bad).length := by
  have hlength := congrArg List.length
    (map_query_badPhaseEntries formula bad)
  simp only [List.length_map] at hlength
  calc
    queryCount ≤ (badTree formula bad).depth :=
      queryCount_le_badTree formula bad
    _ = (badTree formula bad).deepPath.length :=
      (DecisionTree.On.length_deepPath_internal _).symm
    _ = (badPhaseEntries formula bad).length :=
      hlength.symm

private theorem queryCount_le_badPhases_length
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    queryCount ≤
      ((badPhases formula bad).flatMap Prod.snd).length := by
  rw [flatMap_badPhases_eq_deepPath,
    DecisionTree.On.length_deepPath_internal]
  exact queryCount_le_badTree formula bad

private theorem badFirstPhase_spec
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (hpositive : 0 < queryCount) :
    ∃ original literal tail block phases,
      formula.firstLiveTerm
          (RandomRestriction.decode bad.1) =
          some (original, literal :: tail) ∧
        badPhaseEntries formula bad =
          annotateBlock original block ++
            annotatePhases phases ∧
        block.map Prod.fst =
          (Literal.vars (literal :: tail)).toList ∧
        block ≠ [] := by
  have htreePositive : 0 < (badTree formula bad).depth :=
    hpositive.trans_le (queryCount_le_badTree formula bad)
  have hauxPositive :
      0 < (switchingDecisionTreeUnderAux
        (formula.restrict
          (RandomRestriction.decode bad.1)).vars.card
        formula (RandomRestriction.decode bad.1)).depth := by
    simpa [badTree, switchingDecisionTreeUnder] using
      htreePositive
  obtain ⟨original, literal, tail, block, phases,
      hfirst, hphases, hmap, hblock⟩ :=
    switchingPhasesAux_first_spec
      (formula.restrict
        (RandomRestriction.decode bad.1)).vars.card
      formula (RandomRestriction.decode bad.1)
      hauxPositive
  refine ⟨original, literal, tail, block, phases,
    hfirst, ?_, hmap, hblock⟩
  simp [badPhaseEntries, hphases, annotatePhases]

private theorem badFirstPhase_entry_for_literal
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (original reduced : List (Literal N))
    (block : List (Fin N × Bool))
    (remaining : List (PhaseEntry N))
    (hentries : badPhaseEntries formula bad =
      annotateBlock original block ++ remaining)
    (hmap : block.map Prod.fst =
      (Literal.vars reduced).toList)
    (literal : Literal N) (hliteral : literal ∈ reduced) :
    ∃ entry ∈ badPhaseEntries formula bad,
      entry.original = original ∧
        entry.query.1 = literal.var := by
  have hvar : literal.var ∈ block.map Prod.fst := by
    rw [hmap]
    simpa using
      (Literal.mem_vars_iff reduced literal.var).mpr
        ⟨literal, hliteral, rfl⟩
  rw [List.mem_map] at hvar
  obtain ⟨query, hquery, hqueryVar⟩ := hvar
  have hannotated :
      query ∈ (annotateBlock original block).map
        PhaseEntry.query := by
    rw [map_query_annotateBlock]
    exact hquery
  rw [List.mem_map] at hannotated
  obtain ⟨entry, hentry, hentryQuery⟩ := hannotated
  refine ⟨entry, ?_, ?_, ?_⟩
  · rw [hentries]
    exact List.mem_append_left _ hentry
  · exact original_eq_of_mem_annotateBlock
      original block entry hentry
  · exact (congrArg Prod.fst hentryQuery).trans
      hqueryVar

private theorem badFirstLiveTerm
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (hpositive : 0 < queryCount) :
    ∃ reduced,
      formula.firstLiveTerm
          (RandomRestriction.decode bad.1) =
        some ((badPhaseEntries formula bad)[0]'(by
          exact hpositive.trans_le
            (queryCount_le_badPhaseEntries_length
              formula bad))
          |>.original, reduced) := by
  have htreePositive : 0 < (badTree formula bad).depth :=
    hpositive.trans_le (queryCount_le_badTree formula bad)
  have hauxPositive :
      0 < (switchingDecisionTreeUnderAux
        (formula.restrict
          (RandomRestriction.decode bad.1)).vars.card
        formula (RandomRestriction.decode bad.1)).depth := by
    simpa [badTree, switchingDecisionTreeUnder] using
      htreePositive
  obtain ⟨original, literal, tail, hfirst⟩ :=
    firstLiveTerm_of_switchingDepth_pos
      (formula.restrict
        (RandomRestriction.decode bad.1)).vars.card
      formula (RandomRestriction.decode bad.1)
      hauxPositive
  refine ⟨literal :: tail, ?_⟩
  have horiginal :
      ((badPhaseEntries formula bad)[0]'(by
        exact hpositive.trans_le
          (queryCount_le_badPhaseEntries_length
            formula bad))).original = original := by
    cases hfuel :
        (formula.restrict
          (RandomRestriction.decode bad.1)).vars.card with
    | zero =>
        simp [hfuel, switchingDecisionTreeUnderAux,
          DecisionTree.On.depth] at hauxPositive
    | succ fuel =>
        let term := literal :: tail
        let queries := (Literal.vars term).toList
        let continuation : Restriction.On N →
            DecisionTree.On N := fun branch =>
          let assignment :=
            DecisionTree.On.assignmentFor queries
              (branch.applyTo fun _ => false)
          if term.all (fun found => found.eval
              (assignment.applyTo fun _ => false)) then
            .leaf true
          else
            switchingDecisionTreeUnderAux fuel formula
              (Restriction.On.comp
                (RandomRestriction.decode bad.1)
                assignment)
        let block :=
          DecisionTree.On.deepBlockPath queries continuation
        let branch :=
          DecisionTree.On.deepBranch queries continuation
        have hqueries : queries ≠ [] := by
          have hmem : literal.var ∈ queries := by
            simp [queries, term, Literal.mem_vars_iff]
          exact List.ne_nil_of_mem hmem
        have hblock : block ≠ [] := by
          intro hempty
          have hmap : block.map Prod.fst = queries := by
            simpa [block] using
            DecisionTree.On.map_fst_deepBlockPath_internal
              queries continuation
          rw [hempty] at hmap
          exact hqueries hmap.symm
        have hphases : ∃ phases,
            switchingPhasesAux (fuel + 1) formula
                (RandomRestriction.decode bad.1) =
              (original, block) :: phases := by
          simp only [switchingPhasesAux, hfirst]
          change ∃ phases,
            (if term.all (fun found => found.eval
                ((DecisionTree.On.deepBranch queries
                  continuation).applyTo fun _ => false)) then
              [(original, block)]
            else
              (original, block) ::
                switchingPhasesAux fuel formula
                  (Restriction.On.comp
                    (RandomRestriction.decode bad.1)
                    (DecisionTree.On.deepBranch
                      queries continuation))) =
                (original, block) :: phases
          split
          · exact ⟨[], rfl⟩
          · exact ⟨switchingPhasesAux fuel formula
                (Restriction.On.comp
                  (RandomRestriction.decode bad.1)
                  (DecisionTree.On.deepBranch
                    queries continuation)),
              rfl⟩
        obtain ⟨phases, hphases⟩ := hphases
        simpa only [badPhaseEntries, hfuel, hphases] using
          annotatePhases_cons_getElem_zero_original
            original block phases hblock
  rw [horiginal]
  exact hfirst

private noncomputable def badPhaseEntry
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (position : Fin queryCount) :
    PhaseEntry N :=
  (badPhaseEntries formula bad)[position.val]'(by
    exact position.isLt.trans_le
      (queryCount_le_badPhaseEntries_length formula bad))

private theorem badFirstLiveTerm_entry
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (hpositive : 0 < queryCount) :
    ∃ reduced,
      formula.firstLiveTerm
          (RandomRestriction.decode bad.1) =
        some ((badPhaseEntry formula bad
          ⟨0, hpositive⟩).original, reduced) := by
  simpa [badPhaseEntry] using
    badFirstLiveTerm formula bad hpositive

private theorem badPhaseEntry_query
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (position : Fin queryCount) :
    (badPhaseEntry formula bad position).query =
      ((badTree formula bad).deepPath.get
        (Fin.castLE (by
          simpa [DecisionTree.On.length_deepPath_internal] using
            queryCount_le_badTree formula bad)
          position)) := by
  unfold badPhaseEntry
  have hmap := map_query_badPhaseEntries formula bad
  have hentryPosition :
      position.val < (badPhaseEntries formula bad).length :=
    position.isLt.trans_le
      (queryCount_le_badPhaseEntries_length formula bad)
  have hleft : position.val <
      ((badPhaseEntries formula bad).map
        PhaseEntry.query).length := by
    simpa using hentryPosition
  have hright :
      position.val < (badTree formula bad).deepPath.length := by
    simpa [DecisionTree.On.length_deepPath_internal] using
      position.isLt.trans_le
        (queryCount_le_badTree formula bad)
  have hoption := congrArg
    (fun path => path[position.val]?) hmap
  change ((badPhaseEntries formula bad).map
      PhaseEntry.query)[position.val]? =
    (badTree formula bad).deepPath[position.val]? at hoption
  rw [List.getElem?_eq_getElem hleft,
    List.getElem?_eq_getElem hright] at hoption
  have hget := Option.some.inj hoption
  simpa [List.getElem_map, List.get_eq_getElem,
    Fin.castLE] using hget

private theorem badPhaseEntry_query_fst
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (position : Fin queryCount) :
    (badPhaseEntry formula bad position).query.1 =
      badQueries formula bad position := by
  have hpair := congrArg Prod.fst
    (badPhaseEntry_query formula bad position)
  simpa [badQueries,
    DecisionTree.On.deepPrefixEmbeddingInternal,
    DecisionTree.On.deepPathVars,
    List.get_eq_getElem, List.getElem_map,
    Fin.castLE] using hpair

private theorem badPhaseEntry_original_eq_first_of_literal
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (original reduced : List (Literal N))
    (block : List (Fin N × Bool))
    (remaining : List (PhaseEntry N))
    (hentries : badPhaseEntries formula bad =
      annotateBlock original block ++ remaining)
    (hmap : block.map Prod.fst =
      (Literal.vars reduced).toList)
    (position : Fin queryCount)
    (literal : Literal N) (hliteral : literal ∈ reduced)
    (hquery :
      badQueries formula bad position = literal.var) :
    (badPhaseEntry formula bad position).original =
      original := by
  obtain ⟨entry, hentry, hentryOriginal, hentryQuery⟩ :=
    badFirstPhase_entry_for_literal formula bad
      original reduced block remaining hentries hmap
      literal hliteral
  have hcurrent :
      badPhaseEntry formula bad position ∈
        badPhaseEntries formula bad := by
    unfold badPhaseEntry
    exact List.getElem_mem _
  have hproject :
      (badPhaseEntry formula bad position).query.1 =
        entry.query.1 := by
    rw [badPhaseEntry_query_fst, hquery, hentryQuery]
  have heq :=
    eq_of_mem_of_mem_of_map_nodup
      (badPhaseEntries formula bad)
      (fun found : PhaseEntry N => found.query.1)
      (badPhaseEntry formula bad position) entry
      hcurrent hentry
      (nodup_badPhaseEntry_vars formula bad)
      hproject
  exact (congrArg PhaseEntry.original heq).trans
    hentryOriginal

private theorem badPhaseEntry_query_snd
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (position : Fin queryCount) :
    (badPhaseEntry formula bad position).query.2 =
      badValues formula bad position := by
  have hpair := congrArg Prod.snd
    (badPhaseEntry_query formula bad position)
  simpa [badValues,
    DecisionTree.On.deepPrefixValuesInternal,
    List.get_eq_getElem, Fin.castLE] using hpair

private theorem badPhaseEntry_valid
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (position : Fin queryCount) :
    (badPhaseEntry formula bad position).original ∈
        formula.terms ∧
      (badPhaseEntry formula bad position).query.1 ∈
        Literal.vars
          (badPhaseEntry formula bad position).original := by
  unfold badPhaseEntry badPhaseEntries
  exact phaseEntry_valid _ _ _ _
    (List.getElem_mem _)

private noncomputable def badLiteralPosition
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (position : Fin queryCount) :
    Fin (badPhaseEntry formula bad position).original.length :=
  literalPosition
    (badPhaseEntry formula bad position).original
    (badPhaseEntry formula bad position).query.1
    (badPhaseEntry_valid formula bad position).2

private noncomputable def badGammaValues
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    Fin queryCount → Bool :=
  fun position =>
    ((badPhaseEntry formula bad position).original.get
      (badLiteralPosition formula bad position)).polarity

private noncomputable def badWidthPosition
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (position : Fin queryCount) :
    Fin (formula.width + 1) :=
  Fin.castLE
    (Nat.le_succ_of_le
      (DNF.length_le_width formula
        (badPhaseEntry formula bad position).original
        (badPhaseEntry_valid formula bad position).1))
    (badLiteralPosition formula bad position)

private noncomputable def badWidthCode
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    Switching.WidthPathCode formula.width queryCount :=
  fun position =>
    (badWidthPosition formula bad position,
      badValues formula bad position,
      (badPhaseEntry formula bad position).endPhase ||
        decide (position.val + 1 = queryCount))

private noncomputable def badWidthTranscript
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    List (Fin N × Bool × Bool) :=
  widthTranscript (badPhases formula bad) queryCount

private theorem length_badWidthTranscript
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    (badWidthTranscript formula bad).length = queryCount := by
  exact length_widthTranscript
    (badPhases formula bad) queryCount
    (queryCount_le_badPhases_length formula bad)

private noncomputable def badWidthGammaValues
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    Fin queryCount → Bool :=
  fun position =>
    ((badWidthTranscript formula bad)[position.val]'(by
      rw [length_badWidthTranscript formula bad]
      exact position.isLt)).2.2

private noncomputable def badWidthAdvice
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    List (Fin (formula.width + 1) × Bool × Bool) :=
  widthAdvice formula (badPhases formula bad) queryCount

private theorem length_badWidthAdvice
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    (badWidthAdvice formula bad).length = queryCount := by
  exact length_widthAdvice formula
    (badPhases formula bad) queryCount
    (queryCount_le_badPhases_length formula bad)

private noncomputable def badReplayWidthCode
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    Switching.WidthPathCode formula.width queryCount :=
  fun position =>
    (badWidthAdvice formula bad)[position.val]'(by
      rw [length_badWidthAdvice formula bad]
      exact position.isLt)

private theorem ofFn_badReplayWidthCode
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    List.ofFn (badReplayWidthCode formula bad) =
      badWidthAdvice formula bad := by
  apply List.ext_getElem
  · simp [length_badWidthAdvice]
  · intro index hleft hright
    simp [badReplayWidthCode, List.getElem_ofFn]

private theorem badWidthTranscript_queries
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    (badWidthTranscript formula bad).map
        (fun entry => (entry.1, entry.2.1)) =
      List.ofFn fun position =>
        (badQueries formula bad position,
          badValues formula bad position) := by
  rw [badWidthTranscript, map_query_widthTranscript,
    flatMap_badPhases_eq_deepPath]
  apply List.ext_getElem
  · simp [List.length_take,
      queryCount_le_badTree,
      DecisionTree.On.length_deepPath_internal]
  · intro index hleft hright
    simp [badQueries, badValues,
      DecisionTree.On.deepPrefixEmbeddingInternal,
      DecisionTree.On.deepPrefixValuesInternal,
      DecisionTree.On.deepPathVars,
      List.getElem_ofFn, List.getElem_take,
      List.get_eq_getElem, Fin.castLE]

private theorem badWidthTranscript_eq_ofFn
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    badWidthTranscript formula bad =
      List.ofFn fun position =>
        (badQueries formula bad position,
          badValues formula bad position,
          badWidthGammaValues formula bad position) := by
  apply List.ext_getElem
  · simp [length_badWidthTranscript]
  · intro index hleft hright
    have hindex : index < queryCount := by
      simpa [length_badWidthTranscript] using hleft
    have hpair := congrArg (fun items => items[index]?)
      (badWidthTranscript_queries formula bad)
    simp [hindex, hleft] at hpair
    simp [badWidthGammaValues, List.getElem_ofFn]
    apply Prod.ext
    · exact hpair.1
    · apply Prod.ext
      · exact hpair.2
      · rfl

private theorem badWidthTarget_eq
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    widthTargetRestriction
        (RandomRestriction.decode bad.1)
        (badPhases formula bad) queryCount =
      Restriction.On.comp
        (RandomRestriction.assignmentAlong
          (badQueries formula bad)
          (badWidthGammaValues formula bad))
        (RandomRestriction.decode bad.1) := by
  rw [widthTargetRestriction_eq_transcript formula
    (RandomRestriction.decode bad.1)
    (badPhases formula bad)
    (recoverable_badPhases formula bad) queryCount]
  congr 1
  change DecisionTree.On.assignmentOfPath
    ((badWidthTranscript formula bad).map fun entry =>
      (entry.1, entry.2.2)) = _
  rw [badWidthTranscript_eq_ofFn]
  simp only [List.map_ofFn]
  exact assignmentOfPath_ofFn_embedding
    (badQueries formula bad)
    (badWidthGammaValues formula bad)

private theorem badGammaValues_var
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (position : Fin queryCount) :
    ((badPhaseEntry formula bad position).original.get
        (badLiteralPosition formula bad position)).var =
      badQueries formula bad position := by
  exact (literalPosition_var
    (badPhaseEntry formula bad position).original
    (badPhaseEntry formula bad position).query.1
    (badPhaseEntry_valid formula bad position).2).trans
      (badPhaseEntry_query_fst formula bad position)

private theorem badGammaAssignment_survives_first
    (formula : DNF N) (hconsistent : formula.Consistent)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (hpositive : 0 < queryCount) :
    ∃ original reduced final,
      formula.firstLiveTerm
          (RandomRestriction.decode bad.1) =
          some (original, reduced) ∧
        restrictTerm
            (RandomRestriction.assignmentAlong
              (badQueries formula bad)
              (badGammaValues formula bad))
            reduced =
          some final := by
  obtain ⟨original, literal, tail, block, phases,
      hfirst, hentries, hmap, hblock⟩ :=
    badFirstPhase_spec formula bad hpositive
  let reduced := literal :: tail
  let gamma :=
    RandomRestriction.assignmentAlong
      (badQueries formula bad)
      (badGammaValues formula bad)
  obtain ⟨before, after, hterms, hrestrict, hbefore⟩ :=
    firstLiveTerm_spec_internal formula
      (RandomRestriction.decode bad.1)
      original (literal :: tail) hfirst
  have hsatisfies : ∀ found ∈ reduced,
      gamma found.var = none ∨
        gamma found.var = some found.polarity := by
    intro found hfound
    cases hposition :
        RandomRestriction.positionOf
          (badQueries formula bad) found.var with
    | none =>
        left
        simp [gamma, RandomRestriction.assignmentAlong,
          hposition]
    | some position =>
        right
        have hquery :
            badQueries formula bad position =
              found.var :=
          RandomRestriction.positionOf_eq_some_internal
            (badQueries formula bad) found.var
              position hposition
        have horiginal :=
          badPhaseEntry_original_eq_first_of_literal
            formula bad original reduced block
            (annotatePhases phases) hentries hmap
            position found hfound hquery
        have horiginalMem :
            original ∈ formula.terms := by
          rw [← horiginal]
          exact
            (badPhaseEntry_valid formula bad position).1
        let selected :=
          (badPhaseEntry formula bad position).original.get
            (badLiteralPosition formula bad position)
        have hselectedMem :
            selected ∈
              (badPhaseEntry formula bad position).original := by
          exact List.get_mem _ _
        have hselectedVar :
            selected.var = found.var := by
          exact (badGammaValues_var formula bad position).trans
            hquery
        have hpolarity :
            selected.polarity = found.polarity := by
          have hfoundOriginal : found ∈ original := by
            exact (mem_of_mem_restrictTerm
              (RandomRestriction.decode bad.1)
              hrestrict (by simpa [reduced] using hfound)).1
          apply hconsistent original horiginalMem
          · rw [← horiginal]
            exact hselectedMem
          · exact hfoundOriginal
          · exact hselectedVar
        dsimp only [gamma]
        rw [← hquery]
        rw [RandomRestriction.assignmentAlong_apply_internal]
        simpa [badGammaValues, selected] using hpolarity
  refine ⟨original, reduced,
    reduced.filter fun found => gamma found.var = none,
    ?_, ?_⟩
  · simpa [reduced] using hfirst
  · exact (restrictTerm_eq_some_filter_iff
      gamma reduced).mpr hsatisfies

private theorem badQueries_free
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (position : Fin queryCount) :
    bad.1 (badQueries formula bad position) = .inl () := by
  have hinTree :
      badQueries formula bad position ∈
        (badTree formula bad).vars := by
    exact DecisionTree.On.deepPrefixEmbedding_mem_vars_internal
      (badTree formula bad) queryCount
      (queryCount_le_badTree formula bad)
      (badTree_pathReadOnce formula bad) position
  have hinRestricted :
      badQueries formula bad position ∈
        (formula.restrict
          (RandomRestriction.decode bad.1)).vars := by
    apply vars_switchingDecisionTree_subset_internal _
    simpa [badTree,
      switchingDecisionTreeUnder_eq_internal] using hinTree
  have hsurvives := DNF.vars_restrict_subset_filter
    (RandomRestriction.decode bad.1) formula hinRestricted
  have hnone :
      RandomRestriction.decode bad.1
          (badQueries formula bad position) =
        none :=
    (Finset.mem_filter.mp hsurvives).2
  apply (RandomRestriction.decodeSymbol_eq_none_iff_internal _).mp
  simpa [RandomRestriction.decode] using hnone

private noncomputable def badTargetRestriction
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount)) :
    Restriction.On N :=
  Restriction.On.comp
    (RandomRestriction.assignmentAlong
      (badQueries formula bad)
      (badGammaValues formula bad))
    (RandomRestriction.decode bad.1)

private theorem decode_switchingBadWidthSeed
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (copies : Fin queryCount → Fin q) :
    RandomRestriction.decode
        (RandomRestriction.fixAlong bad.1
          (badQueries formula bad) copies
          (badGammaValues formula bad)) =
      badTargetRestriction formula bad := by
  exact RandomRestriction.decode_fixAlong_internal
    bad.1 (badQueries formula bad) copies
      (badGammaValues formula bad)

private theorem badTargetRestriction_firstLiveTerm
    (formula : DNF N) (hconsistent : formula.Consistent)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (hpositive : 0 < queryCount) :
    ∃ final,
      formula.firstLiveTerm
          (badTargetRestriction formula bad) =
        some ((badPhaseEntry formula bad
          ⟨0, hpositive⟩).original, final) := by
  obtain ⟨original, reduced, final, hfirst, hsecond⟩ :=
    badGammaAssignment_survives_first
      formula hconsistent bad hpositive
  obtain ⟨entryReduced, hentryFirst⟩ :=
    badFirstLiveTerm_entry formula bad hpositive
  have horiginal :
      original =
        (badPhaseEntry formula bad
          ⟨0, hpositive⟩).original := by
    have hpairs :=
      Option.some.inj (hfirst.symm.trans hentryFirst)
    exact congrArg Prod.fst hpairs
  let gamma :=
    RandomRestriction.assignmentAlong
      (badQueries formula bad)
      (badGammaValues formula bad)
  let base := RandomRestriction.decode bad.1
  have hfree : ∀ position,
      base (badQueries formula bad position) = none := by
    intro position
    simp [base, RandomRestriction.decode,
      badQueries_free formula bad position,
      RandomRestriction.decodeSymbol]
  have hcomm :
      Restriction.On.comp gamma base =
        Restriction.On.comp base gamma :=
    Restriction.On.comp_comm_of_disjoint gamma base
      (RandomRestriction.assignmentAlong_disjoint_internal
        bad.1 (badQueries formula bad)
          (badGammaValues formula bad) hfree)
  refine ⟨final, ?_⟩
  rw [badTargetRestriction, hcomm]
  rw [← horiginal]
  exact firstLiveTerm_comp_internal
    formula base gamma original reduced final
      hfirst hsecond

private theorem decodeWidthEntry_badWidthCode
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (position : Fin queryCount) :
    decodeWidthEntry
        (badPhaseEntry formula bad position).original
        (badWidthCode formula bad position) =
      some (badQueries formula bad position,
        badValues formula bad position,
        badGammaValues formula bad position) := by
  simp [decodeWidthEntry, badWidthCode, badWidthPosition,
    badQueries, badValues, badGammaValues]
  exact badGammaValues_var formula bad position

private theorem decode_switchingBadReplaySeed
    (formula : DNF N)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (copies : Fin queryCount → Fin q) :
    RandomRestriction.decode
        (RandomRestriction.fixAlong bad.1
          (badQueries formula bad) copies
          (badWidthGammaValues formula bad)) =
      widthTargetRestriction
        (RandomRestriction.decode bad.1)
        (badPhases formula bad) queryCount := by
  rw [RandomRestriction.decode_fixAlong_internal]
  exact (badWidthTarget_eq formula bad).symm

private theorem decode_switchingBadReplay
    (formula : DNF N) (hconsistent : formula.Consistent)
    (bad :
      RandomRestriction.EventSeed N q
        (switchingBad formula queryCount))
    (copies : Fin queryCount → Fin q) :
    decodeWidthPathAux formula
        (RandomRestriction.decode
          (RandomRestriction.fixAlong bad.1
            (badQueries formula bad) copies
            (badWidthGammaValues formula bad)))
        none
        (List.ofFn (badReplayWidthCode formula bad)) =
      List.ofFn fun position =>
        (badQueries formula bad position,
          badValues formula bad position,
          badWidthGammaValues formula bad position) := by
  rw [decode_switchingBadReplaySeed,
    ofFn_badReplayWidthCode]
  change decodeWidthPathAux formula
      (widthTargetRestriction
        (RandomRestriction.decode bad.1)
        (badPhases formula bad) queryCount) none
      (widthAdvice formula (badPhases formula bad) queryCount) = _
  simpa [badWidthTranscript] using
    (decodeWidthPathAux_widthTarget formula hconsistent
      (RandomRestriction.decode bad.1)
      (badPhases formula bad)
      (recoverable_badPhases formula bad) queryCount
      (queryCount_le_badPhases_length formula bad)).trans
        (badWidthTranscript_eq_ofFn formula bad)

private noncomputable def switchingBadWidthEncoding
    (formula : DNF N) :
    RandomRestriction.EventSeed N q
          (switchingBad formula queryCount) ×
        (Fin queryCount → Fin q) →
      RandomRestriction.Seed N q ×
        Switching.WidthPathCode formula.width queryCount :=
  fun pair =>
    (RandomRestriction.fixAlong pair.1.1
      (badQueries formula pair.1) pair.2
      (badWidthGammaValues formula pair.1),
    badReplayWidthCode formula pair.1)

private noncomputable def switchingBadEncoding
    (formula : DNF N) :
    RandomRestriction.EventSeed N q
          (switchingBad formula queryCount) ×
        (Fin queryCount → Fin q) →
      RandomRestriction.Seed N q ×
        Switching.PathCode N queryCount :=
  fun pair =>
    (RandomRestriction.fixAlong pair.1.1
      (badQueries formula pair.1) pair.2
      (badValues formula pair.1),
    (badQueries formula pair.1, badValues formula pair.1))

private theorem switchingBadWidthEncoding_injective
    (formula : DNF N) (hconsistent : formula.Consistent) :
    Function.Injective
      (switchingBadWidthEncoding (q := q)
        (queryCount := queryCount) formula) := by
  intro left right hequal
  rcases left with ⟨leftBad, leftCopies⟩
  rcases right with ⟨rightBad, rightCopies⟩
  change
    (RandomRestriction.fixAlong leftBad.1
        (badQueries formula leftBad) leftCopies
        (badWidthGammaValues formula leftBad),
      badReplayWidthCode formula leftBad) =
    (RandomRestriction.fixAlong rightBad.1
        (badQueries formula rightBad) rightCopies
        (badWidthGammaValues formula rightBad),
      badReplayWidthCode formula rightBad) at hequal
  have hfixed :
      RandomRestriction.fixAlong leftBad.1
          (badQueries formula leftBad) leftCopies
          (badWidthGammaValues formula leftBad) =
        RandomRestriction.fixAlong rightBad.1
          (badQueries formula rightBad) rightCopies
          (badWidthGammaValues formula rightBad) :=
    congrArg Prod.fst hequal
  have hcode :
      badReplayWidthCode formula leftBad =
        badReplayWidthCode formula rightBad :=
    congrArg Prod.snd hequal
  have hdecoded :
      decodeWidthPathAux formula
          (RandomRestriction.decode
            (RandomRestriction.fixAlong leftBad.1
              (badQueries formula leftBad) leftCopies
              (badWidthGammaValues formula leftBad)))
          none
          (List.ofFn (badReplayWidthCode formula leftBad)) =
        decodeWidthPathAux formula
          (RandomRestriction.decode
            (RandomRestriction.fixAlong rightBad.1
              (badQueries formula rightBad) rightCopies
              (badWidthGammaValues formula rightBad)))
          none
          (List.ofFn
            (badReplayWidthCode formula rightBad)) := by
    rw [hfixed, hcode]
  rw [decode_switchingBadReplay formula hconsistent
      leftBad leftCopies,
    decode_switchingBadReplay formula hconsistent
      rightBad rightCopies] at hdecoded
  have htriples :
      (fun position =>
        (badQueries formula leftBad position,
          badValues formula leftBad position,
          badWidthGammaValues formula leftBad position)) =
      fun position =>
        (badQueries formula rightBad position,
          badValues formula rightBad position,
          badWidthGammaValues formula rightBad position) :=
    List.ofFn_inj.mp hdecoded
  have hqueriesFun :
      (badQueries formula leftBad : Fin queryCount → Fin N) =
        (badQueries formula rightBad : Fin queryCount → Fin N) := by
    funext position
    exact congrArg Prod.fst (congrFun htriples position)
  have hqueries :
      badQueries formula leftBad =
        badQueries formula rightBad := by
    apply Function.Embedding.ext
    intro position
    exact congrFun hqueriesFun position
  have hgamma :
      badWidthGammaValues formula leftBad =
        badWidthGammaValues formula rightBad := by
    funext position
    exact congrArg (fun entry => entry.2.2)
      (congrFun htriples position)
  rw [← hqueries, ← hgamma] at hfixed
  have rightFree : ∀ position,
      rightBad.1 (badQueries formula leftBad position) =
        .inl () := by
    intro position
    rw [hqueries]
    exact badQueries_free formula rightBad position
  let leftSeed :
      {seed : RandomRestriction.Seed N q //
        ∀ position,
          seed (badQueries formula leftBad position) = .inl ()} :=
    ⟨leftBad.1, badQueries_free formula leftBad⟩
  let rightSeed :
      {seed : RandomRestriction.Seed N q //
        ∀ position,
          seed (badQueries formula leftBad position) = .inl ()} :=
    ⟨rightBad.1, rightFree⟩
  have hpairs :
      (leftSeed, leftCopies) =
        (rightSeed, rightCopies) := by
    apply
      RandomRestriction.fixAlong_seed_copies_injective_internal
        (badQueries formula leftBad)
        (badWidthGammaValues formula leftBad)
    exact hfixed
  have hseed : leftBad.1 = rightBad.1 := by
    have hrecovered := congrArg
      (fun pair =>
        (pair.1 : RandomRestriction.Seed N q)) hpairs
    simpa [leftSeed, rightSeed] using hrecovered
  have hbad : leftBad = rightBad := Subtype.ext hseed
  have hcopies : leftCopies = rightCopies :=
    congrArg Prod.snd hpairs
  exact Prod.ext hbad hcopies

private theorem switchingBadEncoding_injective
    (formula : DNF N) :
    Function.Injective
      (switchingBadEncoding (q := q)
        (queryCount := queryCount) formula) := by
  intro left right hequal
  rcases left with ⟨leftBad, leftCopies⟩
  rcases right with ⟨rightBad, rightCopies⟩
  change
    (RandomRestriction.fixAlong leftBad.1
        (badQueries formula leftBad) leftCopies
        (badValues formula leftBad),
      ((badQueries formula leftBad : Fin queryCount → Fin N),
        badValues formula leftBad)) =
    (RandomRestriction.fixAlong rightBad.1
        (badQueries formula rightBad) rightCopies
        (badValues formula rightBad),
      ((badQueries formula rightBad : Fin queryCount → Fin N),
        badValues formula rightBad)) at hequal
  have hfixed : RandomRestriction.fixAlong leftBad.1
      (badQueries formula leftBad) leftCopies
      (badValues formula leftBad) =
    RandomRestriction.fixAlong rightBad.1
      (badQueries formula rightBad) rightCopies
      (badValues formula rightBad) :=
    congrArg Prod.fst hequal
  have hqueriesFun :
      (badQueries formula leftBad : Fin queryCount → Fin N) =
        (badQueries formula rightBad : Fin queryCount → Fin N) :=
    congrArg (fun output => output.2.1) hequal
  have hqueries :
      badQueries formula leftBad =
        badQueries formula rightBad := by
    apply Function.Embedding.ext
    intro position
    exact congrFun hqueriesFun position
  have hvalues :
      badValues formula leftBad =
        badValues formula rightBad :=
    congrArg (fun output => output.2.2) hequal
  rw [← hqueries, ← hvalues] at hfixed
  have rightFree : ∀ position,
      rightBad.1 (badQueries formula leftBad position) =
        .inl () := by
    intro position
    rw [hqueries]
    exact badQueries_free formula rightBad position
  let leftSeed :
      {seed : RandomRestriction.Seed N q //
        ∀ position,
          seed (badQueries formula leftBad position) = .inl ()} :=
    ⟨leftBad.1, badQueries_free formula leftBad⟩
  let rightSeed :
      {seed : RandomRestriction.Seed N q //
        ∀ position,
          seed (badQueries formula leftBad position) = .inl ()} :=
    ⟨rightBad.1, rightFree⟩
  have hpairs :
      (leftSeed, leftCopies) =
        (rightSeed, rightCopies) := by
    apply
      RandomRestriction.fixAlong_seed_copies_injective_internal
        (badQueries formula leftBad)
        (badValues formula leftBad)
    exact hfixed
  have hseed : leftBad.1 = rightBad.1 := by
    have hrecovered := congrArg
      (fun pair =>
        (pair.1 : RandomRestriction.Seed N q)) hpairs
    simpa [leftSeed, rightSeed] using hrecovered
  have hbad : leftBad = rightBad := Subtype.ext hseed
  have hcopies : leftCopies = rightCopies :=
    congrArg Prod.snd hpairs
  exact Prod.ext hbad hcopies

theorem switchingBad_width_encoding_bound_internal
    (formula : DNF N) (hconsistent : formula.Consistent)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingBad formula queryCount) *
        q ^ queryCount ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) ^ queryCount := by
  have hbound :=
    RandomRestriction.eventCount_mul_pow_le_of_encoding_internal
      (q := q) (switchingBad formula queryCount) queryCount
      (Switching.WidthPathCode formula.width queryCount)
      (switchingBadWidthEncoding (q := q) formula)
      (switchingBadWidthEncoding_injective
        (q := q) formula hconsistent)
  simpa only [Switching.card_widthPathCode_internal] using hbound

theorem switchingBad_consistentPart_width_encoding_bound_internal
    (formula : DNF N) (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingBad formula.consistentPart queryCount) *
        q ^ queryCount ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) ^ queryCount := by
  calc
    RandomRestriction.eventCount (q := q)
          (switchingBad formula.consistentPart queryCount) *
        q ^ queryCount ≤
      (2 * q + 1) ^ N *
        (4 * (formula.consistentPart.width + 1)) ^ queryCount :=
      switchingBad_width_encoding_bound_internal
        formula.consistentPart
        (consistent_consistentPart_internal formula)
        q queryCount
    _ ≤ (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) ^ queryCount := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      exact Nat.mul_le_mul_left 4
        (Nat.add_le_add_right
          (width_consistentPart_le_internal formula) 1)

theorem switchingBad_arity_encoding_bound_internal
    (formula : DNF N) (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingBad formula queryCount) *
        q ^ queryCount ≤
      (2 * q + 1) ^ N * (2 * N) ^ queryCount := by
  have hbound :=
    RandomRestriction.eventCount_mul_pow_le_of_encoding_internal
      (q := q) (switchingBad formula queryCount) queryCount
      (Switching.PathCode N queryCount)
      (switchingBadEncoding (q := q) formula)
      (switchingBadEncoding_injective (q := q) formula)
  simpa only [Switching.card_pathCode_internal] using hbound

end DNF

namespace CNF

theorem consistent_consistentPart_internal
    (formula : CNF N) :
    formula.consistentPart.Consistent := by
  change ((formula.neg.consistentPart.neg).neg).Consistent
  simpa using DNF.consistent_consistentPart_internal formula.neg

theorem eval_consistentPart_internal
    (formula : CNF N) (input : BitString N) :
    formula.consistentPart.eval input =
      formula.eval input := by
  rw [consistentPart, DNF.eval_neg,
    DNF.eval_consistentPart_internal, CNF.eval_neg]
  simp

theorem width_consistentPart_le_internal
    (formula : CNF N) :
    formula.consistentPart.width ≤ formula.width := by
  rw [consistentPart, DNF.width_neg]
  exact
    (DNF.width_consistentPart_le_internal formula.neg).trans_eq
      (CNF.width_neg formula)

theorem switchingDecisionTreeUnder_eq_internal
    (formula : CNF N) (restriction : Restriction.On N) :
    formula.switchingDecisionTreeUnder restriction =
      (formula.restrict restriction).switchingDecisionTree := by
  rw [switchingDecisionTreeUnder,
    DNF.switchingDecisionTreeUnder_eq_internal,
    switchingDecisionTree, CNF.neg_restrict]

theorem switchingBad_eq_neg_internal
    (formula : CNF N) (queryCount : ℕ)
    (restriction : Restriction.On N) :
    switchingBad formula queryCount restriction ↔
      DNF.switchingBad formula.neg queryCount restriction := by
  simp only [switchingBad, switchingDecisionTreeUnder,
    DNF.switchingBad, DecisionTree.On.depth_neg]

theorem switchingBad_width_encoding_bound_internal
    (formula : CNF N) (hconsistent : formula.Consistent)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingBad formula queryCount) *
        q ^ queryCount ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) ^ queryCount := by
  simpa [RandomRestriction.eventCount, switchingBad,
      switchingDecisionTreeUnder, DNF.switchingBad,
      DecisionTree.On.depth_neg, CNF.width_neg] using
    DNF.switchingBad_width_encoding_bound_internal
      formula.neg hconsistent q queryCount

theorem switchingBad_consistentPart_width_encoding_bound_internal
    (formula : CNF N) (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingBad formula.consistentPart queryCount) *
        q ^ queryCount ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) ^ queryCount := by
  have hbound :=
    switchingBad_width_encoding_bound_internal
      formula.consistentPart
      (consistent_consistentPart_internal formula)
      q queryCount
  exact hbound.trans
    (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left
        (Nat.mul_le_mul_left 4
          (Nat.add_le_add_right
            (width_consistentPart_le_internal formula) 1))
        _))

theorem eval_canonicalDecisionTree_internal
    (formula : CNF N) (input : BitString N) :
    formula.canonicalDecisionTree.eval input =
      formula.eval input := by
  rw [canonicalDecisionTree, DecisionTree.On.eval_neg,
    DNF.eval_canonicalDecisionTree_internal, CNF.eval_neg]
  simp

theorem depth_canonicalDecisionTree_le_vars_internal
    (formula : CNF N) :
    formula.canonicalDecisionTree.depth ≤
      formula.vars.card := by
  rw [canonicalDecisionTree, DecisionTree.On.depth_neg,
    ← CNF.vars_neg]
  exact DNF.depth_canonicalDecisionTree_le_vars_internal
    formula.neg

theorem depth_canonicalDecisionTree_le_arity_internal
    (formula : CNF N) :
    formula.canonicalDecisionTree.depth ≤ N := by
  exact (depth_canonicalDecisionTree_le_vars_internal formula).trans
    ((Finset.card_le_univ formula.vars).trans_eq
      (Fintype.card_fin N))

theorem eval_switchingDecisionTree_internal
    (formula : CNF N) (input : BitString N) :
    formula.switchingDecisionTree.eval input =
      formula.eval input := by
  rw [switchingDecisionTree, DecisionTree.On.eval_neg,
    DNF.eval_switchingDecisionTree_internal, CNF.eval_neg]
  simp

theorem vars_switchingDecisionTree_subset_internal
    (formula : CNF N) :
    formula.switchingDecisionTree.vars ⊆ formula.vars := by
  rw [switchingDecisionTree, DecisionTree.On.vars_neg,
    ← CNF.vars_neg]
  exact DNF.vars_switchingDecisionTree_subset_internal
    formula.neg

theorem pathReadOnce_switchingDecisionTree_internal
    (formula : CNF N) :
    formula.switchingDecisionTree.PathReadOnce := by
  rw [switchingDecisionTree,
    DecisionTree.On.pathReadOnce_neg_internal]
  exact DNF.pathReadOnce_switchingDecisionTree_internal
    formula.neg

theorem depth_switchingDecisionTree_le_vars_internal
    (formula : CNF N) :
    formula.switchingDecisionTree.depth ≤
      formula.vars.card := by
  rw [switchingDecisionTree, DecisionTree.On.depth_neg,
    ← CNF.vars_neg]
  exact DNF.depth_switchingDecisionTree_le_vars_internal
    formula.neg

theorem depth_switchingDecisionTree_le_arity_internal
    (formula : CNF N) :
    formula.switchingDecisionTree.depth ≤ N := by
  exact (depth_switchingDecisionTree_le_vars_internal formula).trans
    ((Finset.card_le_univ formula.vars).trans_eq
      (Fintype.card_fin N))

end CNF
end Complexity
