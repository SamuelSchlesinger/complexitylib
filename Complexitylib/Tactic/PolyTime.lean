/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P
public import Complexitylib.Tactic.PolyTime.Init

/-!
# Synthesizing polynomial-time proofs

`polytime` proves `f ∈ FP`, `UnaryFn f`, and `FPPred p` by composing existing
machine-based closure theorems. It handles pairing, reversal, concatenation,
slicing, bit access, unary arithmetic, comparisons, conditionals, and encoded
bounded ranges. Local certificates support calls to supplied algorithms.
Use `polytime [program]` to unfold a named program before proof search.
Register reusable closure rules and algorithm certificates with `@[polytime]`.
Number-valued certificates should use `UnaryFn`; local certificates written as
membership of a unary encoding in `FP` are normalized automatically.

Iteration requires a certified step, an efficient unary count, and a constant
bound on the number of bits added per step. More general loops can use
`iterate_mem_FP` explicitly, with `polytime` discharging its efficiency premises
and the caller proving the state-size invariant.

This adapts Samuel Schlesinger's Aesop rule-set and local-certificate approach
from the CSLib crypto branch to Complexitylib's own `FP` predicates:
https://github.com/SamuelSchlesinger/cslib/blob/b9f4e0dd39cd88231322b4225b2bf7ba6bc7e8a3/Cslib/Tactic/PolyTime.lean

The rules construct ordinary Lean proofs. Unknown algorithms need certificates;
neither arbitrary Lean computation nor unrestricted iteration gets unit cost.
The underlying Aesop rule set is `ComplexityPolyTime`.
-/

public section

namespace Complexity.Tactic.PolyTime

/-- The identity in the lambda form used by closure rules. -/
theorem id_rule : (fun x : List Bool => x) ∈ FP := id_mem_FP

/-- Normalize unary certificates before matching local hypotheses. -/
theorem unary_rule {f : List Bool → ℕ} :
    (fun x => List.replicate (f x) true) ∈ FP ↔ UnaryFn f := Iff.rfl

/-- Reversal after a certified computation. -/
theorem reverse_rule {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun x => (f x).reverse) ∈ FP := mem_FP_comp hf reverse_mem_FP

/-- Dropping the first bit after a certified computation. -/
theorem tail_rule {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun x => (f x).tail) ∈ FP := by
  simpa using drop_mem_FP hf (UnaryFn.const 1)

/-- First projection after a certified computation. -/
theorem fst_rule {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun x => pairFst (f x)) ∈ FP := mem_FP_comp hf pairFst_mem_FP

/-- Second projection after a certified computation. -/
theorem snd_rule {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun x => pairSnd (f x)) ∈ FP := mem_FP_comp hf pairSnd_mem_FP

/-- Prepending a fixed bit after a certified computation. -/
theorem cons_rule (bit : Bool) {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun x => bit :: f x) ∈ FP := mem_FP_comp hf (Cobham.cons_mem_FP bit)

/-- The flag comparing the lengths of two certified words. -/
theorem lenEqFlag_rule {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun x => Cobham.lenEqFlag (f x) (g x)) ∈ FP :=
  andBitFn_mem_FP (lenLeFlagFn_mem_FP hf hg) (lenLeFlagFn_mem_FP hg hf)

/-- Fix the called algorithm before searching for its argument's certificate. -/
theorem comp_rule {g : List Bool → List Bool} (hg : g ∈ FP)
    {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun x => g (f x)) ∈ FP := mem_FP_comp hf hg

/-- Specialize a certified number-valued function before choosing its argument. -/
theorem unary_comp_rule {g : List Bool → ℕ} (hg : UnaryFn g)
    {f : List Bool → List Bool} (hf : f ∈ FP) :
    UnaryFn (fun x => g (f x)) := hg.comp hf

/-- Specialize a certified predicate before choosing its argument. -/
theorem pred_comp_rule {p : List Bool → Prop} (hp : FPPred p)
    {f : List Bool → List Bool} (hf : f ∈ FP) :
    FPPred (fun x => p (f x)) := hp.comp hf

/-- A unary loop count and constant step growth suffice for polynomial iteration. -/
theorem iterate_rule {f init : List Bool → List Bool} {count : List Bool → ℕ}
    (hf : f ∈ FP) (hi : init ∈ FP) (hc : UnaryFn count) {growth : ℕ}
    (hgrowth : ∀ w, (f w).length ≤ w.length + growth) :
    (fun z => f^[count z] (init z)) ∈ FP := by
  simpa only [List.length_replicate] using
    iterate_mem_FP_of_step_le hf hi hc.mem_FP growth
      (fun z n _ => by
        simpa only [Function.iterate_succ_apply'] using hgrowth (f^[n] (init z)))

-- Unrestricted composition leaves the called function undetermined. Specialize
-- it to a local certificate first, then search only for its argument.
open Lean Meta Elab Tactic in
@[aesop unsafe 50% tactic (rule_sets := [ComplexityPolyTime])]
private meta def polytimeCall : TacticM Unit := withMainContext <| withTransparency .reducible do
  let goal ← getMainGoal
  let target ← goal.getType
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type := decl.type.consumeMData
    let rule ← if type.isAppOf ``UnaryFn then pure ``unary_comp_rule
      else if type.isAppOf ``FPPred then pure ``pred_comp_rule
      else if type.isAppOf ``Membership.mem && type.getAppArgs[3]!.isConstOf ``FP then
        pure ``comp_rule
      else continue
    let saved ← saveState
    try
      let goals ← goal.apply (← mkAppM rule #[decl.toExpr])
      if ← goals.anyM (fun subgoal => do isDefEq (← subgoal.getType) target) then
        throwError "composition made no progress"
      replaceMainGoal goals
      return
    catch _ => saved.restore
  throwError "no applicable local polynomial-time certificate"

-- A named program can reuse a registered certificate on a computed argument.
-- Inspect the actual call so composition never guesses an arbitrary algorithm.
open Lean Meta Elab Tactic in
@[aesop unsafe 60% tactic (rule_sets := [ComplexityPolyTime])]
private meta def polytimeApply : TacticM Unit := withMainContext <| withTransparency .reducible do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let rule ← if target.isAppOf ``UnaryFn then pure ``unary_comp_rule
    else if target.isAppOf ``FPPred then pure ``pred_comp_rule
    else if target.isAppOf ``Membership.mem && target.getAppArgs[3]!.isConstOf ``FP then
      pure ``comp_rule
    else throwError "expected a polynomial-time goal"
  let outer ← lambdaTelescope target.getAppArgs.back! fun inputs body => do
    unless inputs.size == 1 && body.isApp do throwError "expected a function call"
    let input := inputs[0]!
    let argument := body.appArg!
    let outer := body.appFn!
    if outer.containsFVar input.fvarId! then throwError "the function captures the input"
    unless ← isDefEq (← inferType argument) (← inferType input) do
      throwError "expected a word argument"
    if ← isDefEq argument input then throwError "composition made no progress"
    return outer
  replaceMainGoal (← (← getMainGoal).apply (← mkAppOptM rule #[some outer]))

-- Unindexed rules also recognize eta-reduced goals such as `UnaryFn List.length`.
attribute [aesop norm simp (rule_sets := [ComplexityPolyTime])]
  unary_rule Function.comp_def id

attribute [aesop safe apply (transparency := reducible)
    (index := [unindexed]) (rule_sets := [ComplexityPolyTime])]
  id_rule constFn_mem_FP UnaryFn.const FPPred.const
  UnaryFn.length reverse_rule tail_rule fst_rule snd_rule
  Cobham.cons_mem_FP mem_FP_pair

attribute [aesop safe apply (transparency := reducible) (rule_sets := [ComplexityPolyTime])]
  Cobham.appendFn_mem_FP
  cons_rule lenEqFlag_rule polyRulerFn_mem_FP emptyFlagFn_mem_FP dropOneFn_mem_FP
  UnaryFn.replicate_mem_FP UnaryFn.add UnaryFn.mul UnaryFn.pow_const
  UnaryFn.sub UnaryFn.min UnaryFn.max UnaryFn.div UnaryFn.mod UnaryFn.size
  UnaryFn.log UnaryFn.clog UnaryFn.pow_clog
  FPPred.le FPPred.lt FPPred.eq FPPred.and FPPred.or FPPred.not
  take_mem_FP drop_mem_FP getBit_mem_FP FPPred.getBit
  UnaryFn.ite FPPred.ite_mem_FP FPPred.flag_mem_FP
  bits_mem_FP toBitsLE_mem_FP natEncode_mem_FP encodeList_mem_FP
  orBitFn_mem_FP andBitFn_mem_FP notBitFn_mem_FP
  lenLeFlagFn_mem_FP eqFlagFn_mem_FP blockAtFn_mem_FP padToFn_mem_FP
  Cobham.selectHeadFn_mem_FP Cobham.emptyFlag_mem_FP Cobham.mulLenFn_mem_FP
  catRange_mem_FP listEncFn_mem_FP countOver_mem_FP findFirst_mem_FP maxFn_mem_FP

attribute [aesop unsafe 50% apply (transparency := reducible) (rule_sets := [ComplexityPolyTime])]
  iterate_rule UnaryFn.sum UnaryFn.count UnaryFn.bmax
  FPPred.forall_lt FPPred.exists_lt

-- A straight-line program can have many nested calls while every rule makes structural progress.
/-- Prove polynomial-time membership from registered closure rules and local certificates. -/
macro "polytime" : tactic => `(tactic|
  solve
  | aesop (rule_sets := [ComplexityPolyTime, -default, -SetLike, -finsetNonempty])
      (erase Aesop.BuiltinRules.rfl)
      (config := {
        maxRuleApplications := 1000
        maxRuleApplicationDepth := 100
        assumptionTransparency := .reducible
        applyHypsTransparency := .reducible }))

/-- Unfold the listed program definitions before synthesizing an efficiency proof. -/
@[tactic_alt tacticPolytime]
macro "polytime" "[" names:ident,* "]" : tactic =>
  `(tactic| (unfold $names*; polytime))

end Complexity.Tactic.PolyTime
