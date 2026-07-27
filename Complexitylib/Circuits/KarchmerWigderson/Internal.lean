/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KarchmerWigderson.Defs

/-!
# Karchmer--Wigderson protocols -- proof internals
-/

@[expose] public section

namespace Complexity
namespace KarchmerWigderson
namespace Protocol

theorem eval_toFormula_eq_false_internal
    {zeroInputs oneInputs : Set (BitString N)}
    (protocol : Protocol N zeroInputs oneInputs)
    {input : BitString N} (hinput : input ∈ zeroInputs) :
    protocol.toFormula.eval input = false := by
  induction protocol with
  | leaf index zeroAt oneAt =>
      exact zeroAt input hinput
  | alice choice ifFalse ifTrue ihFalse ihTrue =>
      rw [toFormula, MonotoneFormula.eval,
        Bool.or_eq_false_iff]
      exact ⟨ihFalse hinput, ihTrue hinput⟩
  | bob choice ifFalse ifTrue ihFalse ihTrue =>
      rw [toFormula, MonotoneFormula.eval,
        Bool.and_eq_false_iff]
      cases hchoice : choice input
      · exact Or.inl (ihFalse ⟨hinput, hchoice⟩)
      · exact Or.inr (ihTrue ⟨hinput, hchoice⟩)

theorem eval_toFormula_eq_true_internal
    {zeroInputs oneInputs : Set (BitString N)}
    (protocol : Protocol N zeroInputs oneInputs)
    {input : BitString N} (hinput : input ∈ oneInputs) :
    protocol.toFormula.eval input = true := by
  induction protocol with
  | leaf index zeroAt oneAt =>
      exact oneAt input hinput
  | alice choice ifFalse ifTrue ihFalse ihTrue =>
      rw [toFormula, MonotoneFormula.eval, Bool.or_eq_true]
      cases hchoice : choice input
      · exact Or.inl (ihFalse ⟨hinput, hchoice⟩)
      · exact Or.inr (ihTrue ⟨hinput, hchoice⟩)
  | bob choice ifFalse ifTrue ihFalse ihTrue =>
      rw [toFormula, MonotoneFormula.eval,
        Bool.and_eq_true]
      exact ⟨ihFalse hinput, ihTrue hinput⟩

theorem depth_toFormula_internal
    {zeroInputs oneInputs : Set (BitString N)}
    (protocol : Protocol N zeroInputs oneInputs) :
    protocol.toFormula.depth = protocol.depth := by
  induction protocol <;>
    simp_all [toFormula, depth, MonotoneFormula.depth]

theorem toFormula_computes_internal
    (function : BitString N → Bool)
    (protocol : RootProtocol function) :
    protocol.toFormula.Computes function := by
  intro input
  cases hvalue : function input
  · exact eval_toFormula_eq_false_internal protocol hvalue
  · exact eval_toFormula_eq_true_internal protocol hvalue

/-- Internal formula-to-protocol construction under arbitrary rectangle
invariants. -/
def ofFormulaInternal (formula : MonotoneFormula N)
    {zeroInputs oneInputs : Set (BitString N)}
    (zeroInvariant :
      ∀ input ∈ zeroInputs, formula.eval input = false)
    (oneInvariant :
      ∀ input ∈ oneInputs, formula.eval input = true) :
    Protocol N zeroInputs oneInputs :=
  match formula with
  | .var index =>
      .leaf index zeroInvariant oneInvariant
  | .conj left right =>
      .bob (fun input => left.eval input)
        (ofFormulaInternal left
          (fun input hinput => hinput.2)
          (fun input hinput => by
            have hvalue := oneInvariant input hinput
            rw [MonotoneFormula.eval, Bool.and_eq_true] at hvalue
            exact hvalue.1))
        (ofFormulaInternal right
          (fun input hinput => by
            have hvalue := zeroInvariant input hinput.1
            change (left.eval input && right.eval input) = false at hvalue
            have hleft : left.eval input = true := hinput.2
            rw [hleft] at hvalue
            exact hvalue)
          (fun input hinput => by
            have hvalue := oneInvariant input hinput
            rw [MonotoneFormula.eval, Bool.and_eq_true] at hvalue
            exact hvalue.2))
  | .disj left right =>
      .alice (fun input => left.eval input)
        (ofFormulaInternal right
          (fun input hinput =>
            (Bool.or_eq_false_iff.mp
              (zeroInvariant input hinput)).2)
          (fun input hinput => by
            have hvalue := oneInvariant input hinput.1
            change (left.eval input || right.eval input) = true at hvalue
            have hleft : left.eval input = false := hinput.2
            rw [hleft] at hvalue
            exact hvalue))
        (ofFormulaInternal left
          (fun input hinput =>
            (Bool.or_eq_false_iff.mp
              (zeroInvariant input hinput)).1)
          (fun input hinput => hinput.2))

theorem depth_ofFormulaInternal (formula : MonotoneFormula N)
    {zeroInputs oneInputs : Set (BitString N)}
    (zeroInvariant :
      ∀ input ∈ zeroInputs, formula.eval input = false)
    (oneInvariant :
      ∀ input ∈ oneInputs, formula.eval input = true) :
    (ofFormulaInternal formula zeroInvariant oneInvariant).depth =
      formula.depth := by
  induction formula generalizing zeroInputs oneInputs with
  | var index => rfl
  | conj left right ihLeft ihRight =>
      simp only [ofFormulaInternal, depth,
        MonotoneFormula.depth]
      rw [ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp only [ofFormulaInternal, depth,
        MonotoneFormula.depth]
      rw [ihRight, ihLeft, max_comm]

theorem exists_protocol_of_formula_internal
    (formula : MonotoneFormula N) (function : BitString N → Bool)
    (computes : formula.Computes function) :
    ∃ protocol : RootProtocol function,
      protocol.depth = formula.depth := by
  let zeroInvariant : ∀ input ∈ zeroFiber function,
      formula.eval input = false := fun input hinput =>
    (computes input).trans hinput
  let oneInvariant : ∀ input ∈ oneFiber function,
      formula.eval input = true := fun input hinput =>
    (computes input).trans hinput
  refine ⟨ofFormulaInternal formula zeroInvariant oneInvariant, ?_⟩
  exact depth_ofFormulaInternal formula zeroInvariant oneInvariant

theorem exists_formula_of_protocol_internal
    (function : BitString N → Bool)
    (protocol : RootProtocol function) :
    ∃ formula : MonotoneFormula N,
      formula.Computes function ∧ formula.depth = protocol.depth := by
  refine ⟨protocol.toFormula, ?_, ?_⟩
  · exact toFormula_computes_internal function protocol
  · exact depth_toFormula_internal protocol

theorem exists_protocol_depth_iff_formula_depth_internal
    (function : BitString N → Bool) (depthBound : ℕ) :
    (∃ protocol : RootProtocol function,
      protocol.depth ≤ depthBound) ↔
    ∃ formula : MonotoneFormula N,
      formula.Computes function ∧ formula.depth ≤ depthBound := by
  constructor
  · rintro ⟨protocol, hdepth⟩
    rcases exists_formula_of_protocol_internal function protocol with
      ⟨formula, computes, hformula⟩
    exact ⟨formula, computes, hformula.trans_le hdepth⟩
  · rintro ⟨formula, computes, hdepth⟩
    rcases exists_protocol_of_formula_internal
      formula function computes with
      ⟨protocol, hprotocol⟩
    exact ⟨protocol, hprotocol.trans_le hdepth⟩

end Protocol
end KarchmerWigderson
end Complexity
