/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.NormalForm.Internal
public import Complexitylib.Circuits.AC0.Normalization.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar

/-!
# AC0 circuit normalization -- proof internals
-/


public section

namespace Complexity

private theorem foldl_or_eq_true (n : ℕ) (values : Fin n → Bool) :
    (Fin.foldl n (fun result index => result || values index) false =
      true) ↔ ∃ index, values index = true := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    constructor
    · intro h
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [ih] at h
        obtain ⟨index, hindex⟩ := h
        exact ⟨index.castSucc, hindex⟩
      · exact ⟨Fin.last n, h⟩
    · rintro ⟨index, hindex⟩
      rw [Bool.or_eq_true]
      rcases Fin.lastCases
          (motive := fun index =>
            (∃ prior : Fin n, index = prior.castSucc) ∨
              index = Fin.last n)
          (Or.inr rfl) (fun prior => Or.inl ⟨prior, rfl⟩)
          index with ⟨prior, rfl⟩ | rfl
      · exact Or.inl ((ih _).mpr ⟨prior, hindex⟩)
      · exact Or.inr hindex

private theorem foldl_and_eq_true (n : ℕ) (values : Fin n → Bool) :
    (Fin.foldl n (fun result index => result && values index) true =
      true) ↔ ∀ index, values index = true := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    constructor
    · intro h
      rw [Bool.and_eq_true] at h
      exact fun index =>
        Fin.lastCases h.2 (fun prior => (ih _).mp h.1 prior) index
    · intro h
      rw [Bool.and_eq_true]
      exact ⟨(ih _).mpr (fun prior => h prior.castSucc),
        h (Fin.last n)⟩

private theorem foldl_or_not (n : ℕ) (values : Fin n → Bool) :
    Fin.foldl n (fun result index => result || !(values index)) false =
      !Fin.foldl n (fun result index => result && values index) true := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last, ih]
    cases Fin.foldl n
        (fun result index => result && values index.castSucc) true <;>
      cases values (Fin.last n) <;> rfl

private theorem foldl_and_not (n : ℕ) (values : Fin n → Bool) :
    Fin.foldl n (fun result index => result && !(values index)) true =
      !Fin.foldl n (fun result index => result || values index) false := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last, ih]
    cases Fin.foldl n
        (fun result index => result || values index.castSucc) false <;>
      cases values (Fin.last n) <;> rfl

private theorem le_foldl_max (values : Fin n → ℕ) (index : Fin n) :
    values index ≤
      Fin.foldl n (fun result i => max result (values i)) 0 := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    refine Fin.lastCases (le_max_right _ _) (fun prior => ?_) index
    exact (ih (fun i => values i.castSucc) prior).trans
      (le_max_left _ _)

private theorem List.foldr_max_le {α : Type} (values : α → ℕ)
    (items : List α) (bound : ℕ)
    (hbound : ∀ item ∈ items, values item ≤ bound) :
    items.foldr (fun item rest => max (values item) rest) 0 ≤
      bound := by
  induction items with
  | nil => simp
  | cons item items ih =>
    simp only [List.foldr_cons]
    apply max_le
    · exact hbound item (List.mem_cons_self)
    · apply ih
      intro child hchild
      exact hbound child (List.mem_cons_of_mem item hchild)

private theorem List.sum_map_le_length_mul {α : Type}
    (values : α → ℕ) (items : List α) (bound : ℕ)
    (hbound : ∀ item ∈ items, values item ≤ bound) :
    (items.map values).sum ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item items ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons,
      Nat.succ_mul]
    have hhead := hbound item (List.mem_cons_self)
    have htail := ih fun child hchild =>
      hbound child (List.mem_cons_of_mem item hchild)
    omega

private theorem image_attach_all {α : Type} [DecidableEq α]
    (values : Fin n → α) (predicate : α → Bool) :
    ((Finset.univ.image values).attach.toList.all
      fun value => predicate value.val) =
      Fin.foldl n
        (fun result index => result && predicate (values index)) true := by
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, foldl_and_eq_true]
  constructor
  · intro h index
    let value : {value // value ∈ Finset.univ.image values} :=
      ⟨values index, Finset.mem_image.mpr ⟨index,
        Finset.mem_univ index, rfl⟩⟩
    exact h value (by simp [value])
  · intro h value _
    obtain ⟨index, _, hvalue⟩ :=
      Finset.mem_image.mp value.property
    rw [← hvalue]
    exact h index

private theorem image_attach_any {α : Type} [DecidableEq α]
    (values : Fin n → α) (predicate : α → Bool) :
    ((Finset.univ.image values).attach.toList.any
      fun value => predicate value.val) =
      Fin.foldl n
        (fun result index => result || predicate (values index)) false := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, foldl_or_eq_true]
  constructor
  · rintro ⟨value, _, hvalue⟩
    obtain ⟨index, _, hindex⟩ :=
      Finset.mem_image.mp value.property
    exact ⟨index, by simpa only [hindex] using hvalue⟩
  · rintro ⟨index, hindex⟩
    let value : {value // value ∈ Finset.univ.image values} :=
      ⟨values index, Finset.mem_image.mpr ⟨index,
        Finset.mem_univ index, rfl⟩⟩
    exact ⟨value, by simp [value], hindex⟩

private theorem signedSupport_eval
    (gate : Gate Basis.unboundedAndOr W) (outerNegated : Bool)
    (wireValue : BitString W) :
    (match gate.op.dualIf outerNegated with
      | .and =>
          (gate.signedSupport outerNegated).attach.toList.all
            fun source =>
              source.val.2.xor (wireValue source.val.1)
      | .or =>
          (gate.signedSupport outerNegated).attach.toList.any
            fun source =>
              source.val.2.xor (wireValue source.val.1)) =
      outerNegated.xor (gate.eval wireValue) := by
  cases outerNegated with
  | false =>
    cases hop : gate.op with
    | and =>
      simp only [AndOrOp.dualIf, Bool.false_eq_true, ite_false,
        Gate.signedSupport]
      have hsupport := image_attach_all
        (fun input : Fin gate.fanIn =>
          (gate.inputs input, false.xor (gate.negated input)))
        (fun signed : Fin W × Bool =>
          signed.2.xor (wireValue signed.1))
      rw [hsupport]
      simp only [Bool.false_xor, Gate.eval,
        Basis.unboundedAndOr, hop]
      rfl
    | or =>
      simp only [AndOrOp.dualIf, Bool.false_eq_true, ite_false,
        Gate.signedSupport]
      have hsupport := image_attach_any
        (fun input : Fin gate.fanIn =>
          (gate.inputs input, false.xor (gate.negated input)))
        (fun signed : Fin W × Bool =>
          signed.2.xor (wireValue signed.1))
      rw [hsupport]
      simp only [Bool.false_xor, Gate.eval,
        Basis.unboundedAndOr, hop]
      rfl
  | true =>
    have hxor : ∀ input : Fin gate.fanIn,
        (!gate.negated input).xor (wireValue (gate.inputs input)) =
          !(gate.negated input).xor
            (wireValue (gate.inputs input)) := by
      intro input
      cases gate.negated input <;>
        cases wireValue (gate.inputs input) <;> rfl
    cases hop : gate.op with
    | and =>
      simp only [AndOrOp.dualIf, ite_true, AndOrOp.dual,
        Gate.signedSupport]
      have hsupport := image_attach_any
        (fun input : Fin gate.fanIn =>
          (gate.inputs input, true.xor (gate.negated input)))
        (fun signed : Fin W × Bool =>
          signed.2.xor (wireValue signed.1))
      rw [hsupport]
      simp only [Gate.eval, Basis.unboundedAndOr, hop,
        Bool.true_xor]
      simp_rw [hxor]
      rw [foldl_or_not]
      rfl
    | or =>
      simp only [AndOrOp.dualIf, ite_true, AndOrOp.dual,
        Gate.signedSupport]
      have hsupport := image_attach_all
        (fun input : Fin gate.fanIn =>
          (gate.inputs input, true.xor (gate.negated input)))
        (fun signed : Fin W × Bool =>
          signed.2.xor (wireValue signed.1))
      rw [hsupport]
      simp only [Gate.eval, Basis.unboundedAndOr, hop,
        Bool.true_xor]
      simp_rw [hxor]
      rw [foldl_and_not]
      rfl

theorem signedSupport_card_le_internal
    (gate : Gate Basis.unboundedAndOr W)
    (outerNegated : Bool) :
    (gate.signedSupport outerNegated).card ≤ 2 * W := by
  calc
    (gate.signedSupport outerNegated).card ≤
        Fintype.card (Fin W × Bool) :=
      Finset.card_le_univ _
    _ = 2 * W := by
      simp [Fintype.card_prod, Fintype.card_fin]
      omega

namespace Circuit

variable {N M G : ℕ} [NeZero N] [NeZero M]

theorem eval_wireAC0Formula_internal
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (input : BitString N) (negated : Bool)
    (wire : Fin (N + G)) :
    (circuit.wireAC0Formula negated wire).eval input =
      negated.xor (circuit.wireValue input wire) := by
  induction hwire : wire.val using Nat.strong_induction_on
      generalizing wire negated with
  | h wireIndex ih =>
    by_cases hinput : wire.val < N
    · rw [wireAC0Formula]
      simp only [hinput, dite_true, AC0Formula.eval, Literal.eval,
        Circuit.wireValue_of_lt circuit input wire hinput]
      cases negated <;>
        cases input ⟨wire.val, hinput⟩ <;> rfl
    · rw [wireAC0Formula]
      simp only [hinput, dite_false]
      rw [Circuit.wireValue_of_not_lt circuit input wire hinput]
      let gateIndex : Fin G := ⟨wire.val - N, by omega⟩
      let gate := circuit.gates gateIndex
      change AC0Formula.eval input
          (AC0Formula.ofOp (gate.op.dualIf negated)
            (AC0Forest.ofList
              ((gate.signedSupport negated).attach.toList.map
                fun source =>
                  circuit.wireAC0Formula source.val.2
                    source.val.1))) =
        negated.xor (gate.eval (circuit.wireValue input))
      have hsource_lt :
          ∀ source :
              {signed // signed ∈ gate.signedSupport negated},
            source.val.1.val < wire.val := by
        intro source
        obtain ⟨edge, _, hedge⟩ :=
          Finset.mem_image.mp source.property
        have hvalue := congrArg
          (fun signed : Fin (N + G) × Bool => signed.1.val)
          hedge
        have hacyclic := circuit.acyclic gateIndex edge
        calc
          source.val.1.val = (gate.inputs edge).val := by
            simpa only using hvalue.symm
          _ < N + gateIndex.val := by
            simpa only [gate] using hacyclic
          _ = wire.val := by
            simp only [gateIndex]
            omega
      have hrec :
          ∀ source :
              {signed // signed ∈ gate.signedSupport negated},
            AC0Formula.eval input
                (circuit.wireAC0Formula source.val.2
                  source.val.1) =
              source.val.2.xor
                (circuit.wireValue input source.val.1) := by
        intro source
        apply ih source.val.1.val
        · rw [← hwire]
          exact hsource_lt source
        · rfl
      rw [← signedSupport_eval gate negated
        (circuit.wireValue input)]
      cases gate.op.dualIf negated <;>
        simp only [AC0Formula.ofOp, AC0Formula.eval,
          AC0Formula.evalAll_ofList_internal,
          AC0Formula.evalAny_ofList_internal, List.all_map,
          List.any_map, Function.comp_def] <;>
        simp_rw [hrec]

theorem eval_outputAC0Formula_internal
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (input : BitString N) (output : Fin M) :
    (circuit.outputAC0Formula output).eval input =
      circuit.eval input output := by
  unfold outputAC0Formula
  simp only
  let gate := circuit.outputs output
  change AC0Formula.eval input
      (AC0Formula.ofOp gate.op
        (AC0Forest.ofList
          ((gate.signedSupport false).attach.toList.map
            fun source =>
              circuit.wireAC0Formula source.val.2
                source.val.1))) =
    gate.eval (circuit.wireValue input)
  have hrec :
      ∀ source : {signed // signed ∈ gate.signedSupport false},
        AC0Formula.eval input
            (circuit.wireAC0Formula source.val.2 source.val.1) =
          source.val.2.xor
            (circuit.wireValue input source.val.1) := by
    intro source
    exact eval_wireAC0Formula_internal circuit input
      source.val.2 source.val.1
  have hsupport := signedSupport_eval gate false
    (circuit.wireValue input)
  simp only [Bool.false_xor, AndOrOp.dualIf,
    Bool.false_eq_true, ↓reduceIte] at hsupport
  rw [← hsupport]
  cases gate.op <;>
    simp only [AC0Formula.ofOp, AC0Formula.eval,
      AC0Formula.evalAll_ofList_internal,
      AC0Formula.evalAny_ofList_internal, List.all_map,
      List.any_map, Function.comp_def] <;>
    simp_rw [hrec]

theorem depth_wireAC0Formula_internal
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (negated : Bool) (wire : Fin (N + G)) :
    (circuit.wireAC0Formula negated wire).depth ≤
      circuit.wireDepth wire := by
  induction hwire : wire.val using Nat.strong_induction_on
      generalizing wire negated with
  | h wireIndex ih =>
    by_cases hinput : wire.val < N
    · rw [wireAC0Formula]
      simp only [hinput, dite_true, AC0Formula.depth,
        Circuit.wireDepth_of_lt circuit wire hinput]
      exact Nat.le_refl 0
    · rw [wireAC0Formula]
      simp only [hinput, dite_false]
      rw [Circuit.wireDepth_of_not_lt circuit wire hinput]
      let gateIndex : Fin G := ⟨wire.val - N, by omega⟩
      let gate := circuit.gates gateIndex
      change
        (AC0Formula.ofOp (gate.op.dualIf negated)
            (AC0Forest.ofList
              ((gate.signedSupport negated).attach.toList.map
                fun source =>
                  circuit.wireAC0Formula source.val.2
                    source.val.1))).depth ≤
          1 + Fin.foldl gate.fanIn
            (fun result edge =>
              max result
                (circuit.wireDepth (gate.inputs edge))) 0
      have hsource_lt :
          ∀ source :
              {signed // signed ∈ gate.signedSupport negated},
            source.val.1.val < wire.val := by
        intro source
        obtain ⟨edge, _, hedge⟩ :=
          Finset.mem_image.mp source.property
        have hvalue := congrArg
          (fun signed : Fin (N + G) × Bool => signed.1.val)
          hedge
        have hacyclic := circuit.acyclic gateIndex edge
        calc
          source.val.1.val = (gate.inputs edge).val := by
            simpa only using hvalue.symm
          _ < N + gateIndex.val := by
            simpa only [gate] using hacyclic
          _ = wire.val := by
            simp only [gateIndex]
            omega
      have hrec :
          ∀ source :
              {signed // signed ∈ gate.signedSupport negated},
            (circuit.wireAC0Formula source.val.2
              source.val.1).depth ≤
                circuit.wireDepth source.val.1 := by
        intro source
        apply ih source.val.1.val
        · rw [← hwire]
          exact hsource_lt source
        · rfl
      have hsourceDepth :
          ∀ source :
              {signed // signed ∈ gate.signedSupport negated},
            circuit.wireDepth source.val.1 ≤
              Fin.foldl gate.fanIn
                (fun result edge =>
                  max result
                    (circuit.wireDepth (gate.inputs edge))) 0 := by
        intro source
        obtain ⟨edge, _, hedge⟩ :=
          Finset.mem_image.mp source.property
        have hvalue := congrArg
          (fun signed : Fin (N + G) × Bool => signed.1) hedge
        simp only at hvalue
        rw [← hvalue]
        exact le_foldl_max
          (fun edge => circuit.wireDepth (gate.inputs edge)) edge
      cases gate.op.dualIf negated <;>
        simp only [AC0Formula.ofOp, AC0Formula.depth,
          AC0Formula.forestDepth_ofList_internal,
          List.foldr_map] <;>
        apply Nat.add_le_add_left <;>
        apply List.foldr_max_le <;>
        intro source hsource <;>
        exact (hrec source).trans (hsourceDepth source)

theorem depth_outputAC0Formula_internal
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (output : Fin M) :
    (circuit.outputAC0Formula output).depth ≤
      circuit.outputDepth output := by
  unfold outputAC0Formula Circuit.outputDepth
  simp only
  let gate := circuit.outputs output
  change
    (AC0Formula.ofOp gate.op
        (AC0Forest.ofList
          ((gate.signedSupport false).attach.toList.map
            fun source =>
              circuit.wireAC0Formula source.val.2
                source.val.1))).depth ≤
      1 + Fin.foldl gate.fanIn
        (fun result edge =>
          max result (circuit.wireDepth (gate.inputs edge))) 0
  have hrec :
      ∀ source : {signed // signed ∈ gate.signedSupport false},
        (circuit.wireAC0Formula source.val.2
          source.val.1).depth ≤
            circuit.wireDepth source.val.1 := by
    intro source
    exact depth_wireAC0Formula_internal circuit source.val.2
      source.val.1
  have hsourceDepth :
      ∀ source : {signed // signed ∈ gate.signedSupport false},
        circuit.wireDepth source.val.1 ≤
          Fin.foldl gate.fanIn
            (fun result edge =>
              max result
                (circuit.wireDepth (gate.inputs edge))) 0 := by
    intro source
    obtain ⟨edge, _, hedge⟩ :=
      Finset.mem_image.mp source.property
    have hvalue := congrArg
      (fun signed : Fin (N + G) × Bool => signed.1) hedge
    simp only at hvalue
    rw [← hvalue]
    exact le_foldl_max
      (fun edge => circuit.wireDepth (gate.inputs edge)) edge
  cases gate.op <;>
    simp only [AC0Formula.ofOp, AC0Formula.depth,
      AC0Formula.forestDepth_ofList_internal, List.foldr_map] <;>
    apply Nat.add_le_add_left <;>
    apply List.foldr_max_le <;>
    intro source hsource <;>
    exact (hrec source).trans (hsourceDepth source)

theorem size_wireAC0Formula_internal
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (negated : Bool) (wire : Fin (N + G)) :
    (circuit.wireAC0Formula negated wire).size ≤
      (2 * (N + G) + 1) ^ (circuit.wireDepth wire + 1) := by
  let base := 2 * (N + G) + 1
  induction hwire : wire.val using Nat.strong_induction_on
      generalizing wire negated with
  | h wireIndex ih =>
    by_cases hinput : wire.val < N
    · rw [wireAC0Formula]
      simp only [hinput, dite_true, AC0Formula.size,
        Circuit.wireDepth_of_lt circuit wire hinput]
      change 1 ≤ base ^ 1
      rw [Nat.pow_one]
      simp [base]
    · rw [wireAC0Formula]
      simp only [hinput, dite_false]
      rw [Circuit.wireDepth_of_not_lt circuit wire hinput]
      let gateIndex : Fin G := ⟨wire.val - N, by omega⟩
      let gate := circuit.gates gateIndex
      let maximum := Fin.foldl gate.fanIn
        (fun result edge =>
          max result (circuit.wireDepth (gate.inputs edge))) 0
      change
        (AC0Formula.ofOp (gate.op.dualIf negated)
            (AC0Forest.ofList
              ((gate.signedSupport negated).attach.toList.map
                fun source =>
                  circuit.wireAC0Formula source.val.2
                    source.val.1))).size ≤
          base ^ (1 + maximum + 1)
      have hsource_lt :
          ∀ source :
              {signed // signed ∈ gate.signedSupport negated},
            source.val.1.val < wire.val := by
        intro source
        obtain ⟨edge, _, hedge⟩ :=
          Finset.mem_image.mp source.property
        have hvalue := congrArg
          (fun signed : Fin (N + G) × Bool => signed.1.val)
          hedge
        have hacyclic := circuit.acyclic gateIndex edge
        calc
          source.val.1.val = (gate.inputs edge).val := by
            simpa only using hvalue.symm
          _ < N + gateIndex.val := by
            simpa only [gate] using hacyclic
          _ = wire.val := by
            simp only [gateIndex]
            omega
      have hrec :
          ∀ source :
              {signed // signed ∈ gate.signedSupport negated},
            (circuit.wireAC0Formula source.val.2
              source.val.1).size ≤
                base ^ (circuit.wireDepth source.val.1 + 1) := by
        intro source
        apply ih source.val.1.val
        · rw [← hwire]
          exact hsource_lt source
        · rfl
      have hsourceDepth :
          ∀ source :
              {signed // signed ∈ gate.signedSupport negated},
            circuit.wireDepth source.val.1 ≤ maximum := by
        intro source
        obtain ⟨edge, _, hedge⟩ :=
          Finset.mem_image.mp source.property
        have hvalue := congrArg
          (fun signed : Fin (N + G) × Bool => signed.1) hedge
        simp only at hvalue
        rw [← hvalue]
        exact le_foldl_max
          (fun edge => circuit.wireDepth (gate.inputs edge)) edge
      have hchild :
          ∀ source :
              {signed // signed ∈ gate.signedSupport negated},
            (circuit.wireAC0Formula source.val.2
              source.val.1).size ≤ base ^ (maximum + 1) := by
        intro source
        exact (hrec source).trans
          (Nat.pow_le_pow_right (by simp [base])
            (Nat.add_le_add_right (hsourceDepth source) 1))
      have hlength :
          (gate.signedSupport negated).attach.toList.length ≤
            2 * (N + G) := by
        simpa only [Finset.length_toList, Finset.card_attach] using
          signedSupport_card_le_internal gate negated
      have hsum := List.sum_map_le_length_mul
        (fun source :
            {signed // signed ∈ gate.signedSupport negated} =>
          (circuit.wireAC0Formula source.val.2
            source.val.1).size)
        (gate.signedSupport negated).attach.toList
        (base ^ (maximum + 1))
        (fun source _ => hchild source)
      have hsum' :
          (((gate.signedSupport negated).attach.toList.map
            fun source =>
              (circuit.wireAC0Formula source.val.2
                source.val.1).size).sum) ≤
            (2 * (N + G)) * base ^ (maximum + 1) :=
        hsum.trans (Nat.mul_le_mul_right _ hlength)
      have hpow : 1 ≤ base ^ (maximum + 1) :=
        Nat.one_le_pow _ base (by simp [base])
      cases gate.op.dualIf negated <;>
        simp only [AC0Formula.ofOp, AC0Formula.size,
          AC0Formula.forestSize_ofList_internal, List.map_map,
          Function.comp_def] <;>
        calc
          1 +
                (((gate.signedSupport negated).attach.toList.map
                  fun source =>
                    (circuit.wireAC0Formula source.val.2
                      source.val.1).size).sum)
              ≤ 1 + (2 * (N + G)) * base ^ (maximum + 1) :=
            Nat.add_le_add_left hsum' 1
          _ ≤ base ^ (maximum + 1) +
                (2 * (N + G)) * base ^ (maximum + 1) :=
            Nat.add_le_add_right hpow _
          _ = base ^ (1 + maximum + 1) := by
            rw [show 1 + maximum + 1 =
                (maximum + 1) + 1 by omega,
              Nat.pow_succ]
            simp only [base]
            ring

theorem size_outputAC0Formula_internal
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (output : Fin M) :
    (circuit.outputAC0Formula output).size ≤
      (2 * (N + G) + 1) ^ (circuit.outputDepth output + 1) := by
  unfold outputAC0Formula Circuit.outputDepth
  simp only
  let base := 2 * (N + G) + 1
  let gate := circuit.outputs output
  let maximum := Fin.foldl gate.fanIn
    (fun result edge =>
      max result (circuit.wireDepth (gate.inputs edge))) 0
  change
    (AC0Formula.ofOp gate.op
        (AC0Forest.ofList
          ((gate.signedSupport false).attach.toList.map
            fun source =>
              circuit.wireAC0Formula source.val.2
                source.val.1))).size ≤
      base ^ (1 + maximum + 1)
  have hrec :
      ∀ source : {signed // signed ∈ gate.signedSupport false},
        (circuit.wireAC0Formula source.val.2
          source.val.1).size ≤
            base ^ (circuit.wireDepth source.val.1 + 1) := by
    intro source
    exact size_wireAC0Formula_internal circuit source.val.2
      source.val.1
  have hsourceDepth :
      ∀ source : {signed // signed ∈ gate.signedSupport false},
        circuit.wireDepth source.val.1 ≤ maximum := by
    intro source
    obtain ⟨edge, _, hedge⟩ :=
      Finset.mem_image.mp source.property
    have hvalue := congrArg
      (fun signed : Fin (N + G) × Bool => signed.1) hedge
    simp only at hvalue
    rw [← hvalue]
    exact le_foldl_max
      (fun edge => circuit.wireDepth (gate.inputs edge)) edge
  have hchild :
      ∀ source : {signed // signed ∈ gate.signedSupport false},
        (circuit.wireAC0Formula source.val.2
          source.val.1).size ≤ base ^ (maximum + 1) := by
    intro source
    exact (hrec source).trans
      (Nat.pow_le_pow_right (by simp [base])
        (Nat.add_le_add_right (hsourceDepth source) 1))
  have hlength :
      (gate.signedSupport false).attach.toList.length ≤
        2 * (N + G) := by
    simpa only [Finset.length_toList, Finset.card_attach] using
      signedSupport_card_le_internal gate false
  have hsum := List.sum_map_le_length_mul
    (fun source : {signed // signed ∈ gate.signedSupport false} =>
      (circuit.wireAC0Formula source.val.2 source.val.1).size)
    (gate.signedSupport false).attach.toList
    (base ^ (maximum + 1))
    (fun source _ => hchild source)
  have hsum' :
      (((gate.signedSupport false).attach.toList.map
        fun source =>
          (circuit.wireAC0Formula source.val.2
            source.val.1).size).sum) ≤
        (2 * (N + G)) * base ^ (maximum + 1) :=
    hsum.trans (Nat.mul_le_mul_right _ hlength)
  have hpow : 1 ≤ base ^ (maximum + 1) :=
    Nat.one_le_pow _ base (by simp [base])
  cases gate.op <;>
    simp only [AC0Formula.ofOp, AC0Formula.size,
      AC0Formula.forestSize_ofList_internal, List.map_map,
      Function.comp_def] <;>
    calc
      1 +
            (((gate.signedSupport false).attach.toList.map
              fun source =>
                (circuit.wireAC0Formula source.val.2
                  source.val.1).size).sum)
          ≤ 1 + (2 * (N + G)) * base ^ (maximum + 1) :=
        Nat.add_le_add_left hsum' 1
      _ ≤ base ^ (maximum + 1) +
            (2 * (N + G)) * base ^ (maximum + 1) :=
        Nat.add_le_add_right hpow _
      _ = base ^ (1 + maximum + 1) := by
        rw [show 1 + maximum + 1 =
            (maximum + 1) + 1 by omega,
          Nat.pow_succ]
        simp only [base]
        ring

end Circuit

end Complexity
