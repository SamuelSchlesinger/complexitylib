/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Arithmetic
public import Complexitylib.Algebraic.MassProduction.InputSplit
public import Complexitylib.Algebraic.MassProduction.ShannonCircuit
public import Complexitylib.Algebraic.MassProduction.Uhlig

/-!
# Uhlig routing circuits

This module lifts Uhlig's two-request recovery invariant to Boolean functions
on independent row-major inputs. It defines the finite semantic layer,
explicitly routes each request suffix to its selected resources, and composes
those routers with an externally supplied bank of shorter-function circuits.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace UhligCircuit

open scoped BigOperators

/-- The final source index among the `2 ^ prefixWidth` prefix assignments. -/
def prefixLast (prefixWidth : Nat) : Nat :=
  2 ^ prefixWidth - 1

theorem prefixCount_eq (prefixWidth : Nat) :
    prefixLast prefixWidth + 1 = 2 ^ prefixWidth := by
  unfold prefixLast
  have positive : 0 < 2 ^ prefixWidth := Nat.two_pow_pos prefixWidth
  omega

/-- Restrict the first `prefixWidth` variables of a Boolean function to one
canonical source value. -/
def restriction
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (source : Fin (prefixLast prefixWidth + 1)) :
    ScalarFunction Bool suffixWidth :=
  fun suffix => function (InputSplit.joinedInput
    (Fin.cast (prefixCount_eq prefixWidth) source) suffix)

/-- Uhlig's resource functions, now viewed as functions of the unspecialized
suffix variables. -/
def resourceFunction
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (resource : Fin (prefixLast prefixWidth + 2)) :
    ScalarFunction Bool suffixWidth :=
  uhligResource (fun source => restriction function source) resource

/-- Pair-major enumeration of the `2 * pairs` requests. -/
def pairRequest
    (pair : Fin pairs) (side : Fin 2) : Fin (2 * pairs) :=
  Fin.cast (Nat.mul_comm pairs 2) (finProdFinEquiv (pair, side))

/-- The full input block belonging to one side of one request pair. -/
def requestBlock
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    Fin (prefixWidth + suffixWidth) -> Bool :=
  directProductInput input (pairRequest pair side)

/-- The prefix bits of one request. -/
def requestPrefix
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) : Fin prefixWidth -> Bool :=
  fun bit => requestBlock input pair side (Fin.castAdd suffixWidth bit)

/-- The suffix bits of one request. -/
def requestSuffix
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) : Fin suffixWidth -> Bool :=
  fun bit => requestBlock input pair side (Fin.natAdd prefixWidth bit)

/-- Canonical numeric source selected by the request prefix. -/
def requestSource
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    Fin (prefixLast prefixWidth + 1) :=
  Fin.cast (prefixCount_eq prefixWidth).symm
    (RuntimePacking.source (requestPrefix input pair side))

/-- The two disjoint resource sets assigned to one request pair. -/
def recoveryPair
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) :
    Prod (Finset (Fin (prefixLast prefixWidth + 2)))
      (Finset (Fin (prefixLast prefixWidth + 2))) :=
  uhligRecoveryPair (requestSource input pair 0)
    (requestSource input pair 1)

/-- Runtime suffix sent to one resource.  Disjointness makes the first two
branches mutually exclusive; an unused resource receives an arbitrary zero
suffix. -/
def routedSuffix
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs)
    (resource : Fin (prefixLast prefixWidth + 2)) :
    Fin suffixWidth -> Bool :=
  if resource ∈ (recoveryPair input pair).1 then
    requestSuffix input pair 0
  else if resource ∈ (recoveryPair input pair).2 then
    requestSuffix input pair 1
  else
    fun _ => false

/-- Value produced by one resource for one request pair. -/
def resourceValue
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs)
    (resource : Fin (prefixLast prefixWidth + 2)) : Bool :=
  resourceFunction function resource (routedSuffix input pair resource)

/-- Decode one requested output by XORing its assigned resource values. -/
def decodedValue
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) : Bool :=
  let resources : Finset (Fin (prefixLast prefixWidth + 2)) :=
    Fin.cases (recoveryPair input pair).1
    (fun _ => (recoveryPair input pair).2) side
  resources.sum fun resource => resourceValue function input pair resource

/-- The runtime prefix and suffix really reassemble the selected input
block. -/
theorem joined_request_eq_requestBlock
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    InputSplit.joinedInput
        (Fin.cast (prefixCount_eq prefixWidth)
          (requestSource input pair side))
        (requestSuffix input pair side) =
      requestBlock input pair side := by
  funext index
  refine Fin.addCases (motive := fun index =>
      InputSplit.joinedInput
          (Fin.cast (prefixCount_eq prefixWidth)
            (requestSource input pair side))
          (requestSuffix input pair side) index =
        requestBlock input pair side index)
    (fun prefixBit => ?_) (fun suffixBit => ?_) index
  · simp [InputSplit.joinedInput, requestSource, requestPrefix]
  · simp [InputSplit.joinedInput, requestSuffix]

theorem restriction_requestSource_requestSuffix
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    restriction function (requestSource input pair side)
        (requestSuffix input pair side) =
      function (requestBlock input pair side) := by
  unfold restriction
  rw [joined_request_eq_requestBlock]

theorem routedSuffix_eq_left
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs)
    (resource : Fin (prefixLast prefixWidth + 2))
    (member : resource ∈ (recoveryPair input pair).1) :
    routedSuffix input pair resource = requestSuffix input pair 0 := by
  simp [routedSuffix, member]

theorem routedSuffix_eq_right
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs)
    (resource : Fin (prefixLast prefixWidth + 2))
    (member : resource ∈ (recoveryPair input pair).2) :
    routedSuffix input pair resource = requestSuffix input pair 1 := by
  have disjoint :
      Disjoint (recoveryPair input pair).1 (recoveryPair input pair).2 := by
    exact uhligRecoveryPair_disjoint
      (requestSource input pair 0) (requestSource input pair 1)
  have notLeft : resource ∉ (recoveryPair input pair).1 := by
    intro leftMember
    exact Finset.disjoint_left.mp disjoint leftMember member
  simp [routedSuffix, member, notLeft]

/-- Exact correctness for one side of one pair. -/
theorem decodedValue_eq
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    decodedValue function input pair side =
      function (requestBlock input pair side) := by
  let values : Fin (prefixLast prefixWidth + 1) ->
      (Fin suffixWidth -> Bool) -> Bool :=
    fun source => restriction function source
  have recovery := uhligBoolean_two_copy_disjoint_recovery
    (Z := Fin suffixWidth -> Bool) values
    (requestSource input pair 0) (requestSource input pair 1)
  refine Fin.cases ?_ (fun finalSide => ?_) side
  · change
      (recoveryPair input pair).1.sum
          (fun resource => resourceValue function input pair resource) =
        function (requestBlock input pair 0)
    have pointwise := congrFun recovery.2.1 (requestSuffix input pair 0)
    dsimp [values] at pointwise
    rw [restriction_requestSource_requestSuffix] at pointwise
    rw [recoveryPair]
    rw [Finset.sum_apply] at pointwise
    rw [← pointwise]
    apply Finset.sum_congr rfl
    intro resource member
    rw [resourceValue, routedSuffix_eq_left input pair resource member]
    rfl
  · have finalSideZero : finalSide = 0 := Subsingleton.elim _ _
    subst finalSide
    change
      (recoveryPair input pair).2.sum
          (fun resource => resourceValue function input pair resource) =
        function (requestBlock input pair 1)
    have pointwise := congrFun recovery.2.2 (requestSuffix input pair 1)
    dsimp [values] at pointwise
    rw [restriction_requestSource_requestSuffix] at pointwise
    rw [recoveryPair]
    rw [Finset.sum_apply] at pointwise
    rw [← pointwise]
    apply Finset.sum_congr rfl
    intro resource member
    rw [resourceValue, routedSuffix_eq_right input pair resource member]
    rfl

/-- Exact row-major finite Uhlig layer: decoding all pairs is the ordinary
direct product of the original function. -/
theorem decodedValue_eq_directProduct
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool) :
    (fun output =>
        let pairSide := finProdFinEquiv.symm
          (Fin.cast (Nat.mul_comm 2 pairs) output)
        decodedValue function input pairSide.1 pairSide.2) =
      directProduct function (2 * pairs) input := by
  funext output
  let pairSide := finProdFinEquiv.symm
    (Fin.cast (Nat.mul_comm 2 pairs) output)
  have outputEq : pairRequest pairSide.1 pairSide.2 = output := by
    unfold pairRequest pairSide
    rw [Equiv.apply_symm_apply]
    simp
  rw [decodedValue_eq]
  unfold requestBlock
  rw [outputEq]
  rfl

/-! ## Explicit routing expressions -/

/-- Input coordinate in one two-request block. -/
def localInputIndex
    (side : Fin 2) (coordinate : Fin (prefixWidth + suffixWidth)) :
    Fin (2 * (prefixWidth + suffixWidth)) :=
  finProdFinEquiv (side, coordinate)

/-- Prefix bits in one two-request block. -/
def localPrefix
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool)
    (side : Fin 2) : Fin prefixWidth -> Bool :=
  fun bit => input (localInputIndex side (Fin.castAdd suffixWidth bit))

/-- Suffix bits in one two-request block. -/
def localSuffix
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool)
    (side : Fin 2) : Fin suffixWidth -> Bool :=
  fun bit => input (localInputIndex side (Fin.natAdd prefixWidth bit))

/-- Numeric source represented by a local request prefix. -/
def localSource
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool)
    (side : Fin 2) : Fin (prefixLast prefixWidth + 1) :=
  Fin.cast (prefixCount_eq prefixWidth).symm
    (RuntimePacking.source (localPrefix input side))

/-- Indicator that one local request prefix equals a fixed source. -/
def sourceIndicatorExpression
    (side : Fin 2)
    (source : Fin (prefixLast prefixWidth + 1)) :
    DeMorgan.Expression (2 * (prefixWidth + suffixWidth)) :=
  DeMorgan.Expression.finAnd prefixWidth fun bit =>
    ShannonSynthesis.matchingLiteral
      (localInputIndex side (Fin.castAdd suffixWidth bit))
      (InputSplit.sourceBits
        (Fin.cast (prefixCount_eq prefixWidth) source) bit)

theorem sourceIndicatorExpression_eval_eq_true_iff
    (side : Fin 2)
    (source : Fin (prefixLast prefixWidth + 1))
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool) :
    (sourceIndicatorExpression side source).eval input = true <->
      localSource input side = source := by
  rw [sourceIndicatorExpression, DeMorgan.Expression.finAnd_eval,
    DeMorgan.Expression.finAndValue_eq_true_iff]
  constructor
  · intro everyBit
    have bitsEqual : localPrefix input side = InputSplit.sourceBits
        (Fin.cast (prefixCount_eq prefixWidth) source) := by
      funext bit
      have bitMatch := everyBit bit
      rw [ShannonSynthesis.matchingLiteral_eval] at bitMatch
      exact of_decide_eq_true bitMatch
    simp [localSource, bitsEqual]
  · intro sourceEqual bit
    rw [ShannonSynthesis.matchingLiteral_eval]
    apply decide_eq_true
    have encodedEqual : RuntimePacking.source (localPrefix input side) =
        Fin.cast (prefixCount_eq prefixWidth) source := by
      have castEqual := congrArg
        (Fin.cast (prefixCount_eq prefixWidth)) sourceEqual
      simpa [localSource] using castEqual
    calc
      localPrefix input side bit =
          InputSplit.sourceBits
            (RuntimePacking.source (localPrefix input side)) bit :=
        (congrFun (InputSplit.sourceBits_runtimeSource
          (localPrefix input side)) bit).symm
      _ = InputSplit.sourceBits
          (Fin.cast (prefixCount_eq prefixWidth) source) bit :=
        congrFun (congrArg InputSplit.sourceBits encodedEqual) bit

/-- The fixed suffix input chosen for a resource after the two prefixes have
been hardwired. -/
def fixedRoutedSuffixExpression
    (first second : Fin (prefixLast prefixWidth + 1))
    (resource : Fin (prefixLast prefixWidth + 2))
    (bit : Fin suffixWidth) :
    DeMorgan.Expression (2 * (prefixWidth + suffixWidth)) :=
  if resource ∈ (uhligRecoveryPair first second).1 then
    .input (localInputIndex 0 (Fin.natAdd prefixWidth bit))
  else if resource ∈ (uhligRecoveryPair first second).2 then
    .input (localInputIndex 1 (Fin.natAdd prefixWidth bit))
  else
    .constant false

/-- Runtime routing for one suffix bit, written as a one-hot selection over
the two request prefixes. -/
def routedSuffixExpression
    (resource : Fin (prefixLast prefixWidth + 2))
    (bit : Fin suffixWidth) :
    DeMorgan.Expression (2 * (prefixWidth + suffixWidth)) :=
  DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun first =>
    .and (sourceIndicatorExpression 0 first)
      (DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun second =>
        .and (sourceIndicatorExpression 1 second)
          (fixedRoutedSuffixExpression first second resource bit))

theorem fixedRoutedSuffixExpression_eval
    (first second : Fin (prefixLast prefixWidth + 1))
    (resource : Fin (prefixLast prefixWidth + 2))
    (bit : Fin suffixWidth)
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool) :
    (fixedRoutedSuffixExpression first second resource bit).eval input =
      (if resource ∈ (uhligRecoveryPair first second).1 then
        localSuffix input 0 bit
      else if resource ∈ (uhligRecoveryPair first second).2 then
        localSuffix input 1 bit
      else false) := by
  by_cases leftMember : resource ∈ (uhligRecoveryPair first second).1
  · simp only [fixedRoutedSuffixExpression, ite_eq_left leftMember]
    rfl
  · by_cases rightMember : resource ∈ (uhligRecoveryPair first second).2
    · simp only [fixedRoutedSuffixExpression, ite_eq_right leftMember,
        ite_eq_left rightMember]
      rfl
    · simp only [fixedRoutedSuffixExpression, ite_eq_right leftMember,
        ite_eq_right rightMember]
      rfl

theorem routedSuffixExpression_eval
    (resource : Fin (prefixLast prefixWidth + 2))
    (bit : Fin suffixWidth)
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool) :
    (routedSuffixExpression resource bit).eval input =
      (if resource ∈
          (uhligRecoveryPair (localSource input 0) (localSource input 1)).1 then
        localSuffix input 0 bit
      else if resource ∈
          (uhligRecoveryPair (localSource input 0) (localSource input 1)).2 then
        localSuffix input 1 bit
      else false) := by
  rw [routedSuffixExpression, DeMorgan.Expression.finOr_eval]
  simp only [DeMorgan.Expression.eval]
  let first := localSource input 0
  let second := localSource input 1
  have firstTrue :
      (sourceIndicatorExpression (suffixWidth := suffixWidth) 0 first).eval
          input = true :=
    (sourceIndicatorExpression_eval_eq_true_iff 0 first input).2 rfl
  have firstUnique : forall candidate,
      (sourceIndicatorExpression (suffixWidth := suffixWidth) 0 candidate).eval
          input = true -> candidate = first := by
    intro candidate candidateTrue
    exact ((sourceIndicatorExpression_eval_eq_true_iff
      0 candidate input).1 candidateTrue).symm
  rw [DeMorgan.Expression.finOrValue_oneHot
    (prefixLast prefixWidth + 1) first
    (fun candidate =>
      (sourceIndicatorExpression (suffixWidth := suffixWidth)
        0 candidate).eval input)
    (fun candidate =>
      (DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun other =>
        .and (sourceIndicatorExpression 1 other)
          (fixedRoutedSuffixExpression candidate other resource bit)).eval
        input)
    firstTrue firstUnique]
  rw [DeMorgan.Expression.finOr_eval]
  simp only [DeMorgan.Expression.eval]
  have secondTrue :
      (sourceIndicatorExpression (suffixWidth := suffixWidth) 1 second).eval
          input = true :=
    (sourceIndicatorExpression_eval_eq_true_iff 1 second input).2 rfl
  have secondUnique : forall candidate,
      (sourceIndicatorExpression (suffixWidth := suffixWidth) 1 candidate).eval
          input = true -> candidate = second := by
    intro candidate candidateTrue
    exact ((sourceIndicatorExpression_eval_eq_true_iff
      1 candidate input).1 candidateTrue).symm
  rw [DeMorgan.Expression.finOrValue_oneHot
    (prefixLast prefixWidth + 1) second
    (fun candidate =>
      (sourceIndicatorExpression (suffixWidth := suffixWidth)
        1 candidate).eval input)
    (fun candidate =>
      (fixedRoutedSuffixExpression first candidate resource bit).eval input)
    secondTrue secondUnique]
  exact fixedRoutedSuffixExpression_eval first second resource bit input

/-- Explicit circuit routing one pair's suffix to one Uhlig resource. -/
noncomputable def resourceRouterCircuit
    (resource : Fin (prefixLast prefixWidth + 2)) :
    Circuit DeMorgan.signature (2 * (prefixWidth + suffixWidth))
      suffixWidth :=
  Circuit.parallelFin suffixWidth
    (fun bit => (routedSuffixExpression resource bit).circuit)

@[simp] theorem resourceRouterCircuit_eval
    (resource : Fin (prefixLast prefixWidth + 2))
    (input : Fin (2 * (prefixWidth + suffixWidth)) -> Bool)
    (bit : Fin suffixWidth) :
    (resourceRouterCircuit resource).eval DeMorgan.interpretation input bit =
      (if resource ∈
          (uhligRecoveryPair (localSource input 0) (localSource input 1)).1 then
        localSuffix input 0 bit
      else if resource ∈
          (uhligRecoveryPair (localSource input 0) (localSource input 1)).2 then
        localSuffix input 1 bit
      else false) := by
  rw [resourceRouterCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval, routedSuffixExpression_eval]

/-! ## Batched routing and supplied resource circuits -/

/-- Embed one local two-request input into the corresponding global pair. -/
def pairInputMap
    (pair : Fin pairs)
    (input : Fin (2 * (prefixWidth + suffixWidth))) :
    Fin ((2 * pairs) * (prefixWidth + suffixWidth)) :=
  let sideCoordinate := finProdFinEquiv.symm input
  finProdFinEquiv
    (pairRequest pair sideCoordinate.1, sideCoordinate.2)

@[simp] theorem pairInputMap_localInputIndex
    (pair : Fin pairs)
    (side : Fin 2)
    (coordinate : Fin (prefixWidth + suffixWidth)) :
    pairInputMap pair (localInputIndex side coordinate) =
      finProdFinEquiv (pairRequest pair side, coordinate) := by
  simp [pairInputMap, localInputIndex]

theorem localPrefix_pairInputMap
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    localPrefix (input ∘ pairInputMap pair) side =
      requestPrefix input pair side := by
  funext bit
  simp [localPrefix, requestPrefix, requestBlock, directProductInput,
    Function.comp_apply]

theorem localSuffix_pairInputMap
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    localSuffix (input ∘ pairInputMap pair) side =
      requestSuffix input pair side := by
  funext bit
  simp [localSuffix, requestSuffix, requestBlock, directProductInput,
    Function.comp_apply]

theorem localSource_pairInputMap
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    localSource (input ∘ pairInputMap pair) side =
      requestSource input pair side := by
  simp [localSource, requestSource, localPrefix_pairInputMap]

/-- Charged/gate count of one resource router. -/
@[reducible] noncomputable def resourceRouterGateCount
    (prefixWidth suffixWidth : Nat)
    (resource : Fin (prefixLast prefixWidth + 2)) : Nat :=
  Finset.univ.sum fun bit : Fin suffixWidth =>
    (routedSuffixExpression resource bit).gateCount

@[simp] theorem resourceRouterCircuit_size
    (resource : Fin (prefixLast prefixWidth + 2)) :
    (resourceRouterCircuit (suffixWidth := suffixWidth) resource).size =
      resourceRouterGateCount prefixWidth suffixWidth resource := by
  simp [resourceRouterCircuit, resourceRouterGateCount]

/-- Route all request pairs to one shared resource circuit. -/
noncomputable def resourceRouterArrayCircuit
    (pairs : Nat)
    (resource : Fin (prefixLast prefixWidth + 2)) :
    Circuit DeMorgan.signature
      ((2 * pairs) * (prefixWidth + suffixWidth))
      (pairs * suffixWidth) :=
  Circuit.parallelFinVector pairs suffixWidth
    (fun pair => (resourceRouterCircuit resource).mapInputs
      (pairInputMap pair))

@[simp] theorem resourceRouterArrayCircuit_size
    (pairs : Nat)
    (resource : Fin (prefixLast prefixWidth + 2)) :
    (resourceRouterArrayCircuit (suffixWidth := suffixWidth) pairs resource).size =
      Finset.univ.sum fun _pair : Fin pairs =>
        resourceRouterGateCount prefixWidth suffixWidth resource := by
  simp [resourceRouterArrayCircuit]

@[simp] theorem resourceRouterArrayCircuit_eval
    (pairs : Nat)
    (resource : Fin (prefixLast prefixWidth + 2))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs)
    (bit : Fin suffixWidth) :
    (resourceRouterArrayCircuit pairs resource).eval
        DeMorgan.interpretation input (finProdFinEquiv (pair, bit)) =
      routedSuffix input pair resource bit := by
  rw [resourceRouterArrayCircuit, Circuit.eval_parallelFinVector,
    Circuit.eval_mapInputs, resourceRouterCircuit_eval]
  rw [localSource_pairInputMap, localSource_pairInputMap,
    localSuffix_pairInputMap, localSuffix_pairInputMap]
  unfold routedSuffix recoveryPair
  by_cases leftMember : resource ∈
      (uhligRecoveryPair (requestSource input pair 0)
        (requestSource input pair 1)).1
  · simp [leftMember]
  · by_cases rightMember : resource ∈
        (uhligRecoveryPair (requestSource input pair 0)
          (requestSource input pair 1)).2
    · simp [leftMember, rightMember]
    · simp [leftMember, rightMember]

/-- Compose one supplied `pairs`-copy resource circuit after its explicit
Uhlig router. -/
noncomputable def routedResourceCircuit
    (pairs : Nat)
    (resource : Fin (prefixLast prefixWidth + 2))
    (resourceCircuit : Circuit DeMorgan.signature
      (pairs * suffixWidth) pairs) :
    Circuit DeMorgan.signature
      ((2 * pairs) * (prefixWidth + suffixWidth))
      pairs :=
  resourceCircuit.comp (resourceRouterArrayCircuit pairs resource)

@[simp] theorem routedResourceCircuit_size
    (pairs : Nat)
    (resource : Fin (prefixLast prefixWidth + 2))
    (resourceCircuit : Circuit DeMorgan.signature
      (pairs * suffixWidth) pairs) :
    (routedResourceCircuit pairs resource resourceCircuit).size =
      (Finset.univ.sum fun _pair : Fin pairs =>
          resourceRouterGateCount prefixWidth suffixWidth resource) +
        resourceCircuit.size := by
  simp [routedResourceCircuit]

theorem routedResourceCircuit_eval
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (pairs : Nat)
    (resource : Fin (prefixLast prefixWidth + 2))
    (resourceCircuit : Circuit DeMorgan.signature
      (pairs * suffixWidth) pairs)
    (computes : resourceCircuit.ComputesWith DeMorgan.interpretation
      (directProduct (resourceFunction function resource) pairs))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (pair : Fin pairs) :
    (routedResourceCircuit pairs resource resourceCircuit).eval
        DeMorgan.interpretation input pair =
      resourceValue function input pair resource := by
  rw [routedResourceCircuit, Circuit.eval_comp, computes]
  unfold directProduct resourceValue
  apply congrArg (resourceFunction function resource)
  funext bit
  exact resourceRouterArrayCircuit_eval pairs resource input pair bit

/-- Gate count of one routed supplied resource circuit. -/
@[reducible] noncomputable def routedResourceGateCount
    (prefixWidth suffixWidth pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resource : Fin (prefixLast prefixWidth + 2)) : Nat :=
  (Finset.univ.sum fun _pair : Fin pairs =>
      resourceRouterGateCount prefixWidth suffixWidth resource) +
    resourceGateCounts resource

/-- All Uhlig resources evaluated in parallel, in `(resource, pair)` order. -/
noncomputable def resourceBankCircuit
    (pairs : Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth) pairs) :
    Circuit DeMorgan.signature
      ((2 * pairs) * (prefixWidth + suffixWidth))
      ((prefixLast prefixWidth + 2) * pairs) :=
  Circuit.parallelFinVector (prefixLast prefixWidth + 2) pairs
    (fun resource => routedResourceCircuit pairs resource
      (resourceCircuits resource))

@[simp] theorem resourceBankCircuit_size
    (pairs : Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth) pairs) :
    (resourceBankCircuit pairs resourceCircuits).size =
      Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        routedResourceGateCount prefixWidth suffixWidth pairs
          (fun resource => (resourceCircuits resource).size) resource := by
  simp [resourceBankCircuit, routedResourceGateCount]

theorem resourceBankCircuit_eval
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (pairs : Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth) pairs)
    (computes : forall resource,
      (resourceCircuits resource).ComputesWith DeMorgan.interpretation
        (directProduct (resourceFunction function resource) pairs))
    (input : Fin ((2 * pairs) * (prefixWidth + suffixWidth)) -> Bool)
    (resource : Fin (prefixLast prefixWidth + 2))
    (pair : Fin pairs) :
    (resourceBankCircuit pairs resourceCircuits).eval
        DeMorgan.interpretation input (finProdFinEquiv (resource, pair)) =
      resourceValue function input pair resource := by
  rw [resourceBankCircuit, Circuit.eval_parallelFinVector]
  exact routedResourceCircuit_eval function pairs resource
    (resourceCircuits resource) (computes resource) input pair

@[simp] theorem resourceBankCircuit_cost
    (pairs : Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth) pairs) :
    (resourceBankCircuit pairs resourceCircuits).cost
        DeMorgan.standardCost =
      Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        ((Finset.univ.sum fun _pair : Fin pairs =>
            (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
              DeMorgan.standardCost) +
          (resourceCircuits resource).cost DeMorgan.standardCost) := by
  simp [resourceBankCircuit, routedResourceCircuit,
    resourceRouterArrayCircuit]

end UhligCircuit
end MassProduction
end Algebraic
