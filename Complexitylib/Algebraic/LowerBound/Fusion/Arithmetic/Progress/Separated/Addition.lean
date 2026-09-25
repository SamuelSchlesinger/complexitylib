/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Collision
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Finsupp.Fin

/-!
# Addition enrichment of coefficient-one monomials

This file develops the binomial half of the unit-separated enrichment proof.
After eliminating the last variable by `X left + X right`, a source monomial
expands as its prior-variable monomial times a binomial power.  A monomial of
coefficient one in that expansion must be one of the two endpoints: all
occurrences of the eliminated variable went left, or all went right.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Addition

noncomputable section

/-- Restrict an exponent vector to all coordinates before the last one. -/
def dropLast
    (exponent : Fin (variableCount + 1) →₀ ℕ) :
    Fin variableCount →₀ ℕ :=
  Finsupp.comapDomain Fin.castSucc exponent
    (Fin.castSucc_injective _).injOn

@[simp] theorem dropLast_apply
    (exponent : Fin (variableCount + 1) →₀ ℕ)
    (coordinate : Fin variableCount) :
    dropLast exponent coordinate = exponent coordinate.castSucc := by
  simp [dropLast, Finsupp.comapDomain_apply]

/-- Reverse substitution of the last variable by a sum. -/
def substitution
    (left right : Fin variableCount) :
    Fin (variableCount + 1) → MvPolynomial (Fin variableCount) ℕ :=
  Fin.lastCases
    (MvPolynomial.X left + MvPolynomial.X right)
    MvPolynomial.X

/-- Endpoint obtained by sending every occurrence of the eliminated variable
to `coordinate`. -/
def endpoint
    (coordinate : Fin variableCount)
    (source : Fin (variableCount + 1) →₀ ℕ) :
    Fin variableCount →₀ ℕ :=
  dropLast source +
    Finsupp.single coordinate (source (Fin.last variableCount))

/-- Exact binomial form of one source-monomial expansion. -/
theorem monomialExpansion_eq
    (left right : Fin variableCount)
    (exponent : Fin (variableCount + 1) →₀ ℕ) :
    Expansion.monomialExpansion (substitution left right) exponent =
      MvPolynomial.monomial (dropLast exponent) 1 *
        (MvPolynomial.X left + MvPolynomial.X right) ^
          exponent (Fin.last variableCount) := by
  rw [Expansion.monomialExpansion, MvPolynomial.bind₁_monomial]
  simp only [MvPolynomial.C_1, one_mul]
  change exponent.prod
      (fun coordinate power => substitution left right coordinate ^ power) = _
  rw [exponent.prod_fintype _ (fun _ => pow_zero _)]
  rw [Fin.prod_univ_castSucc]
  simp only [substitution, Fin.lastCases_castSucc, Fin.lastCases_last]
  congr 1
  calc
    (∏ coordinate : Fin variableCount,
        MvPolynomial.X coordinate ^ exponent coordinate.castSucc) =
        ∏ coordinate : Fin variableCount,
          MvPolynomial.X coordinate ^ dropLast exponent coordinate := by
      congr 1
    _ = (dropLast exponent).prod
          (fun coordinate power => MvPolynomial.X coordinate ^ power) := by
      symm
      exact (dropLast exponent).prod_fintype _ (fun _ => pow_zero _)
    _ = MvPolynomial.monomial (dropLast exponent) 1 :=
      MvPolynomial.prod_X_pow_eq_monomial

/-- Embed two distinct target coordinates as the two binary coordinates. -/
def pairEmbedding
    (left right : Fin variableCount)
    (distinct : left ≠ right) : Fin 2 ↪ Fin variableCount where
  toFun := Fin.cases left (fun _ => right)
  inj' := by
    intro first second equal
    fin_cases first <;> fin_cases second
    · rfl
    · exact (distinct equal).elim
    · exact (distinct equal.symm).elim
    · rfl

@[simp] theorem pairEmbedding_zero
    (left right : Fin variableCount)
    (distinct : left ≠ right) :
    pairEmbedding left right distinct 0 = left := rfl

@[simp] theorem pairEmbedding_one
    (left right : Fin variableCount)
    (distinct : left ≠ right) :
    pairEmbedding left right distinct 1 = right := rfl

/-- Rename the binary binomial power to any two distinct coordinates. -/
theorem rename_binary_add_pow
    (left right : Fin variableCount)
    (distinct : left ≠ right)
    (power : Nat) :
    MvPolynomial.rename (pairEmbedding left right distinct)
        ((MvPolynomial.X 0 + MvPolynomial.X 1 :
          MvPolynomial (Fin 2) ℕ) ^ power) =
      (MvPolynomial.X left + MvPolynomial.X right) ^ power := by
  simp only [map_pow, map_add, MvPolynomial.rename_X,
    pairEmbedding_zero, pairEmbedding_one]

/-- A coefficient-one monomial of a binomial power on distinct variables is
one of its two endpoints. -/
theorem coeff_add_pow_eq_one
    (left right : Fin variableCount)
    (distinct : left ≠ right)
    (power : Nat)
    (exponent : Fin variableCount →₀ ℕ)
    (coefficientOne : AddMonoidAlgebra.coeff ((MvPolynomial.X left + MvPolynomial.X right) ^ power :
        MvPolynomial (Fin variableCount) ℕ) exponent = 1) :
    exponent = Finsupp.single left power ∨
      exponent = Finsupp.single right power := by
  let embedding := pairEmbedding left right distinct
  let binary :=
    ((MvPolynomial.X 0 + MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℕ) ^ power)
  have renamedCoefficientNonzero :
      AddMonoidAlgebra.coeff (MvPolynomial.rename embedding binary) exponent ≠ 0 := by
    rw [show MvPolynomial.rename embedding binary =
        (MvPolynomial.X left + MvPolynomial.X right) ^ power by
      exact rename_binary_add_pow left right distinct power]
    omega
  obtain ⟨binaryExponent, mapped, binaryNonzero⟩ :=
    MvPolynomial.coeff_rename_ne_zero embedding binary exponent
      renamedCoefficientNonzero
  have binaryCoefficientOne :
      AddMonoidAlgebra.coeff binary binaryExponent = 1 := by
    have renamedCoefficient :=
      MvPolynomial.coeff_rename_mapDomain embedding embedding.injective
        binary binaryExponent
    rw [mapped] at renamedCoefficient
    rw [show MvPolynomial.rename embedding binary =
        (MvPolynomial.X left + MvPolynomial.X right) ^ power by
      exact rename_binary_add_pow left right distinct power]
      at renamedCoefficient
    exact renamedCoefficient.symm.trans coefficientOne
  change AddMonoidAlgebra.coeff ((MvPolynomial.X 0 + MvPolynomial.X 1 :
        MvPolynomial (Fin 2) ℕ) ^ power) binaryExponent = 1 at binaryCoefficientOne
  rw [MvPolynomial.coeff_add_pow] at binaryCoefficientOne
  split at binaryCoefficientOne
  next antidiagonal =>
    have endpoint := Nat.choose_eq_one_iff.mp binaryCoefficientOne
    rcases endpoint with leftZero | leftAll
    · right
      have rightAll : binaryExponent 1 = power := by
        rw [Finset.mem_antidiagonal] at antidiagonal
        omega
      have binaryExponentEqual :
          binaryExponent = Finsupp.single (1 : Fin 2) power := by
        ext coordinate
        fin_cases coordinate
        · simp [leftZero]
        · simp [rightAll]
      rw [← mapped, binaryExponentEqual, Finsupp.mapDomain_single]
      rfl
    · left
      have rightZero : binaryExponent 1 = 0 := by
        rw [Finset.mem_antidiagonal] at antidiagonal
        omega
      have binaryExponentEqual :
          binaryExponent = Finsupp.single (0 : Fin 2) power := by
        ext coordinate
        fin_cases coordinate
        · simp [leftAll]
        · simp [rightZero]
      rw [← mapped, binaryExponentEqual, Finsupp.mapDomain_single]
      rfl
  next outside =>
    simp at binaryCoefficientOne

/-- For distinct summands, a coefficient-one neighbor of a source monomial
is one of the two all-left/all-right expansion endpoints. -/
theorem coeff_monomialExpansion_eq_one
    (left right : Fin variableCount)
    (distinct : left ≠ right)
    (source : Fin (variableCount + 1) →₀ ℕ)
    (target : Fin variableCount →₀ ℕ)
    (coefficientOne : AddMonoidAlgebra.coeff (Expansion.monomialExpansion (substitution left right) source) target = 1) :
    target = endpoint left source ∨
      target = endpoint right source := by
  rw [monomialExpansion_eq,
    MvPolynomial.coeff_monomial_mul'] at coefficientOne
  split at coefficientOne
  next sourceLe =>
    simp only [one_mul] at coefficientOne
    rcases coeff_add_pow_eq_one left right distinct
        (source (Fin.last variableCount))
        (target - dropLast source) coefficientOne with endpoint | endpoint
    · left
      rw [← add_tsub_cancel_of_le sourceLe, endpoint]
      rfl
    · right
      rw [← add_tsub_cancel_of_le sourceLe, endpoint]
      rfl
  next sourceNotLe =>
    simp at coefficientOne

/-- The cross product of an all-left endpoint from `first` and an all-right
endpoint from `second` contains another endpoint from one of the sources. -/
theorem endpoint_le_cross
    (left right : Fin variableCount)
    (distinct : left ≠ right)
    (first second : Fin (variableCount + 1) →₀ ℕ) :
    endpoint left second ≤
        endpoint left first + endpoint right second ∨
      endpoint right first ≤
        endpoint left first + endpoint right second := by
  by_cases enoughLeft :
      second (Fin.last variableCount) ≤
        dropLast first left + first (Fin.last variableCount)
  all_goals simp only [dropLast_apply] at enoughLeft
  · left
    intro coordinate
    by_cases coordinateLeft : coordinate = left
    · subst coordinate
      simp [endpoint, distinct]
      omega
    · by_cases coordinateRight : coordinate = right
      · subst coordinate
        simp [endpoint, distinct.symm]
        omega
      · simp [endpoint, coordinateLeft, coordinateRight]
  · right
    intro coordinate
    by_cases coordinateLeft : coordinate = left
    · subst coordinate
      simp [endpoint, distinct]
      omega
    · by_cases coordinateRight : coordinate = right
      · subst coordinate
        simp [endpoint, distinct.symm]
        omega
      · simp [endpoint, coordinateLeft, coordinateRight]

/-- Two distinct selected endpoint pairs from two sources contradict
separation. -/
theorem not_isSeparated_of_endpoint_pairs
    (left right : Fin variableCount)
    (distinct : left ≠ right)
    {ambient selected : Finset (Fin variableCount →₀ ℕ)}
    (separated : IsSeparated ambient selected)
    (firstSource secondSource : Fin (variableCount + 1) →₀ ℕ)
    (firstLeft firstRight secondLeft secondRight : ↥selected)
    (firstLeftValue : firstLeft.1 = endpoint left firstSource)
    (firstRightValue : firstRight.1 = endpoint right firstSource)
    (secondLeftValue : secondLeft.1 = endpoint left secondSource)
    (secondRightValue : secondRight.1 = endpoint right secondSource)
    (firstDistinct : firstLeft ≠ firstRight)
    (secondDistinct : secondLeft ≠ secondRight)
    (sourcesDistinctLeft : firstLeft ≠ secondLeft)
    (sourcesDistinctRight : firstRight ≠ secondRight) : False := by
  rcases endpoint_le_cross left right distinct firstSource secondSource with
      secondLeftLe | firstRightLe
  · have containment : secondLeft.1 ≤ firstLeft.1 + secondRight.1 := by
      rw [secondLeftValue, firstLeftValue, secondRightValue]
      exact secondLeftLe
    have middlePresent : secondLeft.1 ∈ ambient :=
      separated.subset secondLeft.2
    rcases separated.2 firstLeft.1 firstLeft.2
        secondRight.1 secondRight.2 secondLeft.1 middlePresent containment with
      middleIsFirst | middleIsSecond
    · exact sourcesDistinctLeft (Subtype.ext middleIsFirst.symm)
    · exact secondDistinct (Subtype.ext middleIsSecond)
  · have containment : firstRight.1 ≤ firstLeft.1 + secondRight.1 := by
      rw [firstRightValue, firstLeftValue, secondRightValue]
      exact firstRightLe
    have middlePresent : firstRight.1 ∈ ambient :=
      separated.subset firstRight.2
    rcases separated.2 firstLeft.1 firstLeft.2
        secondRight.1 secondRight.2 firstRight.1 middlePresent containment with
      middleIsFirst | middleIsSecond
    · exact firstDistinct (Subtype.ext middleIsFirst.symm)
    · exact sourcesDistinctRight (Subtype.ext middleIsSecond)
/-- Repeating the same summand gives a singleton binomial-power support. -/
theorem support_add_self_pow
    (coordinate : Fin variableCount)
    (power : Nat) :
    ((MvPolynomial.X coordinate + MvPolynomial.X coordinate) ^ power :
      MvPolynomial (Fin variableCount) ℕ).support =
        {Finsupp.single coordinate power} := by
  induction power with
  | zero => simp
  | succ power inductionHypothesis =>
      rw [pow_succ, MonotonePolynomial.polynomial_support_mul,
        inductionHypothesis,
        MonotonePolynomial.polynomial_support_add,
        MvPolynomial.support_X]
      ext exponent
      constructor
      · intro present
        rw [Finset.mem_add] at present
        obtain ⟨prior, priorPresent, final, finalPresent, equal⟩ := present
        have priorEqual : prior = Finsupp.single coordinate power :=
          Finset.mem_singleton.mp priorPresent
        have finalEqual : final = Finsupp.single coordinate 1 := by
          simpa using finalPresent
        subst prior
        subst final
        rw [Finset.mem_singleton]
        rw [← equal]
        simp [← Finsupp.single_add]
      · rw [Finset.mem_singleton]
        intro exponentEqual
        subst exponent
        rw [Finset.mem_add]
        exact ⟨Finsupp.single coordinate power,
          Finset.mem_singleton_self _,
          Finsupp.single coordinate 1, by simp,
          by simp [← Finsupp.single_add]⟩

/-- When both addition inputs are the same, every source monomial has one
expansion neighbor. -/
theorem support_monomialExpansion_same
    (coordinate : Fin variableCount)
    (source : Fin (variableCount + 1) →₀ ℕ) :
    (Expansion.monomialExpansion
      (substitution coordinate coordinate) source).support =
        {endpoint coordinate source} := by
  rw [monomialExpansion_eq,
    MonotonePolynomial.polynomial_support_mul,
    MvPolynomial.support_monomial,
    ite_eq_right (one_ne_zero : (1 : Nat) ≠ 0),
    support_add_self_pow]
  ext exponent
  constructor
  · intro present
    rw [Finset.mem_add] at present
    obtain ⟨base, basePresent, endpoint, endpointPresent, equal⟩ := present
    rw [Finset.mem_singleton] at basePresent endpointPresent ⊢
    subst base
    subst endpoint
    exact equal.symm
  · rw [Finset.mem_singleton]
    intro equal
    subst exponent
    rw [Finset.mem_add]
    exact ⟨dropLast source, Finset.mem_singleton_self _,
      Finsupp.single coordinate (source (Fin.last variableCount)),
      Finset.mem_singleton_self _, rfl⟩

/-- A coefficient-one neighbor in the repeated-input case is the unique
endpoint. -/
theorem coeff_monomialExpansion_eq_one_same
    (coordinate : Fin variableCount)
    (source : Fin (variableCount + 1) →₀ ℕ)
    (target : Fin variableCount →₀ ℕ)
    (coefficientOne : AddMonoidAlgebra.coeff (Expansion.monomialExpansion
        (substitution coordinate coordinate) source) target = 1) :
    target = endpoint coordinate source := by
  have present : target ∈
      (Expansion.monomialExpansion
        (substitution coordinate coordinate) source).support :=
    MvPolynomial.mem_support_iff.mpr (by omega)
  rw [support_monomialExpansion_same] at present
  exact Finset.mem_singleton.mp present

private theorem third_eq_first_or_second_of_endpoints
    {Value : Type*}
    {left right first second third : Value}
    (firstEndpoint : first = left ∨ first = right)
    (secondEndpoint : second = left ∨ second = right)
    (thirdEndpoint : third = left ∨ third = right)
    (distinct : first ≠ second) :
    third = first ∨ third = second := by
  rcases firstEndpoint with rfl | rfl <;>
    rcases secondEndpoint with rfl | rfl <;>
    rcases thirdEndpoint with rfl | rfl <;> aesop

private theorem orient_distinct_endpoints
    {Value : Type*}
    {left right first second : Value}
    (firstEndpoint : first = left ∨ first = right)
    (secondEndpoint : second = left ∨ second = right)
    (distinct : first ≠ second) :
    (first = left ∧ second = right) ∨
      (second = left ∧ first = right) := by
  rcases firstEndpoint with rfl | rfl <;>
    rcases secondEndpoint with rfl | rfl <;> aesop

/-- Reverse substitution by an addition loses at most one unit-separated
monomial.  Coefficient-one targets have rigid source origins; each origin has
at most two endpoint targets, and separation allows at most one such
two-element fiber. -/
theorem pullback
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (left right : Fin variableCount) :
    Unit.Pullback polynomial
      (MvPolynomial.bind₁ (substitution left right) polynomial) 1 := by
  classical
  constructor
  intro selected separated
  let origin : ↥selected → Fin (variableCount + 1) →₀ ℕ := fun target =>
    Classical.choose
      (Expansion.exists_unique_source_of_coeff_eq_one
        (substitution left right) polynomial target.1
        (separated.2 target.1 target.2))
  have originSpec : ∀ target,
      origin target ∈ polynomial.support ∧
        AddMonoidAlgebra.coeff polynomial (origin target) = 1 ∧
          AddMonoidAlgebra.coeff (Expansion.monomialExpansion (substitution left right)
                (origin target)) target.1 = 1 ∧
            Expansion.IsNeighbor (substitution left right)
                (origin target) target.1 ∧
              ∀ other ∈ polynomial.support,
                Expansion.IsNeighbor (substitution left right)
                    other target.1 →
                  other = origin target := by
    intro target
    exact Classical.choose_spec
      (Expansion.exists_unique_source_of_coeff_eq_one
        (substitution left right) polynomial target.1
        (separated.2 target.1 target.2))
  have score : selected.card - 1 ≤
      (selected.attach.image origin).card - 1 + 1 := by
    by_cases distinct : left ≠ right
    · have targetEndpoint : ∀ target : ↥selected,
          target.1 = endpoint left (origin target) ∨
            target.1 = endpoint right (origin target) := by
        intro target
        exact coeff_monomialExpansion_eq_one left right distinct
          (origin target) target.1 (originSpec target).2.2.1
      have fiberPair : ∀ {first second other : ↥selected},
          first ≠ second →
            origin first = origin second →
              origin other = origin first →
                other = first ∨ other = second := by
        intro first second other firstDistinct sameOrigin otherOrigin
        have firstEndpoint := targetEndpoint first
        have secondEndpoint := targetEndpoint second
        have otherEndpoint := targetEndpoint other
        rw [← sameOrigin] at secondEndpoint
        rw [otherOrigin] at otherEndpoint
        rcases third_eq_first_or_second_of_endpoints
            firstEndpoint secondEndpoint otherEndpoint
            (fun equal => firstDistinct (Subtype.ext equal)) with
          equal | equal
        · exact Or.inl (Subtype.ext equal)
        · exact Or.inr (Subtype.ext equal)
      have collisionsSame : ∀
          {first second third fourth : ↥selected},
          first ≠ second →
            origin first = origin second →
              third ≠ fourth →
                origin third = origin fourth →
                  origin third = origin first := by
        intro first second third fourth firstDistinct firstSame
          thirdDistinct thirdSame
        by_contra originsDifferent
        have firstEndpoint := targetEndpoint first
        have secondEndpoint := targetEndpoint second
        have thirdEndpoint := targetEndpoint third
        have fourthEndpoint := targetEndpoint fourth
        rw [← firstSame] at secondEndpoint
        rw [← thirdSame] at fourthEndpoint
        have crossDistinct : ∀ {firstTarget secondTarget : ↥selected},
            origin firstTarget = origin first →
              origin secondTarget = origin third →
                firstTarget ≠ secondTarget := by
          intro firstTarget secondTarget firstOrigin secondOrigin equal
          apply originsDifferent
          exact secondOrigin.symm.trans
            ((congrArg origin equal.symm).trans firstOrigin)
        rcases orient_distinct_endpoints firstEndpoint secondEndpoint
            (fun equal => firstDistinct (Subtype.ext equal)) with
          firstOrder | firstOrder <;>
          rcases orient_distinct_endpoints thirdEndpoint fourthEndpoint
              (fun equal => thirdDistinct (Subtype.ext equal)) with
            thirdOrder | thirdOrder
        · exact not_isSeparated_of_endpoint_pairs left right distinct
            separated.1 (origin first) (origin third)
            first second third fourth
            firstOrder.1 firstOrder.2 thirdOrder.1 thirdOrder.2
            firstDistinct thirdDistinct
            (crossDistinct rfl rfl)
            (crossDistinct firstSame.symm thirdSame.symm)
        · exact not_isSeparated_of_endpoint_pairs left right distinct
            separated.1 (origin first) (origin third)
            first second fourth third
            firstOrder.1 firstOrder.2 thirdOrder.1 thirdOrder.2
            firstDistinct thirdDistinct.symm
            (crossDistinct rfl thirdSame.symm)
            (crossDistinct firstSame.symm rfl)
        · exact not_isSeparated_of_endpoint_pairs left right distinct
            separated.1 (origin first) (origin third)
            second first third fourth
            firstOrder.1 firstOrder.2 thirdOrder.1 thirdOrder.2
            firstDistinct.symm thirdDistinct
            (crossDistinct firstSame.symm rfl)
            (crossDistinct rfl thirdSame.symm)
        · exact not_isSeparated_of_endpoint_pairs left right distinct
            separated.1 (origin first) (origin third)
            second first fourth third
            firstOrder.1 firstOrder.2 thirdOrder.1 thirdOrder.2
            firstDistinct.symm thirdDistinct.symm
            (crossDistinct firstSame.symm thirdSame.symm)
            (crossDistinct rfl rfl)
      have counted := Collision.card_sub_one_le_image
        origin fiberPair collisionsSame
      simpa using counted
    · have equal : left = right := not_ne_iff.mp distinct
      subst right
      have originInjective : Function.Injective origin := by
        intro first second originsEqual
        have firstNeighbor := (originSpec first).2.2.2.1
        have secondNeighbor : Expansion.IsNeighbor
            (substitution left left) (origin first) second.1 := by
          rw [originsEqual]
          exact (originSpec second).2.2.2.1
        change first.1 ∈
            (Expansion.monomialExpansion (substitution left left)
              (origin first)).support at firstNeighbor
        change second.1 ∈
            (Expansion.monomialExpansion (substitution left left)
              (origin first)).support at secondNeighbor
        rw [support_monomialExpansion_same] at firstNeighbor secondNeighbor
        exact Subtype.ext
          ((Finset.mem_singleton.mp firstNeighbor).trans
            (Finset.mem_singleton.mp secondNeighbor).symm)
      rw [Finset.card_image_of_injective _ originInjective,
        Finset.card_attach]
      omega
  let selection : Expansion.OriginSelection
      (substitution left right) polynomial selected 1 := {
    origin := origin
    origin_mem := fun target => (originSpec target).1
    neighbor := fun target => (originSpec target).2.2.2.1
    rigid := fun target other otherPresent otherNeighbor =>
      (originSpec target).2.2.2.2 other otherPresent otherNeighbor
    score := score }
  refine ⟨selected.attach.image origin, ?_, selection.score⟩
  constructor
  · exact selection.prior_isSeparated separated.1
  · intro source sourcePresent
    obtain ⟨target, _, sourceEqual⟩ := Finset.mem_image.mp sourcePresent
    rw [← sourceEqual]
    exact (originSpec target).2.1

/-- The fully discharged addition-pullback package for the coefficient-one
separation measure. -/
theorem additionPullbacks : Unit.AdditionPullbacks where
  add := by
    intro variableCount polynomial left right
    change Unit.Pullback polynomial
      (MvPolynomial.bind₁ (substitution left right) polynomial) 1
    exact pullback polynomial left right

/-- Coefficient-one separation is an unconditional progress measure for
constant-free monotone arithmetic addition cost. -/
def measure : Progress.Measure
    (Algebraic.Arithmetic.additionCost (K := PEmpty)) :=
  Unit.measure additionPullbacks

/-- Every constant-free monotone arithmetic circuit pays at least the
coefficient-one separation number of its output polynomial in addition
gates. -/
theorem circuit_addition_lowerBound
    (target : MvPolynomial (Fin n) ℕ)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (polynomialInterpretation (Fin n))) :
    Unit.separationNumber target ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := PEmpty)) :=
  measure.circuit_lowerBound target circuit constructs

/-- If the full target support is separated and all of its coefficients are
one, every target monomial except one must be paid for by an addition gate. -/
theorem circuit_addition_lowerBound_of_unitSeparated
    (target : MvPolynomial (Fin n) ℕ)
    (targetSeparated : IsSeparated target.support target.support)
    (coefficientsOne : ∀ exponent ∈ target.support,
      AddMonoidAlgebra.coeff target exponent = 1)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (polynomialInterpretation (Fin n))) :
    target.support.card - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := PEmpty)) :=
  (Unit.candidate_card_sub_one_le ⟨targetSeparated, coefficientsOne⟩).trans
    (circuit_addition_lowerBound target circuit constructs)

end
end Addition
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
