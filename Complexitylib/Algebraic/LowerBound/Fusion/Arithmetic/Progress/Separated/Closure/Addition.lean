/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Addition
public import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# Additive enrichment for Schnorr's substitution closure

After an arbitrary monomial substitution, eliminating a gate variable by a
sum replaces its monomial image by the sum of two monomials.  A source
monomial with last-variable degree `k` consequently has neighbors indexed by
splits `a + b = k`.

The key shift argument is Schnorr's original one.  Fix a selected neighbor
outside the all-left endpoint support.  Any selected neighbor outside the
all-right endpoint support must equal the monomial obtained by shifting one
occurrence from right to left in the fixed neighbor.  Hence the selected set
loses at most one element on restriction to an endpoint support.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Closure
namespace Addition

noncomputable section

/-- Exponent contributed by all source coordinates before the eliminated
last variable. -/
def baseExponent
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (source : Fin (variableCount + 1) →₀ ℕ) : ℕ →₀ ℕ :=
  MonomialSubstitution.exponentMap basis
    (Separated.Addition.dropLast source)

/-- Substitute the last source variable by the sum of two coefficient-one
monomials and all prior variables according to `basis`. -/
def substitution
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : ℕ →₀ ℕ) :
    Fin (variableCount + 1) → MvPolynomial ℕ ℕ :=
  Fin.lastCases
    (MvPolynomial.monomial left 1 + MvPolynomial.monomial right 1)
    (MonomialSubstitution.substitution basis)

/-- Endpoint monomial substitution sending every eliminated occurrence to
`endpoint`. -/
def endpointBasis
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (endpoint : ℕ →₀ ℕ) :
    Fin (variableCount + 1) → ℕ →₀ ℕ :=
  Fin.lastCases endpoint basis

/-- Binary basis whose two variables denote the two endpoint monomials. -/
def binaryBasis
    (left right : ℕ →₀ ℕ) : Fin 2 → ℕ →₀ ℕ :=
  Fin.cases left (fun _ => right)

@[simp] theorem binaryBasis_zero
    (left right : ℕ →₀ ℕ) :
    binaryBasis left right 0 = left := rfl

@[simp] theorem binaryBasis_one
    (left right : ℕ →₀ ℕ) :
    binaryBasis left right 1 = right := rfl

/-- The induced binary exponent map is the expected linear combination of
the two endpoint exponents. -/
theorem binaryExponentMap_eq
    (left right : ℕ →₀ ℕ)
    (exponent : Fin 2 →₀ ℕ) :
    MonomialSubstitution.exponentMap (binaryBasis left right) exponent =
      exponent 0 • left + exponent 1 • right := by
  rw [MonomialSubstitution.exponentMap,
    Finsupp.linearCombination_apply]
  rw [exponent.sum_fintype
    (fun coordinate power => power • binaryBasis left right coordinate)
    (fun _ => zero_nsmul _)]
  simp [Fin.sum_univ_two]

/-- Substituting the binary basis into a binary power gives the power of the
two endpoint monomials. -/
theorem transform_binary_add_pow
    (left right : ℕ →₀ ℕ)
    (power : Nat) :
    transform (binaryBasis left right)
        ((MvPolynomial.X 0 + MvPolynomial.X 1 :
          MvPolynomial (Fin 2) ℕ) ^ power) =
      (MvPolynomial.monomial left 1 +
        MvPolynomial.monomial right 1) ^ power := by
  simp [transform, MonomialSubstitution.substitution, map_add, map_pow]

/-- Every monomial in a power of two coefficient-one monomials comes from a
split of the power between them. -/
theorem exists_split_of_mem_support_add_pow
    (left right target : ℕ →₀ ℕ)
    (power : Nat)
    (present : target ∈
      ((MvPolynomial.monomial left 1 +
        MvPolynomial.monomial right 1) ^ power :
          MvPolynomial ℕ ℕ).support) :
    ∃ leftPower rightPower,
      leftPower + rightPower = power ∧
        target = leftPower • left + rightPower • right := by
  rw [← transform_binary_add_pow, support_transform,
    Finset.mem_image] at present
  obtain ⟨binaryExponent, binaryPresent, targetEqual⟩ := present
  have antidiagonal :
      binaryExponent 0 + binaryExponent 1 = power := by
    rw [MvPolynomial.mem_support_iff,
      MvPolynomial.coeff_add_pow] at binaryPresent
    split at binaryPresent
    next inside => exact Finset.mem_antidiagonal.mp inside
    next outside => simp at binaryPresent
  exact ⟨binaryExponent 0, binaryExponent 1, antidiagonal,
    targetEqual.symm.trans
      (binaryExponentMap_eq left right binaryExponent)⟩

/-- Every numerical split of a binary power contributes its corresponding
monomial to the support. -/
theorem split_mem_support_add_pow
    (left right : ℕ →₀ ℕ)
    {leftPower rightPower power : Nat}
    (sumPower : leftPower + rightPower = power) :
    leftPower • left + rightPower • right ∈
      ((MvPolynomial.monomial left 1 +
        MvPolynomial.monomial right 1) ^ power :
          MvPolynomial ℕ ℕ).support := by
  let binaryExponent : Fin 2 →₀ ℕ :=
    Finsupp.single 0 leftPower + Finsupp.single 1 rightPower
  have binaryZero : binaryExponent 0 = leftPower := by
    simp [binaryExponent]
  have binaryOne : binaryExponent 1 = rightPower := by
    simp [binaryExponent]
  have binaryPresent : binaryExponent ∈
      ((MvPolynomial.X 0 + MvPolynomial.X 1 :
        MvPolynomial (Fin 2) ℕ) ^ power).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add_pow]
    rw [ite_eq_left (Finset.mem_antidiagonal.mpr (by
      simpa [binaryZero, binaryOne] using sumPower))]
    exact Nat.choose_ne_zero (by omega)
  rw [← transform_binary_add_pow, support_transform,
    Finset.mem_image]
  refine ⟨binaryExponent, binaryPresent, ?_⟩
  rw [binaryExponentMap_eq, binaryZero, binaryOne]

/-- Exact binomial form of one source-monomial expansion under a sum of two
monomials. -/
theorem monomialExpansion_eq
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : ℕ →₀ ℕ)
    (source : Fin (variableCount + 1) →₀ ℕ) :
    Expansion.monomialExpansion (substitution basis left right) source =
      MvPolynomial.monomial (baseExponent basis source) 1 *
        (MvPolynomial.monomial left 1 +
          MvPolynomial.monomial right 1) ^
            source (Fin.last variableCount) := by
  rw [Expansion.monomialExpansion, MvPolynomial.bind₁_monomial]
  simp only [MvPolynomial.C_1, one_mul]
  change source.prod
      (fun coordinate power => substitution basis left right coordinate ^ power) = _
  rw [source.prod_fintype _ (fun _ => pow_zero _)]
  rw [Fin.prod_univ_castSucc]
  simp only [substitution, Fin.lastCases_castSucc, Fin.lastCases_last]
  congr 1
  have priorExpansion :=
    MonomialSubstitution.monomialExpansion_eq basis
      (Separated.Addition.dropLast source)
  rw [Expansion.monomialExpansion, MvPolynomial.bind₁_monomial] at priorExpansion
  simp only [MvPolynomial.C_1, one_mul,
    MonomialSubstitution.substitution] at priorExpansion
  calc
    (∏ coordinate : Fin variableCount,
        MvPolynomial.monomial (basis coordinate) 1 ^
          source coordinate.castSucc) =
        ∏ coordinate : Fin variableCount,
          MvPolynomial.monomial (basis coordinate) 1 ^
            Separated.Addition.dropLast source coordinate := by
      congr 1
    _ = (Separated.Addition.dropLast source).prod
          (fun coordinate power =>
            MvPolynomial.monomial (basis coordinate) 1 ^ power) := by
      symm
      exact (Separated.Addition.dropLast source).prod_fintype _
        (fun _ => pow_zero _)
    _ = MvPolynomial.monomial (baseExponent basis source) 1 := by
      change (∏ coordinate ∈
          (Separated.Addition.dropLast source).support,
          MvPolynomial.monomial (basis coordinate) 1 ^
            Separated.Addition.dropLast source coordinate) = _
      simpa only [baseExponent,
        Separated.Addition.dropLast_apply] using priorExpansion

/-- Every neighbor of a source monomial has a split representation. -/
theorem exists_split_of_neighbor
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : ℕ →₀ ℕ)
    (source : Fin (variableCount + 1) →₀ ℕ)
    (target : ℕ →₀ ℕ)
    (neighbor : Expansion.IsNeighbor
      (substitution basis left right) source target) :
    ∃ leftPower rightPower,
      leftPower + rightPower = source (Fin.last variableCount) ∧
        target = baseExponent basis source +
          (leftPower • left + rightPower • right) := by
  rw [Expansion.IsNeighbor, monomialExpansion_eq,
    MonotonePolynomial.polynomial_support_mul,
    MvPolynomial.support_monomial,
    ite_eq_right (one_ne_zero : (1 : ℕ) ≠ 0),
    Finset.mem_add] at neighbor
  obtain ⟨base, basePresent, split, splitPresent, targetEqual⟩ := neighbor
  have baseEqual : base = baseExponent basis source :=
    Finset.mem_singleton.mp basePresent
  subst base
  obtain ⟨leftPower, rightPower, sumPower, splitEqual⟩ :=
    exists_split_of_mem_support_add_pow left right split
      (source (Fin.last variableCount)) splitPresent
  subst split
  exact ⟨leftPower, rightPower, sumPower, targetEqual.symm⟩

/-- Every split representation is an actual expansion neighbor. -/
theorem neighbor_of_split
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : ℕ →₀ ℕ)
    (source : Fin (variableCount + 1) →₀ ℕ)
    {leftPower rightPower : Nat}
    (sumPower : leftPower + rightPower =
      source (Fin.last variableCount)) :
    Expansion.IsNeighbor (substitution basis left right) source
      (baseExponent basis source +
        (leftPower • left + rightPower • right)) := by
  rw [Expansion.IsNeighbor, monomialExpansion_eq,
    MonotonePolynomial.polynomial_support_mul,
    MvPolynomial.support_monomial,
    ite_eq_right (one_ne_zero : (1 : ℕ) ≠ 0),
    Finset.mem_add]
  exact ⟨baseExponent basis source, Finset.mem_singleton_self _,
    leftPower • left + rightPower • right,
    split_mem_support_add_pow left right sumPower, rfl⟩

/-- The exponent map of an endpoint substitution is the prior contribution
plus the last-variable degree times the endpoint exponent. -/
theorem endpointExponentMap_eq
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (endpoint : ℕ →₀ ℕ)
    (source : Fin (variableCount + 1) →₀ ℕ) :
    MonomialSubstitution.exponentMap (endpointBasis basis endpoint) source =
      baseExponent basis source +
        source (Fin.last variableCount) • endpoint := by
  ext coordinate
  simp [MonomialSubstitution.exponentMap,
    Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    Fin.sum_univ_castSucc, endpointBasis, baseExponent,
    Separated.Addition.dropLast_apply]

/-- The all-left endpoint support is contained in the enriched support. -/
theorem leftEndpoint_support_subset
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ) :
    (transform (endpointBasis basis left) polynomial).support ⊆
      (MvPolynomial.bind₁ (substitution basis left right) polynomial).support := by
  intro target targetPresent
  rw [support_transform, Finset.mem_image] at targetPresent
  obtain ⟨source, sourcePresent, targetEqual⟩ := targetPresent
  rw [← targetEqual, endpointExponentMap_eq]
  apply Expansion.mem_support_bind₁_of_neighbor
    (substitution basis left right) polynomial source sourcePresent
  simpa using neighbor_of_split basis left right source
    (leftPower := source (Fin.last variableCount))
    (rightPower := 0) (Nat.add_zero _)

/-- The all-right endpoint support is contained in the enriched support. -/
theorem rightEndpoint_support_subset
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ) :
    (transform (endpointBasis basis right) polynomial).support ⊆
      (MvPolynomial.bind₁ (substitution basis left right) polynomial).support := by
  intro target targetPresent
  rw [support_transform, Finset.mem_image] at targetPresent
  obtain ⟨source, sourcePresent, targetEqual⟩ := targetPresent
  rw [← targetEqual, endpointExponentMap_eq]
  apply Expansion.mem_support_bind₁_of_neighbor
    (substitution basis left right) polynomial source sourcePresent
  simpa using neighbor_of_split basis left right source
    (leftPower := 0)
    (rightPower := source (Fin.last variableCount)) (Nat.zero_add _)

/-- Restricting a separated set to a smaller ambient support preserves
separatedness. -/
theorem IsSeparated.inter_of_subset
    [DecidableEq Variable]
    {ambient smaller selected : Finset (Variable →₀ ℕ)}
    (separated : IsSeparated ambient selected)
    (smallerSubset : smaller ⊆ ambient) :
    IsSeparated smaller (selected ∩ smaller) := by
  constructor
  · exact Finset.inter_subset_right
  · intro left leftPresent right rightPresent middle middlePresent middleLe
    exact separated.2 left (Finset.mem_inter.mp leftPresent).1
      right (Finset.mem_inter.mp rightPresent).1 middle
      (smallerSubset middlePresent) middleLe

/-- Shift one eliminated-variable occurrence from the right monomial to the
left monomial. -/
def shiftLeft
    (base left right : ℕ →₀ ℕ)
    (leftPower rightPower : Nat) : ℕ →₀ ℕ :=
  base + ((leftPower + 1) • left + (rightPower - 1) • right)

/-- Shift one eliminated-variable occurrence from the left monomial to the
right monomial. -/
def shiftRight
    (base left right : ℕ →₀ ℕ)
    (leftPower rightPower : Nat) : ℕ →₀ ℕ :=
  base + ((leftPower - 1) • left + (rightPower + 1) • right)

/-- Opposite one-step shifts preserve the product exponent of the original
two monomials. -/
theorem shiftLeft_add_shiftRight
    (firstBase secondBase left right : ℕ →₀ ℕ)
    (firstLeft firstRight secondLeft secondRight : Nat)
    (firstRightPositive : 0 < firstRight)
    (secondLeftPositive : 0 < secondLeft) :
    shiftLeft firstBase left right firstLeft firstRight +
        shiftRight secondBase left right secondLeft secondRight =
      (firstBase + (firstLeft • left + firstRight • right)) +
        (secondBase + (secondLeft • left + secondRight • right)) := by
  obtain ⟨firstRight, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt firstRightPositive)
  obtain ⟨secondLeft, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt secondLeftPositive)
  simp [shiftLeft, shiftRight, add_nsmul]
  abel

/-- The left shift divides the product of the two original monomials. -/
theorem shiftLeft_le_add
    (firstBase secondBase left right : ℕ →₀ ℕ)
    (firstLeft firstRight secondLeft secondRight : Nat)
    (firstRightPositive : 0 < firstRight)
    (secondLeftPositive : 0 < secondLeft) :
    shiftLeft firstBase left right firstLeft firstRight ≤
      (firstBase + (firstLeft • left + firstRight • right)) +
        (secondBase + (secondLeft • left + secondRight • right)) := by
  intro coordinate
  have equalityAt := congrArg (fun exponent : ℕ →₀ ℕ => exponent coordinate)
    (shiftLeft_add_shiftRight firstBase secondBase left right
      firstLeft firstRight secondLeft secondRight
      firstRightPositive secondLeftPositive)
  rw [← equalityAt]
  simp only [Finsupp.add_apply]
  exact Nat.le_add_right _ _

/-- If a nontrivial left shift does not change a monomial, then that monomial
was already its all-left endpoint. -/
theorem leftEndpoint_eq_of_shiftLeft_eq
    (base left right : ℕ →₀ ℕ)
    (leftPower rightPower totalPower : Nat)
    (rightPositive : 0 < rightPower)
    (sumPower : leftPower + rightPower = totalPower)
    (shiftEqual : shiftLeft base left right leftPower rightPower =
      base + (leftPower • left + rightPower • right)) :
    base + totalPower • left =
      base + (leftPower • left + rightPower • right) := by
  obtain ⟨priorRight, rightEqual⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt rightPositive)
  subst rightPower
  have endpointsEqual : left = right := by
    let common := base + (leftPower • left + priorRight • right)
    apply add_left_cancel (a := common)
    calc
      common + left =
          shiftLeft base left right leftPower (priorRight + 1) := by
        simp [common, shiftLeft, add_nsmul]
        abel
      _ = base +
          (leftPower • left + (priorRight + 1) • right) := shiftEqual
      _ = common + right := by
        simp [common, add_nsmul]
        abel
  subst right
  rw [← sumPower, add_nsmul]

/-- A representation outside the all-left endpoint support uses the right
summand at least once. -/
theorem rightPower_pos_of_not_mem_leftEndpoint
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (source : Fin (variableCount + 1) →₀ ℕ)
    (sourcePresent : source ∈ polynomial.support)
    (target : ℕ →₀ ℕ)
    (leftPower rightPower : Nat)
    (sumPower : leftPower + rightPower =
      source (Fin.last variableCount))
    (targetEqual : target = baseExponent basis source +
      (leftPower • left + rightPower • right))
    (notLeftEndpoint : target ∉
      (transform (endpointBasis basis left) polynomial).support) :
    0 < rightPower := by
  by_contra notPositive
  have rightZero : rightPower = 0 := Nat.eq_zero_of_not_pos notPositive
  have leftAll : leftPower = source (Fin.last variableCount) := by
    omega
  apply notLeftEndpoint
  rw [support_transform, Finset.mem_image]
  refine ⟨source, sourcePresent, ?_⟩
  rw [endpointExponentMap_eq, targetEqual, rightZero, leftAll]
  simp

/-- A representation outside the all-right endpoint support uses the left
summand at least once. -/
theorem leftPower_pos_of_not_mem_rightEndpoint
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (source : Fin (variableCount + 1) →₀ ℕ)
    (sourcePresent : source ∈ polynomial.support)
    (target : ℕ →₀ ℕ)
    (leftPower rightPower : Nat)
    (sumPower : leftPower + rightPower =
      source (Fin.last variableCount))
    (targetEqual : target = baseExponent basis source +
      (leftPower • left + rightPower • right))
    (notRightEndpoint : target ∉
      (transform (endpointBasis basis right) polynomial).support) :
    0 < leftPower := by
  by_contra notPositive
  have leftZero : leftPower = 0 := Nat.eq_zero_of_not_pos notPositive
  have rightAll : rightPower = source (Fin.last variableCount) := by
    omega
  apply notRightEndpoint
  rw [support_transform, Finset.mem_image]
  refine ⟨source, sourcePresent, ?_⟩
  rw [endpointExponentMap_eq, targetEqual, leftZero, rightAll]
  simp

/-- Schnorr's shift lemma: relative to one selected monomial outside the
all-left endpoint support, every selected monomial outside the all-right
endpoint support is the same fixed left shift. -/
theorem eq_shiftLeft_of_not_mem_endpoints
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    {selected : Finset (ℕ →₀ ℕ)}
    (separated : IsSeparated
      (MvPolynomial.bind₁ (substitution basis left right) polynomial).support
      selected)
    (fixed : ℕ →₀ ℕ)
    (fixedSelected : fixed ∈ selected)
    (fixedNotLeft : fixed ∉
      (transform (endpointBasis basis left) polynomial).support)
    (fixedSource : Fin (variableCount + 1) →₀ ℕ)
    (fixedSourcePresent : fixedSource ∈ polynomial.support)
    (fixedLeft fixedRight : Nat)
    (fixedSum : fixedLeft + fixedRight =
      fixedSource (Fin.last variableCount))
    (fixedEqual : fixed = baseExponent basis fixedSource +
      (fixedLeft • left + fixedRight • right))
    (other : ℕ →₀ ℕ)
    (otherSelected : other ∈ selected)
    (otherNotRight : other ∉
      (transform (endpointBasis basis right) polynomial).support) :
    other = shiftLeft (baseExponent basis fixedSource) left right
      fixedLeft fixedRight := by
  have fixedRightPositive :=
    rightPower_pos_of_not_mem_leftEndpoint basis left right polynomial
      fixedSource fixedSourcePresent fixed fixedLeft fixedRight fixedSum
      fixedEqual fixedNotLeft
  have otherAmbient : other ∈
      (MvPolynomial.bind₁
        (substitution basis left right) polynomial).support :=
    separated.subset otherSelected
  obtain ⟨otherSource, otherSourcePresent, otherNeighbor⟩ :=
    Expansion.exists_source_of_mem_support_bind₁
      (substitution basis left right) polynomial other otherAmbient
  obtain ⟨otherLeft, otherRight, otherSum, otherEqual⟩ :=
    exists_split_of_neighbor basis left right otherSource other otherNeighbor
  have otherLeftPositive :=
    leftPower_pos_of_not_mem_rightEndpoint basis left right polynomial
      otherSource otherSourcePresent other otherLeft otherRight otherSum
      otherEqual otherNotRight
  have shiftedSum : fixedLeft + 1 + (fixedRight - 1) =
      fixedSource (Fin.last variableCount) := by
    omega
  have shiftedNeighbor := neighbor_of_split basis left right fixedSource
    (leftPower := fixedLeft + 1) (rightPower := fixedRight - 1)
    shiftedSum
  have shiftedAmbient :
      shiftLeft (baseExponent basis fixedSource) left right
          fixedLeft fixedRight ∈
        (MvPolynomial.bind₁
          (substitution basis left right) polynomial).support := by
    apply Expansion.mem_support_bind₁_of_neighbor
      (substitution basis left right) polynomial fixedSource
      fixedSourcePresent
    simpa [shiftLeft] using shiftedNeighbor
  have shiftedLe :
      shiftLeft (baseExponent basis fixedSource) left right
          fixedLeft fixedRight ≤ fixed + other := by
    rw [fixedEqual, otherEqual]
    exact shiftLeft_le_add
      (baseExponent basis fixedSource)
      (baseExponent basis otherSource) left right
      fixedLeft fixedRight otherLeft otherRight
      fixedRightPositive otherLeftPositive
  rcases separated.2 fixed fixedSelected other otherSelected
      (shiftLeft (baseExponent basis fixedSource) left right
        fixedLeft fixedRight) shiftedAmbient shiftedLe with
    shiftedFixed | shiftedOther
  · exfalso
    apply fixedNotLeft
    rw [support_transform, Finset.mem_image]
    refine ⟨fixedSource, fixedSourcePresent, ?_⟩
    rw [endpointExponentMap_eq]
    have endpointEqual := leftEndpoint_eq_of_shiftLeft_eq
      (baseExponent basis fixedSource) left right
      fixedLeft fixedRight (fixedSource (Fin.last variableCount))
      fixedRightPositive fixedSum
      (shiftedFixed.trans fixedEqual)
    exact endpointEqual.trans fixedEqual.symm
  · exact shiftedOther.symm

/-- Once a selected monomial lies outside the left endpoint support, the
selected complement of the right endpoint support is subsingleton. -/
theorem outside_right_subsingleton_of_not_subset_left
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    {selected : Finset (ℕ →₀ ℕ)}
    (separated : IsSeparated
      (MvPolynomial.bind₁ (substitution basis left right) polynomial).support
      selected)
    (notSubsetLeft : ¬ selected ⊆
      (transform (endpointBasis basis left) polynomial).support) :
    (selected \ (transform
      (endpointBasis basis right) polynomial).support).card ≤ 1 := by
  obtain ⟨fixed, fixedSelected, fixedNotLeft⟩ :=
    Finset.not_subset.mp notSubsetLeft
  have fixedAmbient := separated.subset fixedSelected
  obtain ⟨fixedSource, fixedSourcePresent, fixedNeighbor⟩ :=
    Expansion.exists_source_of_mem_support_bind₁
      (substitution basis left right) polynomial fixed fixedAmbient
  obtain ⟨fixedLeft, fixedRight, fixedSum, fixedEqual⟩ :=
    exists_split_of_neighbor basis left right fixedSource fixed fixedNeighbor
  rw [Finset.card_le_one]
  intro first firstPresent second secondPresent
  have firstData := Finset.mem_sdiff.mp firstPresent
  have secondData := Finset.mem_sdiff.mp secondPresent
  have firstEqual := eq_shiftLeft_of_not_mem_endpoints
    basis left right polynomial separated fixed fixedSelected fixedNotLeft
    fixedSource fixedSourcePresent fixedLeft fixedRight fixedSum fixedEqual
    first firstData.1 firstData.2
  have secondEqual := eq_shiftLeft_of_not_mem_endpoints
    basis left right polynomial separated fixed fixedSelected fixedNotLeft
    fixedSource fixedSourcePresent fixedLeft fixedRight fixedSum fixedEqual
    second secondData.1 secondData.2
  exact firstEqual.trans secondEqual.symm

/-- Every separated enriched set restricts to one endpoint support while
losing at most one element. -/
theorem restrict_to_endpoint
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (selected : Finset (ℕ →₀ ℕ))
    (separated : IsSeparated
      (MvPolynomial.bind₁ (substitution basis left right) polynomial).support
      selected) :
    (IsSeparated
        (transform (endpointBasis basis left) polynomial).support
        (selected ∩
          (transform (endpointBasis basis left) polynomial).support) ∧
      selected.card - 1 ≤
        (selected ∩
          (transform (endpointBasis basis left) polynomial).support).card - 1 + 1) ∨
    (IsSeparated
        (transform (endpointBasis basis right) polynomial).support
        (selected ∩
          (transform (endpointBasis basis right) polynomial).support) ∧
      selected.card - 1 ≤
        (selected ∩
          (transform (endpointBasis basis right) polynomial).support).card - 1 + 1) := by
  classical
  by_cases subsetLeft : selected ⊆
      (transform (endpointBasis basis left) polynomial).support
  · left
    constructor
    · exact IsSeparated.inter_of_subset separated
        (leftEndpoint_support_subset basis left right polynomial)
    · rw [Finset.inter_eq_left.mpr subsetLeft]
      omega
  · right
    constructor
    · exact IsSeparated.inter_of_subset separated
        (rightEndpoint_support_subset basis left right polynomial)
    · have outsideCard :=
        outside_right_subsingleton_of_not_subset_left
          basis left right polynomial separated subsetLeft
      have decomposition := Finset.card_sdiff_add_card_inter selected
        (transform (endpointBasis basis right) polynomial).support
      omega

/-- Separation after replacing one variable by a sum of two monomials is at
most the larger endpoint separation plus one. -/
theorem separationNumber_bind_add_le
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ) :
    separationNumber
        (MvPolynomial.bind₁
          (substitution basis left right) polynomial).support ≤
      max
          (separationNumber
            (transform (endpointBasis basis left) polynomial).support)
          (separationNumber
            (transform (endpointBasis basis right) polynomial).support) + 1 := by
  classical
  unfold separationNumber
  apply Finset.sup_le
  intro selected _
  split_ifs with separated
  · rcases restrict_to_endpoint basis left right polynomial selected separated with
      leftRestriction | rightRestriction
    · have candidate := candidate_card_sub_one_le leftRestriction.1
      exact leftRestriction.2.trans
        (Nat.add_le_add_right
          (candidate.trans (Nat.le_max_left _ _)) 1)
    · have candidate := candidate_card_sub_one_le rightRestriction.1
      exact rightRestriction.2.trans
        (Nat.add_le_add_right
          (candidate.trans (Nat.le_max_right _ _)) 1)
  · exact Nat.zero_le _

/-- A post-composed monomial substitution turns ordinary reverse addition
enrichment into substitution of the eliminated variable by the sum of the
two corresponding monomials. -/
theorem transform_reverse_add_eq
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (left right : Fin variableCount) :
    transform basis
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left + MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) =
      MvPolynomial.bind₁
        (substitution basis (basis left) (basis right)) polynomial := by
  rw [transform, MvPolynomial.bind₁_bind₁]
  congr 1
  apply MvPolynomial.algHom_ext
  intro source
  simp only [MvPolynomial.bind₁_X_right]
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · simp [substitution, MonomialSubstitution.substitution]
  · simp [substitution, MonomialSubstitution.substitution]

/-- Reverse addition substitution grows Schnorr's closed separation by at
most one. -/
theorem separationClosure_add_substitution_le
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (left right : Fin variableCount) :
    separationClosure
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left + MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) ≤
      separationClosure polynomial + 1 := by
  by_cases positive : 0 < separationClosure
      (MvPolynomial.bind₁
        (Fin.lastCases
          (MvPolynomial.X left + MvPolynomial.X right)
          MvPolynomial.X)
        polynomial)
  · obtain ⟨basis, witnessed⟩ :=
      achievable_separationClosure_of_pos positive
    calc
      separationClosure
          (MvPolynomial.bind₁
            (Fin.lastCases
              (MvPolynomial.X left + MvPolynomial.X right)
              MvPolynomial.X)
            polynomial) ≤
          separationNumber
            (transform basis
              (MvPolynomial.bind₁
                (Fin.lastCases
                  (MvPolynomial.X left + MvPolynomial.X right)
                  MvPolynomial.X)
                polynomial)).support := witnessed
      _ = separationNumber
          (MvPolynomial.bind₁
            (substitution basis (basis left) (basis right))
            polynomial).support := by
        rw [transform_reverse_add_eq]
      _ ≤ max
            (separationNumber
              (transform (endpointBasis basis (basis left))
                polynomial).support)
            (separationNumber
              (transform (endpointBasis basis (basis right))
                polynomial).support) + 1 :=
        separationNumber_bind_add_le basis (basis left) (basis right)
          polynomial
      _ ≤ separationClosure polynomial + 1 := by
        apply Nat.add_le_add_right
        exact max_le
          (separationNumber_transform_le_closure _ _)
          (separationNumber_transform_le_closure _ _)
  · omega

/-- Schnorr's substitution-closed separation is an unconditional addition
progress measure for constant-free monotone arithmetic circuits. -/
def measure : Progress.Measure
    (Algebraic.Arithmetic.additionCost (K := PEmpty)) where
  value := fun _ polynomial => separationClosure polynomial
  variable_zero := fun _ coordinate => separationClosure_X coordinate
  add_substitution_le := by
    intro variableCount polynomial left right
    simpa using separationClosure_add_substitution_le polynomial left right
  mul_substitution_le := by
    intro variableCount polynomial left right
    simpa using product_substitution_le polynomial left right

/-- Coefficient-insensitive Schnorr closure lower-bounds additions in every
constant-free monotone arithmetic circuit. -/
theorem circuit_addition_lowerBound
    (target : MvPolynomial (Fin n) ℕ)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (polynomialInterpretation (Fin n))) :
    separationClosure target ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := PEmpty)) :=
  measure.circuit_lowerBound target circuit constructs

/-- Ordinary support separation is a coefficient-insensitive addition lower
bound. -/
theorem circuit_addition_lowerBound_of_separationNumber
    (target : MvPolynomial (Fin n) ℕ)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (polynomialInterpretation (Fin n))) :
    separationNumber target.support ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := PEmpty)) :=
  (separationNumber_le_closure target).trans
    (circuit_addition_lowerBound target circuit constructs)

/-- Schnorr's classical theorem: if the full monomial support is separated,
all but one support monomials must be paid for by additions, independently of
their positive coefficients. -/
theorem circuit_addition_lowerBound_of_isSeparated
    (target : MvPolynomial (Fin n) ℕ)
    (targetSeparated : IsSeparated target.support target.support)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (polynomialInterpretation (Fin n))) :
    target.support.card - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := PEmpty)) := by
  rw [← separationNumber_eq_card_sub_one targetSeparated]
  exact circuit_addition_lowerBound_of_separationNumber
    target circuit constructs

end
end Addition
end Closure
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
