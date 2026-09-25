/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise
public import Complexitylib.Metacomplexity.MINKT.Gap.Defs
public import Complexitylib.Metacomplexity.MINKT.Gap.Internal

/-!
# Gap MINKT

This module exposes Hirahara's quantitative decision promise and associated
search relation with separate description-loss and clock-blow-up maps.

For a canonical input `(x, 1^t, 1^s)`, the promise distinguishes
`C_U^t(x) <= s` from
`C_U^(tau(|x|,t))(x) > sigma(|x|,s)`. Malformed encodings and intermediate-gap
instances lie outside the promise.
-/


public section

namespace Complexity

namespace GapMINKT

namespace Instance

variable {tapes : ℕ}

/-- The unary threshold has exactly the represented length. -/
@[simp] theorem length_unaryThreshold (inst : Instance) :
    inst.unaryThreshold.length = inst.threshold :=
  length_unaryThreshold_internal inst

/-- Every canonical gap instance decodes exactly. -/
@[simp] theorem decode?_encode (inst : Instance) :
    decode? inst.encode = some inst :=
  decode?_encode_internal inst

/-- Exact decoding accepts precisely canonical gap encodings. -/
theorem decode?_eq_some_iff (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode :=
  decode?_eq_some_iff_internal bits inst

/-- Decoding rejects exactly the noncanonical strings. -/
theorem decode?_eq_none_iff (bits : List Bool) :
    decode? bits = none ↔ ¬ ∃ inst : Instance, bits = inst.encode :=
  decode?_eq_none_iff_internal bits

/-- Canonical gap-instance encoding is injective. -/
theorem encode_injective : Function.Injective encode :=
  encode_injective_internal

/-- Exact nested-pair code length for `(x, 1^t, 1^s)`. -/
@[simp] theorem length_encode (inst : Instance) :
    inst.encode.length =
      4 * inst.output.length + 2 * inst.time + inst.threshold + 6 :=
  length_encode_internal inst

/-- The yes condition is equivalent to a source-short program within the
source clock. -/
theorem isYes_iff_exists_program (inst : Instance) (machine : TM tapes) :
    inst.IsYes machine ↔
      ∃ program, program.length ≤ inst.threshold ∧
        machine.ProducesInTime program inst.output inst.time :=
  isYes_iff_exists_program_internal inst machine

/-- The no condition says exactly that no program meets both relaxed target
resources. -/
theorem isNo_iff_no_relaxedWitness (inst : Instance)
    (machine : TM tapes) (parameters : Parameters) :
    inst.IsNo machine parameters ↔
      ¬∃ program, inst.IsRelaxedWitness machine parameters program :=
  isNo_iff_no_relaxedWitness_internal inst machine parameters

/-- Widening both resources prevents any yes-instance from also satisfying the
no condition. -/
theorem not_isNo_of_isYes (inst : Instance) (machine : TM tapes)
    (parameters : Parameters) (hwidening : parameters.IsWidening)
    (hyes : inst.IsYes machine) : ¬inst.IsNo machine parameters :=
  not_isNo_of_isYes_internal inst machine parameters hwidening hyes

end Instance

/-- Canonical yes-language membership is the source bounded-complexity
inequality. -/
@[simp] theorem mem_yesLanguage_encode_iff {tapes : ℕ}
    (machine : TM tapes) (inst : Instance) :
    inst.encode ∈ yesLanguage machine ↔ inst.IsYes machine :=
  yesLanguage_mem_encode_iff_internal machine inst

/-- Canonical no-language membership is the relaxed lower-bound inequality. -/
@[simp] theorem mem_noLanguage_encode_iff {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters) (inst : Instance) :
    inst.encode ∈ noLanguage machine parameters ↔
      inst.IsNo machine parameters :=
  noLanguage_mem_encode_iff_internal machine parameters inst

/-- Under widening, the two encoded gap languages are disjoint. -/
theorem disjoint_yesLanguage_noLanguage {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (hwidening : parameters.IsWidening) :
    Disjoint (yesLanguage machine) (noLanguage machine parameters) :=
  disjoint_yesLanguage_noLanguage_internal machine parameters hwidening

/-- Encoded yes membership is exactly existence of a raw source program
witness. -/
theorem mem_yesLanguage_iff_exists_program {tapes : ℕ}
    (machine : TM tapes) (bits : List Bool) :
    bits ∈ yesLanguage machine ↔
      ∃ program, YesWitnessRelation machine bits program :=
  mem_yesLanguage_iff_exists_program_internal machine bits

/-- Every valid source program is no longer than its canonical unary-threshold
instance code. -/
theorem yesWitnessRelation_length_le_input {tapes : ℕ}
    (machine : TM tapes) {bits program : List Bool}
    (hrelation : YesWitnessRelation machine bits program) :
    program.length ≤ bits.length :=
  yesWitnessRelation_length_le_input_internal machine hrelation

/-- The direct source-program witness relation for GapMINKT yes-instances is
linearly balanced, with the identity polynomial as its bound. -/
theorem yesWitnessRelation_polyBalanced {tapes : ℕ}
    (machine : TM tapes) :
    PolyBalanced (YesWitnessRelation machine) :=
  yesWitnessRelation_polyBalanced_internal machine

/-- Once its paired verifier language is in `P`, the direct GapMINKT
yes-witness relation belongs to `FNP`; polynomial balance is unconditional. -/
theorem yesWitnessRelation_mem_FNP_of_pairLang_mem_P {tapes : ℕ}
    (machine : TM tapes)
    (hverifier : pairLang (YesWitnessRelation machine) ∈ P) :
    YesWitnessRelation machine ∈ FNP :=
  yesWitnessRelation_mem_FNP_of_pairLang_mem_P_internal machine hverifier

/-- The optimization search relation has a witness exactly when the source
time-bounded complexity is finite. -/
theorem exists_searchRelation_iff {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (hwidening : parameters.IsWidening) (inst : MINKT.Instance) :
    (∃ program, SearchRelation machine parameters inst program) ↔
      machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤ :=
  exists_searchRelation_iff_internal machine parameters hwidening inst

/-- On canonical `(x,1^t)` inputs, the encoded and semantic optimization
search relations agree exactly. -/
@[simp] theorem encodedSearchRelation_encode_iff {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (inst : MINKT.Instance) (program : List Bool) :
    EncodedSearchRelation machine parameters inst.encode program ↔
      SearchRelation machine parameters inst program :=
  encodedSearchRelation_encode_iff_internal machine parameters inst program

/-- The canonical encoded optimization search problem has a solution exactly
when the source time-bounded complexity is finite. -/
theorem exists_encodedSearchRelation_encode_iff {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (hwidening : parameters.IsWidening) (inst : MINKT.Instance) :
    (∃ program, EncodedSearchRelation machine parameters inst.encode program) ↔
      machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤ :=
  exists_encodedSearchRelation_encode_iff_internal
    machine parameters hwidening inst

/-- Explicit composed polynomial bound for every output of the encoded search
relation. The description loss is polynomial in `|x|+s`, while finite source
optima are polynomial in the canonical `(x,1^t)` input length. -/
theorem encodedSearchRelation_length_le_polynomial
    {tapes : ℕ} (machine : TM tapes) (parameters : Parameters)
    (descriptionPolynomial sourcePolynomial : Polynomial ℕ)
    (hdescription : ∀ length optimum,
      parameters.description length optimum ≤
        descriptionPolynomial.eval (length + optimum))
    (hsource : ∀ inst : MINKT.Instance, ∀ optimum : ℕ,
      machine.timeBoundedKolmogorovComplexity inst.output inst.time =
          (optimum : WithTop ℕ) →
        optimum ≤ sourcePolynomial.eval inst.encode.length)
    {bits program : List Bool}
    (hrelation : EncodedSearchRelation machine parameters bits program) :
    program.length ≤
      (descriptionPolynomial.comp (Polynomial.X + sourcePolynomial)).eval
        bits.length :=
  encodedSearchRelation_length_le_polynomial_internal
    machine parameters descriptionPolynomial sourcePolynomial
      hdescription hsource hrelation

/-- Polynomial description loss and polynomially bounded finite source
optima make the canonical optimization search relation polynomially balanced. -/
theorem encodedSearchRelation_polyBalanced
    {tapes : ℕ} (machine : TM tapes) (parameters : Parameters)
    (hdescription : parameters.DescriptionPolyBound)
    (hsource : SourceComplexityPolyBound machine) :
    PolyBalanced (EncodedSearchRelation machine parameters) :=
  encodedSearchRelation_polyBalanced_internal
    machine parameters hdescription hsource

/-- Every deterministic machine satisfies the source-complexity input-size
bound, with the identity polynomial: finite `C_U^t(x)` is at most the unary
clock `t`, which is contained in the canonical input. -/
theorem sourceComplexityPolyBound {tapes : ℕ} (machine : TM tapes) :
    SourceComplexityPolyBound machine :=
  sourceComplexityPolyBound_internal machine

/-- Polynomial growth of the description-loss map is the only parameter
condition needed for polynomial balance of the encoded optimization search
relation. -/
theorem encodedSearchRelation_polyBalanced_of_description
    {tapes : ℕ} (machine : TM tapes) (parameters : Parameters)
    (hdescription : parameters.DescriptionPolyBound) :
    PolyBalanced (EncodedSearchRelation machine parameters) :=
  encodedSearchRelation_polyBalanced_of_description_internal
    machine parameters hdescription

/-- The executable relaxed-resource checker accepts exactly valid candidates. -/
theorem verifyRelaxedWitness_eq_true_iff {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters) (inst : Instance)
    (program : List Bool) :
    verifyRelaxedWitness machine parameters inst program = true ↔
      inst.IsRelaxedWitness machine parameters program :=
  verifyRelaxedWitness_eq_true_iff_internal machine parameters inst program

/-- The executable relaxed-resource checker rejects exactly invalid
candidates. -/
theorem verifyRelaxedWitness_eq_false_iff {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters) (inst : Instance)
    (program : List Bool) :
    verifyRelaxedWitness machine parameters inst program = false ↔
      ¬inst.IsRelaxedWitness machine parameters program :=
  verifyRelaxedWitness_eq_false_iff_internal machine parameters inst program

/-- A correct finite-input search solver makes the search-derived decision
function accept every promised yes-instance when `sigma` is monotone. -/
theorem decisionOfSearch_eq_true_of_mem_yesLanguage
    {tapes : ℕ} {machine : TM tapes} {parameters : Parameters}
    {search : SearchAlgorithm}
    (hdescription : parameters.DescriptionMonotone)
    (hsearch : SolvesSearchOnFinite machine parameters search)
    {bits : List Bool} (hyes : bits ∈ yesLanguage machine) :
    decisionOfSearch machine parameters search bits = true :=
  decisionOfSearch_eq_true_of_mem_yesLanguage_internal
    hdescription hsearch hyes

/-- The search-derived decision function rejects every promised no-instance,
regardless of the search algorithm's behavior there. -/
theorem decisionOfSearch_eq_false_of_mem_noLanguage
    {tapes : ℕ} {machine : TM tapes} {parameters : Parameters}
    (search : SearchAlgorithm) {bits : List Bool}
    (hno : bits ∈ noLanguage machine parameters) :
    decisionOfSearch machine parameters search bits = false :=
  decisionOfSearch_eq_false_of_mem_noLanguage_internal search hno

end GapMINKT

/-- The widening-certified GapMINKT decision promise. -/
@[expose]
def GapMINKT {tapes : ℕ} (machine : TM tapes)
    (parameters : GapMINKT.Parameters)
    (hwidening : parameters.IsWidening) : PromiseProblem where
  yesInstances := GapMINKT.yesLanguage machine
  noInstances := GapMINKT.noLanguage machine parameters
  disjoint := GapMINKT.disjoint_yesLanguage_noLanguage
    machine parameters hwidening

/-- The promise problem exposes exactly the canonical yes language. -/
@[simp] theorem GapMINKT_yesInstances {tapes : ℕ} (machine : TM tapes)
    (parameters : GapMINKT.Parameters)
    (hwidening : parameters.IsWidening) :
    (GapMINKT machine parameters hwidening).yesInstances =
      GapMINKT.yesLanguage machine := rfl

/-- The promise problem exposes exactly the canonical no language. -/
@[simp] theorem GapMINKT_noInstances {tapes : ℕ} (machine : TM tapes)
    (parameters : GapMINKT.Parameters)
    (hwidening : parameters.IsWidening) :
    (GapMINKT machine parameters hwidening).noInstances =
      GapMINKT.noLanguage machine parameters := rfl

/-- A search algorithm correct on every finite source instance induces a
semantic solver for the widening-certified GapMINKT promise. -/
theorem GapMINKT_solvedBy_decisionOfSearch
    {tapes : ℕ} {machine : TM tapes} {parameters : GapMINKT.Parameters}
    (hwidening : parameters.IsWidening)
    (hdescription : parameters.DescriptionMonotone)
    {search : GapMINKT.SearchAlgorithm}
    (hsearch : GapMINKT.SolvesSearchOnFinite machine parameters search) :
    (GapMINKT machine parameters hwidening).SolvedBy
      (GapMINKT.decisionOfSearch machine parameters search) := by
  constructor
  · intro bits hyes
    exact GapMINKT.decisionOfSearch_eq_true_of_mem_yesLanguage
      hdescription hsearch hyes
  · intro bits hno
    exact GapMINKT.decisionOfSearch_eq_false_of_mem_noLanguage search hno

/-- An FNP implementation of the direct yes-witness relation places GapMINKT
in `PromiseNP`. -/
theorem GapMINKT_mem_PromiseNP_of_yesWitnessRelation_mem_FNP
    {tapes : ℕ} {machine : TM tapes} {parameters : GapMINKT.Parameters}
    (hwidening : parameters.IsWidening)
    (hrelation : GapMINKT.YesWitnessRelation machine ∈ FNP) :
    GapMINKT machine parameters hwidening ∈ PromiseNP := by
  apply PromiseProblem.mem_PromiseNP_of_FNP_witness
    (GapMINKT machine parameters hwidening) hrelation
  intro bits
  exact GapMINKT.mem_yesLanguage_iff_exists_program machine bits

/-- The remaining GapMINKT-specific `PromiseNP` obligation is a deterministic
polynomial-time verifier for the paired direct-witness language. -/
theorem GapMINKT_mem_PromiseNP_of_pairLang_mem_P
    {tapes : ℕ} {machine : TM tapes} {parameters : GapMINKT.Parameters}
    (hwidening : parameters.IsWidening)
    (hverifier : pairLang (GapMINKT.YesWitnessRelation machine) ∈ P) :
    GapMINKT machine parameters hwidening ∈ PromiseNP :=
  GapMINKT_mem_PromiseNP_of_yesWitnessRelation_mem_FNP
    hwidening
      (GapMINKT.yesWitnessRelation_mem_FNP_of_pairLang_mem_P machine hverifier)

end Complexity
