/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Defs

/-!
# From proofs to answer tables

The combinatorial heart of `PCP[r, q] ⊆ NP`: a nondeterministic machine cannot
guess the *proof*, which may be astronomically long — the verifier's query
positions are outputs of a polynomial-time function, so they are bounded only by
`2 ^ poly`. What it can guess is the much smaller table of answers at the
positions actually queried.

This module shows the two are interchangeable. A proof determines a table by
reading it, and conversely any table that satisfies the verifier on every coin
string can be realised by an actual proof — take the list long enough to cover
every position the verifier could ever ask about, which is a finite maximum since
there are finitely many coin strings.

## Main definitions

- `PCPVerifier.AcceptsWith` — acceptance when answers come from a table
- `PCPVerifier.maxQuery` — a bound past every position the verifier can query

## Main results

- `PCPVerifier.accepts_iff_acceptsWith` — a proof is a table
- `PCPVerifier.exists_proof_of_table` — a table is a proof
- `PCPVerifier.Consistent`, `PCPVerifier.exists_proof_of_consistent_table` — a
  consistent accepted table, indexed by coin string, is a proof
- `PCPVerifier.exists_proof_iff_exists_table` — the two are interchangeable
- `PCPVerifier.coinIndex`, `PCPVerifier.tableOf`, `PCPVerifier.Witness` — the
  table as a bitstring, in a fixed-stride layout
- `PCPVerifier.witnessOf`, `PCPVerifier.tableOf_witnessOf` — the witness a proof
  induces
- `PCPVerifier.exists_witness_iff` — a proof exists exactly when a witness does
- `PCPVerifier.eventProb_acceptEvent_eq_one_iff` — certain acceptance, unfolded
-/

@[expose] public section

namespace Complexity

namespace PCPVerifier

variable (V : PCPVerifier)

/-- The verifier accepts when the answers are read off the table `f`. -/
def AcceptsWith (V : PCPVerifier) (x : List Bool) (f : ℕ → Bool) (ρ : List Bool) : Prop :=
  pair (pair x ρ) ((V.positions x ρ).map f) ∈ V.verdict

/-- Reading a proof gives a table, and acceptance is unchanged. -/
theorem accepts_iff_acceptsWith (x π ρ : List Bool) :
    V.Accepts x π ρ ↔ V.AcceptsWith x (fun i => π.getD i false) ρ := Iff.rfl

/-! ### Realising a table by a proof -/

/-- A bound past every position the verifier can query on `x` with `t` coins. -/
noncomputable def maxQuery (V : PCPVerifier) (t : ℕ) (x : List Bool) : ℕ :=
  (Finset.univ.sup fun ρ : Fin t → Bool =>
    (V.positions x (BitString.toList ρ)).foldr max 0) + 1

theorem lt_maxQuery {t : ℕ} {x : List Bool} {ρ : Fin t → Bool} {p : ℕ}
    (hp : p ∈ V.positions x (BitString.toList ρ)) : p < V.maxQuery t x := by
  have h1 : p ≤ (V.positions x (BitString.toList ρ)).foldr max 0 := List.le_max_of_le' 0 hp le_rfl
  have h2 : (V.positions x (BitString.toList ρ)).foldr max 0
      ≤ Finset.univ.sup fun σ : Fin t → Bool =>
        (V.positions x (BitString.toList σ)).foldr max 0 :=
    Finset.le_sup (f := fun σ : Fin t → Bool =>
      (V.positions x (BitString.toList σ)).foldr max 0) (Finset.mem_univ ρ)
  rw [maxQuery]
  omega

/-- **A table is a proof.** A table accepted on every coin string is realised by
an honest proof: the list of its values up to the largest position the verifier
could query. -/
theorem exists_proof_of_table (t : ℕ) (x : List Bool) (f : ℕ → Bool)
    (h : ∀ ρ : Fin t → Bool, V.AcceptsWith x f (BitString.toList ρ)) :
    ∃ π : List Bool, ∀ ρ : Fin t → Bool, V.Accepts x π (BitString.toList ρ) := by
  classical
  refine ⟨(List.range (V.maxQuery t x)).map f, fun ρ => ?_⟩
  have hread : ∀ p ∈ V.positions x (BitString.toList ρ),
      ((List.range (V.maxQuery t x)).map f).getD p false = f p := by
    intro p hp
    have hlt : p < V.maxQuery t x := V.lt_maxQuery hp
    have hlen : ((List.range (V.maxQuery t x)).map f).length = V.maxQuery t x := by
      simp
    rw [← List.getElem_eq_getD (h := by rw [hlen]; exact hlt)]
    simp
  have hmap : (V.positions x (BitString.toList ρ)).map
      (fun i => ((List.range (V.maxQuery t x)).map f).getD i false)
      = (V.positions x (BitString.toList ρ)).map f :=
    List.map_congr_left hread
  rw [Accepts, answers, hmap]
  exact h ρ

/-! ### Tables indexed by coin string -/

/-- A table assigns answers to every coin string. It is *consistent* when two
coin strings that query the same position receive the same answer — the
condition a dishonest prover would violate, and the one that lets a table be
read back as a single proof. -/
def Consistent (V : PCPVerifier) (t : ℕ) (x : List Bool)
    (tbl : (Fin t → Bool) → List Bool) : Prop :=
  ∀ (ρ ρ' : Fin t → Bool) (i i' : ℕ) (p : ℕ),
    (V.positions x (BitString.toList ρ))[i]? = some p →
    (V.positions x (BitString.toList ρ'))[i']? = some p →
    (tbl ρ)[i]? = (tbl ρ')[i']?

open Classical in
/-- The position-indexed reading of a table. -/
noncomputable def tableFun (V : PCPVerifier) (t : ℕ) (x : List Bool)
    (tbl : (Fin t → Bool) → List Bool) (p : ℕ) : Bool :=
  if ∃ (ρ : Fin t → Bool) (i : ℕ),
      (V.positions x (BitString.toList ρ))[i]? = some p ∧ (tbl ρ)[i]? = some true
    then true else false

/-- On a consistent table the reading returns the recorded answer. -/
theorem tableFun_eq {t : ℕ} {x : List Bool} {tbl : (Fin t → Bool) → List Bool}
    (hcons : V.Consistent t x tbl) {ρ : Fin t → Bool} {i p : ℕ} {b : Bool}
    (hpos : (V.positions x (BitString.toList ρ))[i]? = some p)
    (hans : (tbl ρ)[i]? = some b) : V.tableFun t x tbl p = b := by
  classical
  cases b with
  | true =>
      rw [tableFun, ite_eq_left ⟨ρ, i, hpos, hans⟩]
  | false =>
      rw [tableFun, ite_eq_right]
      rintro ⟨ρ', i', hpos', hans'⟩
      have := hcons ρ ρ' i i' p hpos hpos'
      rw [hans, hans'] at this
      exact absurd this (by simp)

/-- **A consistent accepted table is a proof.** -/
theorem exists_proof_of_consistent_table (t : ℕ) (x : List Bool)
    (tbl : (Fin t → Bool) → List Bool)
    (hlen : ∀ ρ : Fin t → Bool,
      (tbl ρ).length = (V.positions x (BitString.toList ρ)).length)
    (hcons : V.Consistent t x tbl)
    (hacc : ∀ ρ : Fin t → Bool,
      pair (pair x (BitString.toList ρ)) (tbl ρ) ∈ V.verdict) :
    ∃ π : List Bool, ∀ ρ : Fin t → Bool, V.Accepts x π (BitString.toList ρ) := by
  classical
  refine V.exists_proof_of_table t x (V.tableFun t x tbl) fun ρ => ?_
  have hmap : (V.positions x (BitString.toList ρ)).map (V.tableFun t x tbl) = tbl ρ := by
    refine List.ext_getElem? fun i => ?_
    rcases hi : (V.positions x (BitString.toList ρ))[i]? with _ | p
    · have hlen1 : (V.positions x (BitString.toList ρ)).length ≤ i :=
        List.getElem?_eq_none_iff.mp hi
      rw [List.getElem?_map, hi]
      exact (List.getElem?_eq_none_iff.mpr (by rw [hlen]; exact hlen1)).symm
    · have hilt : i < (V.positions x (BitString.toList ρ)).length :=
        List.getElem?_eq_some_iff.mp hi |>.1
      have hilt' : i < (tbl ρ).length := by rw [hlen]; exact hilt
      obtain ⟨b, hb⟩ : ∃ b, (tbl ρ)[i]? = some b :=
        ⟨(tbl ρ)[i]'hilt', List.getElem?_eq_getElem hilt'⟩
      rw [List.getElem?_map, hi, hb]
      exact congrArg some (V.tableFun_eq hcons hi hb)
  rw [AcceptsWith, hmap]
  exact hacc ρ

/-! ### The characterisation -/

/-- The table a proof induces is consistent: both entries read the same
position of the same proof. -/
theorem consistent_of_proof (t : ℕ) (x π : List Bool) :
    V.Consistent t x fun ρ => answers π (V.positions x (BitString.toList ρ)) := by
  intro ρ ρ' i i' p hpos hpos'
  show (List.map (fun i => π.getD i false) (V.positions x (BitString.toList ρ)))[i]?
    = (List.map (fun i => π.getD i false) (V.positions x (BitString.toList ρ')))[i']?
  rw [List.getElem?_map, List.getElem?_map, hpos, hpos']

theorem length_answers (t : ℕ) (x π : List Bool) (ρ : Fin t → Bool) :
    (answers π (V.positions x (BitString.toList ρ))).length
      = (V.positions x (BitString.toList ρ)).length := by
  show (List.map (fun i => π.getD i false) (V.positions x (BitString.toList ρ))).length = _
  rw [List.length_map]

/-- **Proofs and consistent tables are interchangeable.** This is what lets a
nondeterministic machine guess a polynomially long table instead of a proof it
could never write down. -/
theorem exists_proof_iff_exists_table (t : ℕ) (x : List Bool) :
    (∃ π : List Bool, ∀ ρ : Fin t → Bool, V.Accepts x π (BitString.toList ρ))
      ↔ ∃ tbl : (Fin t → Bool) → List Bool,
          (∀ ρ : Fin t → Bool,
            (tbl ρ).length = (V.positions x (BitString.toList ρ)).length)
          ∧ V.Consistent t x tbl
          ∧ ∀ ρ : Fin t → Bool,
            pair (pair x (BitString.toList ρ)) (tbl ρ) ∈ V.verdict := by
  constructor
  · rintro ⟨π, hπ⟩
    exact ⟨fun ρ => answers π (V.positions x (BitString.toList ρ)),
      V.length_answers t x π, V.consistent_of_proof t x π, hπ⟩
  · rintro ⟨tbl, hlen, hcons, hacc⟩
    exact V.exists_proof_of_consistent_table t x tbl hlen hcons hacc

/-! ### Encoding a table as a witness -/

/-- The digits of a coin string, as an element of `Fin 2` per coin. -/
def coinDigits {t : ℕ} (ρ : Fin t → Bool) : Fin t → Fin 2 :=
  fun i => if ρ i then 1 else 0

theorem coinDigits_injective {t : ℕ} : Function.Injective (coinDigits (t := t)) := by
  intro ρ ρ' h
  funext i
  have hi := congrFun h i
  rw [coinDigits, coinDigits] at hi
  revert hi
  cases ρ i <;> cases ρ' i <;> decide

/-- A canonical index for each coin string: the value of its digits read as a
binary numeral. This is deliberately an explicit equivalence rather than one
obtained from `Fintype.equivFinOfCardEq`, so that the layout of a witness is
computable — the reduction of a verifier to a CNF formula depends on it. -/
def coinIndex {t : ℕ} (ρ : Fin t → Bool) : ℕ :=
  (finFunctionFinEquiv (coinDigits ρ)).val

theorem coinIndex_lt {t : ℕ} (ρ : Fin t → Bool) : coinIndex ρ < 2 ^ t :=
  (finFunctionFinEquiv (coinDigits ρ)).isLt

theorem coinIndex_injective {t : ℕ} : Function.Injective (coinIndex (t := t)) :=
  fun _ _ h => coinDigits_injective (finFunctionFinEquiv.injective (Fin.ext h))

/-- The coin string with a given index — the inverse of `coinIndex`. -/
def coinOfIndex {t : ℕ} (c : Fin (2 ^ t)) : Fin t → Bool :=
  fun i => finFunctionFinEquiv.symm c i == 1

theorem coinOfIndex_coinIndex {t : ℕ} (ρ : Fin t → Bool) (h : coinIndex ρ < 2 ^ t) :
    coinOfIndex ⟨coinIndex ρ, h⟩ = ρ := by
  have hfin : (⟨coinIndex ρ, h⟩ : Fin (2 ^ t)) = finFunctionFinEquiv (coinDigits ρ) :=
    Fin.ext rfl
  funext i
  rw [coinOfIndex, hfin, Equiv.symm_apply_apply, coinDigits]
  cases ρ i <;> decide

/-- The table a witness encodes: the answers for coin string `ρ` sit in the
slots `coinIndex ρ * Q, …` of the witness, a fixed stride apart. -/
noncomputable def tableOf (V : PCPVerifier) (t Q : ℕ) (x : List Bool) (w : List Bool) :
    (Fin t → Bool) → List Bool :=
  fun ρ => (List.range (V.positions x (BitString.toList ρ)).length).map
    fun i => w.getD (coinIndex ρ * Q + i) false

theorem length_tableOf (t Q : ℕ) (x w : List Bool) (ρ : Fin t → Bool) :
    (V.tableOf t Q x w ρ).length = (V.positions x (BitString.toList ρ)).length := by
  rw [tableOf, List.length_map, List.length_range]

/-- The witness relation: the encoded table is consistent and accepted on every
coin string. -/
def Witness (V : PCPVerifier) (t Q : ℕ) (x w : List Bool) : Prop :=
  V.Consistent t x (V.tableOf t Q x w) ∧
    ∀ ρ : Fin t → Bool,
      pair (pair x (BitString.toList ρ)) (V.tableOf t Q x w ρ) ∈ V.verdict

/-- A witness yields a proof. -/
theorem exists_proof_of_witness {t Q : ℕ} {x w : List Bool} (h : V.Witness t Q x w) :
    ∃ π : List Bool, ∀ ρ : Fin t → Bool, V.Accepts x π (BitString.toList ρ) :=
  V.exists_proof_of_consistent_table t x (V.tableOf t Q x w) (V.length_tableOf t Q x w)
    h.1 h.2

open Classical in
/-- The witness a proof induces: each coin string's answers written into its own
stride of the witness. -/
noncomputable def witnessOf (V : PCPVerifier) (t Q : ℕ) (x π : List Bool) : List Bool :=
  (List.range (2 ^ t * Q)).map fun k =>
    if h : k / Q < 2 ^ t then
      π.getD ((V.positions x (BitString.toList (coinOfIndex ⟨k / Q, h⟩))).getD (k % Q) 0)
        false
    else false

theorem length_witnessOf (t Q : ℕ) (x π : List Bool) :
    (V.witnessOf t Q x π).length = 2 ^ t * Q := by
  rw [witnessOf, List.length_map, List.length_range]

/-- The witness a proof induces encodes exactly the proof's own answers. -/
theorem tableOf_witnessOf {t Q : ℕ} (x π : List Bool) (hQ0 : 0 < Q)
    (hQ : ∀ ρ : Fin t → Bool, (V.positions x (BitString.toList ρ)).length ≤ Q)
    (ρ : Fin t → Bool) :
    V.tableOf t Q x (V.witnessOf t Q x π) ρ
      = answers π (V.positions x (BitString.toList ρ)) := by
  classical
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · rw [V.length_tableOf t Q x (V.witnessOf t Q x π) ρ]
    show _ = (List.map (fun i => π.getD i false) _).length
    rw [List.length_map]
  · have hilt : i < (V.positions x (BitString.toList ρ)).length := by
      rw [V.length_tableOf t Q x (V.witnessOf t Q x π) ρ] at h1
      exact h1
    have hiQ : i < Q := lt_of_lt_of_le hilt (hQ ρ)
    have hkey : coinIndex ρ * Q + i < 2 ^ t * Q := by
      have hc := coinIndex_lt ρ
      calc coinIndex ρ * Q + i < coinIndex ρ * Q + Q := by omega
        _ = (coinIndex ρ + 1) * Q := by ring
        _ ≤ 2 ^ t * Q := Nat.mul_le_mul_right _ (by omega)
    have hdiv : (coinIndex ρ * Q + i) / Q = coinIndex ρ := by
      rw [mul_comm, Nat.mul_add_div hQ0, Nat.div_eq_of_lt hiQ, Nat.add_zero]
    have hmod : (coinIndex ρ * Q + i) % Q = i := by
      rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hiQ]
    have hrho : ∀ h : (coinIndex ρ * Q + i) / Q < 2 ^ t,
        coinOfIndex ⟨(coinIndex ρ * Q + i) / Q, h⟩ = ρ := by
      intro h
      have hfin : (⟨(coinIndex ρ * Q + i) / Q, h⟩ : Fin (2 ^ t))
          = ⟨coinIndex ρ, coinIndex_lt ρ⟩ := Fin.ext hdiv
      rw [hfin, coinOfIndex_coinIndex]
    have hdivlt : (coinIndex ρ * Q + i) / Q < 2 ^ t := by
      rw [hdiv]
      exact coinIndex_lt ρ
    have hwit : (V.witnessOf t Q x π).getD (coinIndex ρ * Q + i) false
        = π.getD ((V.positions x (BitString.toList ρ)).getD i 0) false := by
      have hlen : coinIndex ρ * Q + i < (V.witnessOf t Q x π).length := by
        rw [V.length_witnessOf t Q x π]
        exact hkey
      rw [← List.getElem_eq_getD (h := hlen)]
      show ((List.range (2 ^ t * Q)).map _)[coinIndex ρ * Q + i] = _
      erw [List.getElem_map, List.getElem_range, dite_eq_left hdivlt, hrho hdivlt, hmod]
    show ((List.range (V.positions x (BitString.toList ρ)).length).map
      fun i => (V.witnessOf t Q x π).getD (coinIndex ρ * Q + i) false)[i] = _
    erw [List.getElem_map, List.getElem_range, hwit]
    show _ = (List.map (fun i => π.getD i false) _)[i]
    erw [List.getElem_map]
    congr 1
    rw [← List.getElem_eq_getD (h := hilt)]

/-- **The witness characterisation.** A proof exists exactly when a witness
does — and a witness is a bitstring of length `2 ^ t * Q`, which is polynomial
when `t = O(log n)` and `Q = O(1)`. -/
theorem exists_witness_iff {t Q : ℕ} (x : List Bool) (hQ0 : 0 < Q)
    (hQ : ∀ ρ : Fin t → Bool, (V.positions x (BitString.toList ρ)).length ≤ Q) :
    (∃ w : List Bool, V.Witness t Q x w)
      ↔ ∃ π : List Bool, ∀ ρ : Fin t → Bool, V.Accepts x π (BitString.toList ρ) := by
  constructor
  · rintro ⟨w, hw⟩
    exact V.exists_proof_of_witness hw
  · rintro ⟨π, hπ⟩
    refine ⟨V.witnessOf t Q x π, ?_, ?_⟩
    · intro ρ ρ' i i' p hpos hpos'
      rw [V.tableOf_witnessOf x π hQ0 hQ ρ, V.tableOf_witnessOf x π hQ0 hQ ρ']
      exact V.consistent_of_proof t x π ρ ρ' i i' p hpos hpos'
    · intro ρ
      rw [V.tableOf_witnessOf x π hQ0 hQ ρ]
      exact hπ ρ

/-- Certain acceptance is acceptance on every coin string. -/
theorem eventProb_acceptEvent_eq_one_iff (t : ℕ) (x π : List Bool) :
    eventProb (V.acceptEvent t x π) = 1
      ↔ ∀ ρ : Fin t → Bool, V.Accepts x π (BitString.toList ρ) := by
  classical
  have hcard : (Finset.univ : Finset (Fin t → Bool)).card = 2 ^ t := by
    rw [Finset.card_univ, card_finArrowBool]
  constructor
  · intro h ρ
    have huniv : V.acceptEvent t x π = Finset.univ := by
      by_contra hne
      have hlt : (V.acceptEvent t x π).card < 2 ^ t := by
        rw [← hcard]
        exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hne)
      have hpos : (0 : ℚ) < 2 ^ t := by positivity
      rw [eventProb, div_eq_one_iff_eq (ne_of_gt hpos)] at h
      have : ((V.acceptEvent t x π).card : ℚ) < ((2 : ℚ) ^ t) := by exact_mod_cast hlt
      rw [h] at this
      exact absurd this (lt_irrefl _)
    have hmem : ρ ∈ V.acceptEvent t x π := by rw [huniv]; exact Finset.mem_univ ρ
    rw [acceptEvent, Finset.mem_filter] at hmem
    exact hmem.2
  · intro h
    have huniv : V.acceptEvent t x π = Finset.univ := by
      ext ρ
      simp only [acceptEvent, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact h ρ
    rw [huniv, eventProb_univ]

end PCPVerifier

end Complexity
