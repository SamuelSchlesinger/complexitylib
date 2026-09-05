/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.SubsetNP
public import Complexitylib.SAT.Semantics
public import Complexitylib.SAT.Language
public import Complexitylib.SAT.Verifier

/-!
# A PCP verifier as a CNF formula

`SubsetNP` reduces "some proof is accepted on every coin string" to "some
bitstring is a witness": a table, laid out one block of `Q` answers per coin
string, that is consistent and accepted everywhere. Both conditions are
predicates on individual bits of that bitstring, so both are CNF clauses.

That is what this module builds. The formula's variables *are* the positions of
the witness — a SAT assignment and a witness are the same object, since both
read out of range as `false` — so the encoding needs no translation of models.

* Consistency contributes, for each pair of query slots that read the same proof
  position, the two clauses saying their variables agree.
* Acceptance contributes, for each coin string and each answer vector the
  verdict rejects, the clause blocking that vector.

With `r` coins and `q` queries the formula has `2^r q` variables and
`O(4^r q^2 + 2^r 2^q)` clauses — polynomial when `r` is logarithmic and `q`
constant.

## Main definitions

- `Complexity.allVecs` — the bit vectors of a given length
- `Complexity.PCPVerifier.varIdx` — the variable holding one answer
- `Complexity.PCPVerifier.toCNF` — the formula

## Main results

- `Complexity.mem_allVecs_iff` — `allVecs n` is exactly the vectors of length `n`
-/

@[expose] public section

namespace Complexity

open SAT

/-! ### Enumerating bit vectors -/

/-- Every bit vector of a given length. -/
def allVecs : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allVecs n).flatMap fun v => [false :: v, true :: v]

theorem mem_allVecs_iff : ∀ (n : ℕ) (b : List Bool), b ∈ allVecs n ↔ b.length = n := by
  intro n
  induction n with
  | zero =>
      intro b
      constructor
      · intro hb
        simp only [allVecs, List.mem_singleton] at hb
        rw [hb]
        rfl
      · intro hb
        have : b = [] := List.length_eq_zero_iff.1 hb
        rw [this]
        simp [allVecs]
  | succ m ih =>
      intro b
      constructor
      · intro hb
        simp only [allVecs, List.mem_flatMap] at hb
        obtain ⟨v, hv, hbv⟩ := hb
        have hlen : v.length = m := (ih v).1 hv
        simp only [List.mem_cons] at hbv
        rcases hbv with h | h | h
        · rw [h, List.length_cons, hlen]
        · rw [h, List.length_cons, hlen]
        · exact absurd h (by simp)
      · intro hb
        match b with
        | [] => exact absurd hb (by simp)
        | c :: v =>
            have hlen : v.length = m := by
              rw [List.length_cons] at hb
              omega
            simp only [allVecs, List.mem_flatMap]
            refine ⟨v, (ih v).2 hlen, ?_⟩
            cases c <;> simp

namespace PCPVerifier

variable (V : PCPVerifier)

/-! ### Variables -/

/-- The variable holding the answer to query `i` on coin string `ρ`. The blocks
sit a stride `Q` apart, exactly as `SubsetNP.tableOf` reads them. -/
def varIdx (t Q : ℕ) (ρ : Fin t → Bool) (i : ℕ) : ℕ := coinIndex ρ * Q + i

theorem get_varIdx (t Q : ℕ) (x w : List Bool) (ρ : Fin t → Bool) {i : ℕ}
    (hi : i < (V.positions x (BitString.toList ρ)).length) :
    (V.tableOf t Q x w ρ)[i]? = some (Assignment.get w (varIdx t Q ρ i)) := by
  rw [tableOf, List.getElem?_map, List.getElem?_range hi]
  rfl

/-! ### The clauses -/

/-- The coin strings, listed by index. Computable, unlike an enumeration drawn
from `Finset.univ`, because the reduction has to be carried out by a machine. -/
def coinList (t : ℕ) : List (Fin t → Bool) :=
  (List.finRange (2 ^ t)).map coinOfIndex

theorem mem_coinList (t : ℕ) (ρ : Fin t → Bool) : ρ ∈ coinList t := by
  rw [coinList, List.mem_map]
  exact ⟨⟨coinIndex ρ, coinIndex_lt ρ⟩, List.mem_finRange _, coinOfIndex_coinIndex ρ _⟩

/-- Two query slots reading the same proof position must get the same answer. -/
def consClauses (t Q : ℕ) (x : List Bool) : List Clause :=
  (coinList t).flatMap fun ρ =>
    (coinList t).flatMap fun ρ' =>
      (List.range (V.positions x (BitString.toList ρ)).length).flatMap fun i =>
        (List.range (V.positions x (BitString.toList ρ')).length).flatMap fun i' =>
          if (V.positions x (BitString.toList ρ))[i]?
              = (V.positions x (BitString.toList ρ'))[i']? then
            [[⟨false, varIdx t Q ρ i⟩, ⟨true, varIdx t Q ρ' i'⟩],
              [⟨true, varIdx t Q ρ i⟩, ⟨false, varIdx t Q ρ' i'⟩]]
          else []

/-- For each coin string, a clause blocking every answer vector the verdict
rejects. The verdict arrives as a Boolean function, which is the form a
polynomial-time decision procedure takes. -/
def acceptClauses (g : List Bool → Bool) (t Q : ℕ) (x : List Bool) : List Clause :=
  (coinList t).flatMap fun ρ =>
    ((allVecs (V.positions x (BitString.toList ρ)).length).filter fun b =>
        !g (pair (pair x (BitString.toList ρ)) b)).map fun b =>
      (List.range (V.positions x (BitString.toList ρ)).length).map fun i =>
        (⟨!(b.getD i false), varIdx t Q ρ i⟩ : Lit)

/-- **The formula of a verifier on an input.** -/
def toCNF (g : List Bool → Bool) (t Q : ℕ) (x : List Bool) : CNF :=
  V.consClauses t Q x ++ V.acceptClauses g t Q x

/-! ### Semantics of the consistency clauses -/

theorem eval_consClauses_iff (t Q : ℕ) (x w : List Bool) :
    CNF.eval w (V.consClauses t Q x) = true ↔
      ∀ (ρ ρ' : Fin t → Bool) (i i' : ℕ),
        i < (V.positions x (BitString.toList ρ)).length →
        i' < (V.positions x (BitString.toList ρ')).length →
        (V.positions x (BitString.toList ρ))[i]?
            = (V.positions x (BitString.toList ρ'))[i']? →
        Assignment.get w (varIdx t Q ρ i) = Assignment.get w (varIdx t Q ρ' i') := by
  classical
  rw [CNF.eval, List.all_eq_true]
  constructor
  · intro h ρ ρ' i i' hi hi' hpos
    have hmem : ([⟨false, varIdx t Q ρ i⟩, ⟨true, varIdx t Q ρ' i'⟩] : Clause)
        ∈ V.consClauses t Q x := by
      rw [consClauses]
      simp only [List.mem_flatMap]
      exact ⟨ρ, mem_coinList t ρ, ρ', mem_coinList t ρ', i, List.mem_range.2 hi,
        i', List.mem_range.2 hi', by rw [ite_eq_left hpos]; simp⟩
    have hmem2 : ([⟨true, varIdx t Q ρ i⟩, ⟨false, varIdx t Q ρ' i'⟩] : Clause)
        ∈ V.consClauses t Q x := by
      rw [consClauses]
      simp only [List.mem_flatMap]
      exact ⟨ρ, mem_coinList t ρ, ρ', mem_coinList t ρ', i, List.mem_range.2 hi,
        i', List.mem_range.2 hi', by rw [ite_eq_left hpos]; simp⟩
    have h1 := h _ hmem
    have h2 := h _ hmem2
    simp only [Clause.eval, List.any_cons, List.any_nil, Lit.eval, Bool.or_false,
      Bool.or_eq_true, beq_iff_eq] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all
  · intro h c hc
    rw [consClauses] at hc
    simp only [List.mem_flatMap] at hc
    obtain ⟨ρ, -, ρ', -, i, hi, i', hi', hc⟩ := hc
    rw [List.mem_range] at hi hi'
    by_cases hpos : (V.positions x (BitString.toList ρ))[i]?
        = (V.positions x (BitString.toList ρ'))[i']?
    · rw [ite_eq_left hpos] at hc
      have heq := h ρ ρ' i i' hi hi' hpos
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · simp only [Clause.eval, List.any_cons, List.any_nil, Lit.eval, Bool.or_false,
          Bool.or_eq_true, beq_iff_eq]
        rw [heq]
        cases Assignment.get w (varIdx t Q ρ' i') <;> simp
      · simp only [Clause.eval, List.any_cons, List.any_nil, Lit.eval, Bool.or_false,
          Bool.or_eq_true, beq_iff_eq]
        rw [heq]
        cases Assignment.get w (varIdx t Q ρ' i') <;> simp
      · exact absurd hc (by simp)
    · rw [ite_eq_right hpos] at hc
      exact absurd hc (by simp)

/-! ### Semantics of the acceptance clauses -/

theorem tableOf_getD (t Q : ℕ) (x w : List Bool) (ρ : Fin t → Bool) {i : ℕ}
    (hi : i < (V.positions x (BitString.toList ρ)).length) :
    (V.tableOf t Q x w ρ).getD i false = Assignment.get w (varIdx t Q ρ i) := by
  rw [List.getD_eq_getElem?_getD, V.get_varIdx t Q x w ρ hi]
  rfl

theorem eval_acceptClauses_iff {g : List Bool → Bool}
    (hg : ∀ z, g z = true ↔ z ∈ V.verdict) (t Q : ℕ) (x w : List Bool) :
    CNF.eval w (V.acceptClauses g t Q x) = true ↔
      ∀ ρ : Fin t → Bool,
        pair (pair x (BitString.toList ρ)) (V.tableOf t Q x w ρ) ∈ V.verdict := by
  classical
  rw [CNF.eval, List.all_eq_true]
  constructor
  · intro h ρ
    by_contra hrej
    set L := (V.positions x (BitString.toList ρ)).length with hL
    set b := V.tableOf t Q x w ρ with hb
    have hblen : b.length = L := V.length_tableOf t Q x w ρ
    have hmem : ((List.range L).map fun i =>
        (⟨!(b.getD i false), varIdx t Q ρ i⟩ : Lit)) ∈ V.acceptClauses g t Q x := by
      rw [acceptClauses]
      simp only [List.mem_flatMap, List.mem_map, List.mem_filter]
      refine ⟨ρ, mem_coinList t ρ, b, ⟨(mem_allVecs_iff L b).2 hblen, ?_⟩, rfl⟩
      simp only [Bool.not_eq_true']
      exact Bool.eq_false_iff.2 fun hcon => hrej ((hg _).1 hcon)
    have hev := h _ hmem
    rw [Clause.eval, List.any_eq_true] at hev
    obtain ⟨l, hlmem, hlev⟩ := hev
    rw [List.mem_map] at hlmem
    obtain ⟨i, hi, rfl⟩ := hlmem
    rw [List.mem_range] at hi
    rw [Lit.eval, beq_iff_eq] at hlev
    rw [V.tableOf_getD t Q x w ρ hi] at hlev
    exact absurd hlev (by cases Assignment.get w (varIdx t Q ρ i) <;> simp)
  · intro h c hc
    rw [acceptClauses] at hc
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter] at hc
    obtain ⟨ρ, -, b, ⟨hbvec, hbrej⟩, rfl⟩ := hc
    set L := (V.positions x (BitString.toList ρ)).length with hL
    have hblen : b.length = L := (mem_allVecs_iff L b).1 hbvec
    have htlen : (V.tableOf t Q x w ρ).length = L := V.length_tableOf t Q x w ρ
    have hne : b ≠ V.tableOf t Q x w ρ := by
      intro heq
      rw [heq] at hbrej
      simp only [Bool.not_eq_true'] at hbrej
      exact absurd ((hg _).2 (h ρ)) (by rw [hbrej]; simp)
    -- they differ somewhere
    have hdiff : ∃ i, i < L ∧ b.getD i false ≠ (V.tableOf t Q x w ρ).getD i false := by
      by_contra hall
      push Not at hall
      refine hne (List.ext_getElem (by rw [hblen, htlen]) fun i hi1 hi2 => ?_)
      have hiL : i < L := by rw [← hblen]; exact hi1
      have h1 : b.getD i false = b[i] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1]
        rfl
      have h2 : (V.tableOf t Q x w ρ).getD i false = (V.tableOf t Q x w ρ)[i] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
        rfl
      rw [← h1, ← h2]
      exact hall i hiL
    obtain ⟨i, hi, hne'⟩ := hdiff
    rw [Clause.eval, List.any_eq_true]
    refine ⟨⟨!(b.getD i false), varIdx t Q ρ i⟩, ?_, ?_⟩
    · rw [List.mem_map]
      exact ⟨i, List.mem_range.2 hi, rfl⟩
    · rw [Lit.eval, beq_iff_eq, V.tableOf_getD t Q x w ρ hi] at *
      revert hne'
      cases hbi : b.getD i false <;> cases hwi : Assignment.get w (varIdx t Q ρ i) <;> simp

/-! ### The formula is equivalent to the witness relation -/

/-- **A satisfying assignment is exactly a witness.** -/
theorem eval_toCNF_iff {g : List Bool → Bool} (hg : ∀ z, g z = true ↔ z ∈ V.verdict)
    (t Q : ℕ) (x w : List Bool) :
    CNF.eval w (V.toCNF g t Q x) = true ↔ V.Witness t Q x w := by
  classical
  rw [toCNF, CNF.eval, List.all_append, Bool.and_eq_true, ← CNF.eval, ← CNF.eval,
    V.eval_consClauses_iff t Q x w, V.eval_acceptClauses_iff hg t Q x w, Witness]
  constructor
  · rintro ⟨hcons, hacc⟩
    refine ⟨?_, hacc⟩
    intro ρ ρ' i i' p hp hp'
    have hi : i < (V.positions x (BitString.toList ρ)).length := by
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at hp
      exact absurd hp (by simp)
    have hi' : i' < (V.positions x (BitString.toList ρ')).length := by
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at hp'
      exact absurd hp' (by simp)
    rw [V.get_varIdx t Q x w ρ hi, V.get_varIdx t Q x w ρ' hi']
    exact congrArg some (hcons ρ ρ' i i' hi hi' (by rw [hp, hp']))
  · rintro ⟨hcons, hacc⟩
    refine ⟨?_, hacc⟩
    intro ρ ρ' i i' hi hi' hpos
    have hp : (V.positions x (BitString.toList ρ))[i]?
        = some ((V.positions x (BitString.toList ρ))[i]'hi) :=
      List.getElem?_eq_getElem hi
    have hcons' := hcons ρ ρ' i i' _ hp (by rw [← hpos]; exact hp)
    rw [V.get_varIdx t Q x w ρ hi, V.get_varIdx t Q x w ρ' hi'] at hcons'
    exact Option.some.inj hcons'

/-- **The formula is satisfiable exactly when a proof exists.** -/
theorem satisfiable_toCNF_iff {g : List Bool → Bool} (hg : ∀ z, g z = true ↔ z ∈ V.verdict)
    (t Q : ℕ) (x : List Bool) :
    CNF.Satisfiable (V.toCNF g t Q x) ↔ ∃ w : List Bool, V.Witness t Q x w := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨α, (V.eval_toCNF_iff hg t Q x α).1 hα⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (V.eval_toCNF_iff hg t Q x w).2 hw⟩

/-! ### The reduction, at the level of membership -/

/-- The query budget used for a given input: one more than the bound, so that
the stride is positive even when the verifier makes no queries. -/
def budget (q : ℕ → ℕ) (x : List Bool) : ℕ := q x.length + 1

theorem budget_pos (q : ℕ → ℕ) (x : List Bool) : 0 < budget q x := Nat.succ_pos _

theorem length_positions_le_budget {q : ℕ → ℕ} (hq : V.QueryBounded q) (x : List Bool)
    (r : List Bool) : (V.positions x r).length ≤ budget q x :=
  le_trans (hq x r) (Nat.le_succ _)

/-- **The encoded formula tracks membership.** For an input on which the
verifier is either certainly accepted or accepted with probability at most a
half, the formula is satisfiable exactly when some proof is always accepted. -/
theorem satisfiable_toCNF_iff_exists_proof {g : List Bool → Bool}
    (hg : ∀ z, g z = true ↔ z ∈ V.verdict) {q : ℕ → ℕ} (hq : V.QueryBounded q)
    (t : ℕ) (x : List Bool) :
    CNF.Satisfiable (V.toCNF g t (budget q x) x)
      ↔ ∃ π : List Bool, ∀ ρ : Fin t → Bool, V.Accepts x π (BitString.toList ρ) := by
  rw [V.satisfiable_toCNF_iff hg t (budget q x) x]
  exact V.exists_witness_iff x (budget_pos q x)
    fun ρ => V.length_positions_le_budget hq x (BitString.toList ρ)

/-- **The reduction is correct.** If `L` is decided by the verifier with `t`
coins in the sense of `PCP`, then membership in `L` is membership of the encoded
formula in `SAT`. -/
theorem mem_language_toCNF_iff {L : Language} {g : List Bool → Bool}
    (hg : ∀ z, g z = true ↔ z ∈ V.verdict) {q : ℕ → ℕ} {t : ℕ} (hq : V.QueryBounded q)
    (hcomp : ∀ x ∈ L, ∃ π : List Bool, eventProb (V.acceptEvent t x π) = 1)
    (hsound : ∀ x ∉ L, ∀ π : List Bool, eventProb (V.acceptEvent t x π) ≤ 1 / 2)
    (x : List Bool) :
    x ∈ L ↔ (V.toCNF g t (budget q x) x).encode ∈ SAT.language := by
  constructor
  · intro hx
    obtain ⟨π, hπ⟩ := hcomp x hx
    have hall := (V.eventProb_acceptEvent_eq_one_iff t x π).1 hπ
    obtain ⟨α, hα⟩ := (V.satisfiable_toCNF_iff_exists_proof hg hq t x).2 ⟨π, hall⟩
    exact ⟨_, rfl, ⟨α, hα⟩⟩
  · rintro ⟨φ, hφenc, hφsat⟩
    by_contra hx
    have hφ : φ = V.toCNF g t (budget q x) x := by
      have h1 := CNF.decode?_encode φ
      have h2 := CNF.decode?_encode (V.toCNF g t (budget q x) x)
      rw [hφenc] at h2
      exact Option.some.inj (h1.symm.trans h2)
    have hsat : CNF.Satisfiable (V.toCNF g t (budget q x) x) := hφ ▸ hφsat
    obtain ⟨π, hπ⟩ := (V.satisfiable_toCNF_iff_exists_proof hg hq t x).1 hsat
    have hone : eventProb (V.acceptEvent t x π) = 1 :=
      (V.eventProb_acceptEvent_eq_one_iff t x π).2 hπ
    have hhalf := hsound x hx π
    rw [hone] at hhalf
    norm_num at hhalf

end PCPVerifier

end Complexity
