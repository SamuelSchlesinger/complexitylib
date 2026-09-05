/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.CNFCount
public import Complexitylib.Classes.PCP.Internal.CNFSegment
public import Complexitylib.SAT.Verifier

/-!
# The scan agrees with the encoding

The clause counter reads two bits at a time and counts the token `10`. This
module checks that against the encoding it is meant to read: every token
occupies two bits, only the clause separator is `10`, and a formula's encoding
carries one separator per clause.

Because tokens are two bits wide and the scan steps two bits at a time, a `10`
pattern straddling two tokens is never seen.

## Main results

- `Complexity.sepCount_encodeTokens` — the scan counts separators
- `Complexity.sepCount_encode` — a formula's encoding has one per clause
- `Complexity.segFrom_tokenJoin` — the extraction returns one segment
- `Complexity.litSegFn_encode` — the packaged extraction returns one literal
- `Complexity.litVarFn_encode` — and its variable index
-/

@[expose] public section

namespace Complexity

open SAT

theorem length_encode_token (t : EncToken) : t.encode.length = 2 := by
  cases t with
  | bit b => cases b <;> rfl
  | litSep => rfl
  | clauseSep => rfl

/-- **The scan counts separators.** -/
theorem sepCount_encodeTokens : ∀ toks : List EncToken,
    sepCount (encodeTokens toks)
      = (toks.filter (fun t => t = EncToken.clauseSep)).length := by
  intro toks
  induction toks with
  | nil => rfl
  | cons t ts ih =>
      rw [encodeTokens_cons, List.filter_cons]
      cases t
      case bit b =>
        cases b
        · show sepCount ([false, false] ++ encodeTokens ts) = _
          rw [show ([false, false] ++ encodeTokens ts)
            = false :: false :: encodeTokens ts from rfl, sepCount_cons₂, ite_eq_right (by simp)]
          simp [ih]
        · show sepCount ([true, true] ++ encodeTokens ts) = _
          rw [show ([true, true] ++ encodeTokens ts)
            = true :: true :: encodeTokens ts from rfl, sepCount_cons₂, ite_eq_right (by simp)]
          simp [ih]
      case litSep =>
        show sepCount ([false, true] ++ encodeTokens ts) = _
        rw [show ([false, true] ++ encodeTokens ts)
          = false :: true :: encodeTokens ts from rfl, sepCount_cons₂, ite_eq_right (by simp)]
        simp [ih]
      case clauseSep =>
        show sepCount ([true, false] ++ encodeTokens ts) = _
        rw [show ([true, false] ++ encodeTokens ts)
          = true :: false :: encodeTokens ts from rfl, sepCount_cons₂, ite_eq_left (by simp)]
        simp [ih]

theorem clause_tokens_no_sep (c : Clause) :
    (Clause.tokens c).filter (fun t => t = EncToken.clauseSep) = [] := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
      rw [Clause.tokens, List.filter_append, List.filter_append, ih]
      have hraw : (Lit.rawTokens l).filter (fun t => t = EncToken.clauseSep) = [] := by
        rw [Lit.rawTokens, List.filter_map]
        simp
      rw [hraw]
      rfl

/-- **A formula's encoding has one separator per clause.** -/
theorem sepCount_encode (φ : CNF) : sepCount φ.encode = φ.length := by
  rw [← CNF.encodeTokens_tokens, sepCount_encodeTokens]
  induction φ with
  | nil => rfl
  | cons c cs ih =>
      rw [CNF.tokens, List.filter_append, List.filter_append, List.length_append,
        List.length_append, clause_tokens_no_sep, ih]
      simp
      omega

/-! ### The extraction returns one clause -/

theorem hne_clauseSep : ∀ t : EncToken, t ≠ EncToken.clauseSep →
    ∃ c0 c1, t.encode = [c0, c1] ∧ ¬(c0 = true ∧ c1 = false) := by
  intro t h
  cases t with
  | bit b =>
      cases b
      · exact ⟨false, false, rfl, by simp⟩
      · exact ⟨true, true, rfl, by simp⟩
  | litSep => exact ⟨false, true, rfl, by simp⟩
  | clauseSep => exact absurd rfl h

theorem hne_litSep : ∀ t : EncToken, t ≠ EncToken.litSep →
    ∃ c0 c1, t.encode = [c0, c1] ∧ ¬(c0 = false ∧ c1 = true) := by
  intro t h
  cases t with
  | bit b =>
      cases b
      · exact ⟨false, false, rfl, by simp⟩
      · exact ⟨true, true, rfl, by simp⟩
  | litSep => exact absurd rfl h
  | clauseSep => exact ⟨true, false, rfl, by simp⟩

/-- Reading past a run of non-separator tokens collects them, or not, according
to whether the count matches. -/
theorem segFrom_encodeTokens_noSep {sep : EncToken} {b0 b1 : Bool}
    (hne : ∀ t : EncToken, t ≠ sep → ∃ c0 c1, t.encode = [c0, c1] ∧ ¬(c0 = b0 ∧ c1 = b1)) :
    ∀ (toks : List EncToken), (∀ t ∈ toks, t ≠ sep) → ∀ (v : List Bool) (t c : ℕ),
      segFrom b0 b1 t c (encodeTokens toks ++ v)
        = (if c = t then encodeTokens toks else []) ++ segFrom b0 b1 t c v := by
  intro toks
  induction toks with
  | nil => intro _ v t c; by_cases h : c = t <;> simp [h]
  | cons tk ts ih =>
      intro hall v t c
      obtain ⟨c0, c1, henc, hnec⟩ := hne tk (hall tk (by simp))
      rw [encodeTokens_cons, henc, List.append_assoc,
        show ([c0, c1] ++ (encodeTokens ts ++ v)) = c0 :: c1 :: (encodeTokens ts ++ v) from rfl,
        segFrom_cons₂, ite_eq_right hnec, ih (fun t' ht' => hall t' (by simp [ht'])) v t c]
      by_cases h : c = t
      · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
        rfl
      · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]

theorem segFrom_of_gt (s0 s1 : Bool) : ∀ (n : ℕ) (s : List Bool) (t c : ℕ),
    s.length ≤ n → t < c → segFrom s0 s1 t c s = [] := by
  intro n
  induction n with
  | zero =>
      intro s t c hs _
      have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rfl
  | succ n ih =>
      intro s t c hs hlt
      match s with
      | [] => rfl
      | [b] => rfl
      | b0 :: b1 :: r =>
          have hr : r.length ≤ n := by
            simp only [List.length_cons] at hs
            omega
          rw [segFrom_cons₂]
          by_cases hcase : b0 = s0 ∧ b1 = s1
          · rw [ite_eq_left hcase]
            exact ih r t (c + 1) hr (by omega)
          · rw [ite_eq_right hcase, ite_eq_right (by omega : ¬ c = t)]
            exact ih r t c hr hlt

/-- Token segments joined by a separator. -/
def tokenJoin (sep : EncToken) : List (List EncToken) → List EncToken
  | [] => []
  | g :: gs => g ++ [sep] ++ tokenJoin sep gs

theorem cnf_tokens_eq (φ : CNF) :
    CNF.tokens φ = tokenJoin EncToken.clauseSep (φ.map Clause.tokens) := by
  induction φ with
  | nil => rfl
  | cons c cs ih => rw [CNF.tokens, ih, List.map_cons, tokenJoin]

theorem clause_tokens_eq (c : Clause) :
    Clause.tokens c = tokenJoin EncToken.litSep (c.map Lit.rawTokens) := by
  induction c with
  | nil => rfl
  | cons l ls ih => rw [Clause.tokens, ih, List.map_cons, tokenJoin]

/-- **The extraction returns one segment.** -/
theorem segFrom_tokenJoin {sep : EncToken} {b0 b1 : Bool} (hsep : sep.encode = [b0, b1])
    (hne : ∀ t : EncToken, t ≠ sep → ∃ c0 c1, t.encode = [c0, c1] ∧ ¬(c0 = b0 ∧ c1 = b1)) :
    ∀ (segs : List (List EncToken)), (∀ g ∈ segs, ∀ t ∈ g, t ≠ sep) →
    ∀ (t c : ℕ), c ≤ t → ∀ hlt : t - c < segs.length,
      segFrom b0 b1 t c (encodeTokens (tokenJoin sep segs))
        = encodeTokens (segs[t - c]'hlt) := by
  intro segs
  induction segs with
  | nil => intro _ t c _ hlt; simp at hlt
  | cons g gs ih =>
      intro hall t c hle hlt
      have hnosep : ∀ t' ∈ g, t' ≠ sep := hall g (by simp)
      have hsplit : tokenJoin sep (g :: gs) = g ++ ([sep] ++ tokenJoin sep gs) := by
        rw [tokenJoin, List.append_assoc]
      rw [hsplit, encodeTokens_append]
      rw [show segFrom b0 b1 t c (encodeTokens g ++
          encodeTokens ([sep] ++ tokenJoin sep gs))
          = (if c = t then encodeTokens g else [])
            ++ segFrom b0 b1 t c (encodeTokens ([sep] ++ tokenJoin sep gs)) from
        segFrom_encodeTokens_noSep hne g hnosep _ t c]
      have hs : encodeTokens ([sep] ++ tokenJoin sep gs)
          = b0 :: b1 :: encodeTokens (tokenJoin sep gs) := by
        rw [encodeTokens_append,
          show encodeTokens [sep] = sep.encode from by simp, hsep]
        rfl
      rw [hs, segFrom_cons₂, ite_eq_left (by simp : (b0 = b0 ∧ b1 = b1))]
      rcases Nat.eq_or_lt_of_le hle with heq | hlt2
      · rw [ite_eq_left heq, segFrom_of_gt b0 b1
          (encodeTokens (tokenJoin sep gs)).length _ t (c + 1) (le_refl _) (by omega)]
        have hzero : t - c = 0 := by omega
        simp only [hzero]
        simp
      · rw [ite_eq_right (by omega : ¬ c = t)]
        have hidx : t - c = (t - (c + 1)) + 1 := by omega
        have hlt' : t - (c + 1) < gs.length := by
          rw [hidx] at hlt
          simp only [List.length_cons] at hlt
          omega
        rw [ih (fun g' hg' => hall g' (by simp [hg'])) t (c + 1) (by omega) hlt']
        simp only [List.nil_append]
        congr 1
        simp only [hidx]
        simp

/-! ### Down to a literal of a real formula -/

theorem length_encodeTokens : ∀ toks : List EncToken,
    (encodeTokens toks).length = 2 * toks.length := by
  intro toks
  induction toks with
  | nil => rfl
  | cons t ts ih =>
      rw [encodeTokens_cons, List.length_append, length_encode_token, ih,
        List.length_cons]
      ring

theorem even_length_encode (φ : CNF) : Even φ.encode.length := by
  rw [← CNF.encodeTokens_tokens, length_encodeTokens]
  exact ⟨(CNF.tokens φ).length, by ring⟩

theorem rawTokens_no_litSep (l : Lit) :
    ∀ t ∈ Lit.rawTokens l, t ≠ EncToken.litSep := by
  intro t ht
  rw [Lit.rawTokens, List.mem_map] at ht
  obtain ⟨b, -, hb⟩ := ht
  rw [← hb]
  simp

/-- **The extraction returns one clause of a real formula.** -/
theorem segFrom_encode_clause (φ : CNF) {j : ℕ} (hj : j < φ.length) :
    segFrom true false j 0 φ.encode = encodeTokens (Clause.tokens (φ[j]'hj)) := by
  rw [← CNF.encodeTokens_tokens, cnf_tokens_eq]
  have hall : ∀ g ∈ φ.map Clause.tokens, ∀ t ∈ g, t ≠ EncToken.clauseSep := by
    intro g hg t ht hcon
    rw [List.mem_map] at hg
    obtain ⟨cl, -, hcl⟩ := hg
    rw [← hcl] at ht
    have hmem : t ∈ (Clause.tokens cl).filter (fun t => t = EncToken.clauseSep) := by
      rw [List.mem_filter]
      exact ⟨ht, by simp [hcon]⟩
    rw [clause_tokens_no_sep cl] at hmem
    simp at hmem
  have hlt : j - 0 < (φ.map Clause.tokens).length := by
    rw [List.length_map]
    omega
  rw [segFrom_tokenJoin rfl hne_clauseSep _ hall j 0 (Nat.zero_le _) hlt]
  congr 1
  simp

/-- **The extraction returns one literal of a real clause.** -/
theorem segFrom_encode_lit (cl : Clause) {p : ℕ} (hp : p < cl.length) :
    segFrom false true p 0 (encodeTokens (Clause.tokens cl))
      = encodeTokens (Lit.rawTokens (cl[p]'hp)) := by
  rw [clause_tokens_eq]
  have hall : ∀ g ∈ cl.map Lit.rawTokens, ∀ t ∈ g, t ≠ EncToken.litSep := by
    intro g hg t ht
    rw [List.mem_map] at hg
    obtain ⟨l, -, hl⟩ := hg
    rw [← hl] at ht
    exact rawTokens_no_litSep l t ht
  have hlt : p - 0 < (cl.map Lit.rawTokens).length := by
    rw [List.length_map]
    omega
  rw [segFrom_tokenJoin rfl hne_litSep _ hall p 0 (Nat.zero_le _) hlt]
  congr 1
  simp

/-- **The packaged extraction returns one literal.** -/
theorem litSegFn_encode (φ : CNF) {j p : ℕ} (hj : j < φ.length)
    (hp : p < (φ[j]'hj).length) :
    litSegFn (pair (pair (List.replicate j true) (List.replicate p true)) φ.encode)
      = encodeTokens (Lit.rawTokens ((φ[j]'hj)[p]'hp)) := by
  rw [litSegFn_eq (even_length_encode φ), segFrom_encode_clause φ hj,
    segFrom_encode_lit _ hp]

theorem length_rawTokens (l : Lit) : (Lit.rawTokens l).length = l.var + 1 := by
  rw [Lit.rawTokens, List.length_map, Lit.encodeRaw_length]

/-- **The extracted literal has the length its variable index dictates.** -/
theorem length_litSegFn_encode (φ : CNF) {j p : ℕ} (hj : j < φ.length)
    (hp : p < (φ[j]'hj).length) :
    (litSegFn (pair (pair (List.replicate j true) (List.replicate p true))
        φ.encode)).length = 2 * (((φ[j]'hj)[p]'hp).var + 1) := by
  rw [litSegFn_encode φ hj hp, length_encodeTokens, length_rawTokens]

/-- **The extraction reads off the variable index.** -/
theorem litVarFn_encode (φ : CNF) {j p : ℕ} (hj : j < φ.length)
    (hp : p < (φ[j]'hj).length) :
    litVarFn (pair (pair (List.replicate j true) (List.replicate p true)) φ.encode)
      = List.replicate (((φ[j]'hj)[p]'hp).var) true := by
  rw [litVarFn, halfFn_eq, List.length_drop, length_litSegFn_encode φ hj hp]
  congr 1
  omega

end Complexity
