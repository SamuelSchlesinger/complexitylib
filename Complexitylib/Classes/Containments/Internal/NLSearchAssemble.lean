/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.BlockSearchCorrect
public import Complexitylib.Classes.Containments.Internal.BlockAccept
public import Complexitylib.Classes.P.DecisionFn
public import Complexitylib.Classes.P.Bridge
public import Complexitylib.Classes.L

/-!
# Running the search to saturation

⚠️ Unreviewed by Bolton

The search is run for as many steps as there are configurations. Each step
advances the counter by one, so after that many steps the counter has passed
every record — there are at most as many records as configurations — and the
search is complete.

## Main definitions

- `Complexity.searchState` — the unpacked search state after `n` steps

## Main results

- `Complexity.searchState_counter` — the counter counts the steps
- `Complexity.searchState_ok` — the invariant holds throughout
- `Complexity.searchState_complete` — a long enough run finds every reachable
  configuration
-/

@[expose] public section

namespace Complexity

open Cobham

variable {k : ℕ}

/-! ## Rulers of polynomial length -/

/-- The block ruler of a polynomial window. -/
theorem blockRuler_eq_polyRuler (q : Polynomial ℕ) (x : List Bool) :
    blockRuler (q.eval x.length) = polyRuler (2 * q + 2) x := by
  rw [blockRuler, polyRuler, blockWidth]
  congr 1
  simp [Polynomial.eval_add, Polynomial.eval_mul]
  omega

/-! ## The state after `n` steps -/

/-- The unpacked search state after `n` steps. -/
noncomputable def searchState (tm : NTM k) (R V₀ : List Bool) (n : ℕ) :
    List Bool × List Bool :=
  (searchStepPair tm (codeBlocks k) R)^[n] ([], V₀)

/-- **The counter counts the steps.** -/
theorem searchState_counter (tm : NTM k) (R V₀ : List Bool) (n : ℕ) :
    (searchState tm R V₀ n).1.length = n := by
  have key : ∀ (m : ℕ) (s : List Bool × List Bool),
      ((searchStepPair tm (codeBlocks k) R)^[m] s).1.length = s.1.length + m := by
    intro m
    induction m with
    | zero => intro s; simp
    | succ m ih =>
        intro s
        rw [Function.iterate_succ_apply, ih (searchStepPair tm (codeBlocks k) R s),
          searchStepPair]
        split <;> · show (false :: s.1).length + m = s.1.length + (m + 1)
                    rw [List.length_cons]
                    omega
  rw [searchState, key]
  simp

/-- **The invariant holds throughout the run.** -/
theorem searchState_ok (tm : NTM k) {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) (W : ℕ)
    (hq : Fintype.card tm.Q ≤ blockWidth W) (hW : x.length + S x.length + 1 ≤ W) (n : ℕ) :
    SearchOk tm x W (searchState tm (blockRuler W) (Cobham.cfgCode W (tm.initCfg x)) n).1
      (searchState tm (blockRuler W) (Cobham.cfgCode W (tm.initCfg x)) n).2 := by
  induction n with
  | zero => exact searchOk_init tm x W
  | succ n ih =>
      have := searchStepPair_ok tm hdec x W hq hW _ _ ih
      rw [searchState, Function.iterate_succ_apply']
      exact this

/-- **A long enough run finds every reachable configuration.** -/
theorem searchState_complete (tm : NTM k) {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) (W : ℕ)
    (hq : Fintype.card tm.Q ≤ blockWidth W) (hW : x.length + S x.length + 1 ≤ W) (n : ℕ)
    (hn : Fintype.card (Code tm.Q k x.length (S x.length)) ≤ n) {c : Cfg k tm.Q}
    (hc : tm.ReachesCfg (tm.initCfg x) c) :
    memFlag (wideRuler (codeBlocks k) (blockRuler W)) (Cobham.cfgCode W c)
      (searchState tm (blockRuler W) (Cobham.cfgCode W (tm.initCfg x)) n).2 = [true] := by
  have hok := searchState_ok tm hdec x W hq hW n
  refine searchOk_complete tm hdec x W hq hW _ _ hok ?_ hc
  rw [searchState_counter]
  exact le_trans (searchOk_length_le tm hdec x W _ _ hok) (Nat.mul_le_mul_right _ hn)

/-! ## What the accept scan on the finished search decides -/

/-- **The scan fires only on a genuinely accepting configuration.** -/
theorem acceptScan_sound (tm : NTM k) {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) (W : ℕ)
    (hq : Fintype.card tm.Q ≤ blockWidth W) (hW : x.length + S x.length + 1 ≤ W)
    (hW1 : 1 ≤ W) (n : ℕ) (ruler : List Bool) (hruler : W ≤ ruler.length)
    (h : acceptScan k (stateCode tm.qhalt) (blockRuler W) ruler
      (searchState tm (blockRuler W) (Cobham.cfgCode W (tm.initCfg x)) n).2 = [true]) :
    ∃ c, tm.ReachesCfg (tm.initCfg x) c ∧ tm.halted c ∧ c.output.cells 1 = Γ.one := by
  have hRpos : 0 < (blockRuler W).length := by
    rw [blockRuler_length, blockWidth]
    omega
  obtain ⟨i, hlen, hflag⟩ :=
    (acceptScan_eq_true_iff k _ _ _ _ hRpos).mp h
  obtain ⟨cs, hV, -, hreach, -, -⟩ := searchState_ok tm hdec x W hq hW n
  have hbs := codesOf_recordWidth W cs
  have hflatten : (codesOf W cs).flatten.length = cs.length * recordWidth k W := by
    rw [length_flatten_records k W _ hbs, codesOf_length]
  have hwlen : (wideRuler (codeBlocks k) (blockRuler W)).length = recordWidth k W :=
    wideRuler_blockRuler_length k W
  rw [hV, hwlen, hflatten] at hlen
  have hpos := recordWidth_pos k W
  have hi : i < cs.length := by
    by_contra hcon
    have : cs.length * recordWidth k W ≤ i * recordWidth k W :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hi' : i < (codesOf W cs).length := by rwa [codesOf_length]
  have hblk : blockAt (wideRuler (codeBlocks k) (blockRuler W))
      (searchState tm (blockRuler W) (Cobham.cfgCode W (tm.initCfg x)) n).2 i
      = Cobham.cfgCode W cs[i] := by
    rw [hV, blockAt_records k W _ hbs i hi', codesOf_getElem]
  rw [hblk] at hflag
  have hc : tm.ReachesCfg (tm.initCfg x) cs[i] := hreach _ (List.getElem_mem hi)
  have := (acceptFlag_cfgCode tm W cs[i] hq (codeInv_of_reachesCfg tm hdec x hc W hW)
    hW1 ruler hruler).mp hflag
  exact ⟨cs[i], hc, this.1, this.2⟩

/-- **The scan fires whenever an accepting configuration is reachable.** -/
theorem acceptScan_complete (tm : NTM k) {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) (W : ℕ)
    (hq : Fintype.card tm.Q ≤ blockWidth W) (hW : x.length + S x.length + 1 ≤ W)
    (hW1 : 1 ≤ W) (n : ℕ)
    (hn : Fintype.card (Code tm.Q k x.length (S x.length)) ≤ n) (ruler : List Bool)
    (hruler : W ≤ ruler.length) {c : Cfg k tm.Q}
    (hc : tm.ReachesCfg (tm.initCfg x) c) (hhalt : tm.halted c)
    (hout : c.output.cells 1 = Γ.one) :
    acceptScan k (stateCode tm.qhalt) (blockRuler W) ruler
      (searchState tm (blockRuler W) (Cobham.cfgCode W (tm.initCfg x)) n).2 = [true] := by
  have hRpos : 0 < (blockRuler W).length := by
    rw [blockRuler_length, blockWidth]
    omega
  have hmem := searchState_complete tm hdec x W hq hW n hn hc
  have hwpos : 0 < (wideRuler (codeBlocks k) (blockRuler W)).length := by
    rw [wideRuler_blockRuler_length]
    exact recordWidth_pos k W
  obtain ⟨i, hlen, hblk⟩ := (memFlag_eq_true_iff _ _ _ hwpos).mp hmem
  refine (acceptScan_eq_true_iff k _ _ _ _ hRpos).mpr ⟨i, hlen, ?_⟩
  rw [hblk]
  exact (acceptFlag_cfgCode tm W c hq (codeInv_of_reachesCfg tm hdec x hc W hW) hW1
    ruler hruler).mpr ⟨hhalt, hout⟩

/-! ## The search as one polynomial-time function -/

/-- The initial record, built straight from the input. -/
noncomputable def initRecord (tm : NTM k) (R x : List Bool) : List Bool :=
  Cobham.initFn (tm.branchTM false) R x

theorem initRecord_eq (tm : NTM k) (W : ℕ) (x : List Bool) (hx : x.length ≤ W) :
    initRecord tm (blockRuler W) x = Cobham.cfgCode W (tm.initCfg x) :=
  Cobham.initFn_eq (tm.branchTM false) W x hx

theorem initRecordFn_mem_FP (tm : NTM k) {a b : List Bool → List Bool} (ha : a ∈ FP)
    (hb : b ∈ FP) : (fun z => initRecord tm (a z) (b z)) ∈ FP :=
  binFn_mem_FP (g := initRecord tm)
    (Cobham.initFn_mem (tm.branchTM false) (Cobham.proj 0) (Cobham.proj 1)) ha hb

/-- The packed search, one step per bit of the ruler. -/
noncomputable def searchRun (tm : NTM k) (R V₀ ruler : List Bool) : List Bool :=
  (searchStep tm (codeBlocks k))^[ruler.length] (searchPack R [] V₀)

theorem searchRun_eq (tm : NTM k) (R V₀ ruler : List Bool) :
    searchRun tm R V₀ ruler = searchPack R (searchState tm R V₀ ruler.length).1
      (searchState tm R V₀ ruler.length).2 :=
  searchStep_iterate tm (codeBlocks k) R ([], V₀) ruler.length

/-- The visited string a search leaves behind. -/
noncomputable def searchVisited (tm : NTM k) (R V₀ ruler : List Bool) : List Bool :=
  pairSnd (pairSnd (searchRun tm R V₀ ruler))

theorem searchVisited_eq (tm : NTM k) (R V₀ ruler : List Bool) :
    searchVisited tm R V₀ ruler = (searchState tm R V₀ ruler.length).2 := by
  rw [searchVisited, searchRun_eq, searchPack, pairSnd_pair, pairSnd_pair]

/-- **The search is polynomial-time**, given a polynomial bound on its state. -/
theorem searchVisitedFn_mem_FP (tm : NTM k)
    {Rf V₀f rulerf widthf : List Bool → List Bool} (hR : Rf ∈ FP) (hV₀ : V₀f ∈ FP)
    (hruler : rulerf ∈ FP) (hwidth : widthf ∈ FP)
    (hbound : ∀ x, ∀ n ≤ (rulerf x).length,
      ((searchStep tm (codeBlocks k))^[n] (searchPack (Rf x) [] (V₀f x))).length
        ≤ (widthf x).length) :
    (fun x => searchVisited tm (Rf x) (V₀f x) (rulerf x)) ∈ FP := by
  have hinit : (fun x => searchPack (Rf x) [] (V₀f x)) ∈ FP :=
    Cobham.pairFn_mem_FP hR (Cobham.pairFn_mem_FP (constFn_mem_FP []) hV₀)
  have h := Cobham.iterate_mem_FP (searchStep_mem_FP tm (codeBlocks k)) hinit hruler
    hwidth hbound
  have h1 := mem_FP_comp h Cobham.sndBlock_mem_FP
  have h2 := mem_FP_comp h1 Cobham.sndBlock_mem_FP
  refine mem_FP_of_eq h2 fun x => ?_
  rw [Function.comp_apply, Function.comp_apply, searchVisited, searchRun]

/-! ## The verdict -/

/-- **The whole decision**: search the configuration graph, then scan the visited
string for an accepting record. -/
noncomputable def nlVerdict (tm : NTM k) (qp np : Polynomial ℕ) (x : List Bool) :
    List Bool :=
  acceptScan k (stateCode tm.qhalt) (polyRuler (2 * qp + 2) x) (polyRuler qp x)
    (searchVisited tm (polyRuler (2 * qp + 2) x)
      (initRecord tm (polyRuler (2 * qp + 2) x) x) (polyRuler np x))

/-- The verdict is a flag. -/
theorem nlVerdict_flag (tm : NTM k) (qp np : Polynomial ℕ) (x : List Bool) :
    nlVerdict tm qp np x = [true] ∨ nlVerdict tm qp np x = [false] :=
  acceptScan_flag _ _ _ _ _

/-- **The verdict decides the language.** -/
theorem nlVerdict_eq_true_iff (tm : NTM k) {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (qp np : Polynomial ℕ)
    (hqp : ∀ n, n + S n + 1 ≤ qp.eval n)
    (hcardq : ∀ n, Fintype.card tm.Q ≤ blockWidth (qp.eval n))
    (hnp : ∀ n, Fintype.card (Code tm.Q k n (S n)) ≤ np.eval n) (x : List Bool) :
    nlVerdict tm qp np x = [true] ↔ x ∈ L := by
  have hW : x.length + S x.length + 1 ≤ qp.eval x.length := hqp x.length
  have hW1 : 1 ≤ qp.eval x.length := by omega
  have hxW : x.length ≤ qp.eval x.length := by omega
  have hR : polyRuler (2 * qp + 2) x = blockRuler (qp.eval x.length) :=
    (blockRuler_eq_polyRuler qp x).symm
  have hV : searchVisited tm (polyRuler (2 * qp + 2) x)
      (initRecord tm (polyRuler (2 * qp + 2) x) x) (polyRuler np x)
      = (searchState tm (blockRuler (qp.eval x.length))
          (Cobham.cfgCode (qp.eval x.length) (tm.initCfg x)) (np.eval x.length)).2 := by
    rw [searchVisited_eq, hR, initRecord_eq tm _ x hxW, polyRuler_length]
  rw [nlVerdict, hV, hR, mem_iff_exists_accepting_reachable hdec x]
  constructor
  · intro h
    exact acceptScan_sound tm hdec x _ (hcardq x.length) hW hW1 _ (polyRuler qp x)
      (by rw [polyRuler_length]) h
  · rintro ⟨c, hc, hhalt, hout⟩
    exact acceptScan_complete tm hdec x _ (hcardq x.length) hW hW1 _
      (hnp x.length) (polyRuler qp x) (by rw [polyRuler_length]) hc hhalt hout

/-- **The verdict is polynomial-time.** -/
theorem nlVerdictFn_mem_FP (tm : NTM k) {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (qp np wp : Polynomial ℕ)
    (hqp : ∀ n, n + S n + 1 ≤ qp.eval n)
    (hcardq : ∀ n, Fintype.card tm.Q ≤ blockWidth (qp.eval n))
    (hnp : ∀ n, Fintype.card (Code tm.Q k n (S n)) ≤ np.eval n)
    (hwp : ∀ n, 2 * (2 * qp.eval n + 2) + 2 * np.eval n
      + np.eval n * recordWidth k (qp.eval n) + 4 ≤ wp.eval n) :
    (fun x => nlVerdict tm qp np x) ∈ FP := by
  have hx : (fun x : List Bool => x) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hRf : (fun x => polyRuler (2 * qp + 2) x) ∈ FP := polyRulerFn_mem_FP _ hx
  have hV₀ : (fun x => initRecord tm (polyRuler (2 * qp + 2) x) x) ∈ FP :=
    initRecordFn_mem_FP tm hRf hx
  have hruler : (fun x => polyRuler np x) ∈ FP := polyRulerFn_mem_FP _ hx
  have hwidth : (fun x => polyRuler wp x) ∈ FP := polyRulerFn_mem_FP _ hx
  have hbound : ∀ x : List Bool, ∀ n ≤ (polyRuler np x).length,
      ((searchStep tm (codeBlocks k))^[n] (searchPack (polyRuler (2 * qp + 2) x) []
        (initRecord tm (polyRuler (2 * qp + 2) x) x))).length
        ≤ (polyRuler wp x).length := by
    intro x n hn
    have hW := hqp x.length
    have hxW : x.length ≤ qp.eval x.length := by omega
    have hR : polyRuler (2 * qp + 2) x = blockRuler (qp.eval x.length) :=
      (blockRuler_eq_polyRuler qp x).symm
    rw [hR, initRecord_eq tm _ x hxW,
      searchStep_iterate tm (codeBlocks k) (blockRuler (qp.eval x.length))
        ([], Cobham.cfgCode (qp.eval x.length) (tm.initCfg x)) n,
      searchPack_length, polyRuler_length]
    have hok := searchState_ok tm hdec x (qp.eval x.length) (hcardq x.length) hW n
    have hlen := searchOk_length_le tm hdec x (qp.eval x.length) _ _ hok
    have hcnt := searchState_counter tm (blockRuler (qp.eval x.length))
      (Cobham.cfgCode (qp.eval x.length) (tm.initCfg x)) n
    have hcard : Fintype.card (Code tm.Q k x.length (S x.length))
        * recordWidth k (qp.eval x.length)
        ≤ np.eval x.length * recordWidth k (qp.eval x.length) :=
      Nat.mul_le_mul_right _ (hnp x.length)
    have hbr : (blockRuler (qp.eval x.length)).length = 2 * qp.eval x.length + 2 := by
      rw [blockRuler_length, blockWidth]
      ring
    have hnle : n ≤ np.eval x.length := by
      rw [polyRuler_length] at hn
      exact hn
    have hfin := hwp x.length
    rw [searchState] at hlen hcnt
    omega
  have hqruler : (fun x => polyRuler qp x) ∈ FP := polyRulerFn_mem_FP _ hx
  have hV := searchVisitedFn_mem_FP tm hRf hV₀ hruler hwidth hbound
  exact acceptScanFn_mem_FP k (stateCode tm.qhalt) hRf hqruler hV

/-! ## The containment -/

/-- **`NL ⊆ P`.** A log-space nondeterministic machine's configuration graph has
polynomially many nodes, and the worklist search above walks all of it in
polynomial time. -/
theorem NL_subset_P_internal : NL ⊆ P := by
  intro Lang hL
  obtain ⟨k, tm, S, -, hdec, hS⟩ := hL
  obtain ⟨C, D, hCD⟩ := exists_log_bound hS
  obtain ⟨A, B, hAB⟩ := exists_config_bound (k := k) tm.Q hS
  set qp : Polynomial ℕ :=
    Polynomial.C (C + 1) * Polynomial.X + Polynomial.C (D + 1 + Fintype.card tm.Q) with hqpdef
  set np : Polynomial ℕ := Polynomial.C A * (Polynomial.X + 1) ^ B with hnpdef
  set wp : Polynomial ℕ :=
    2 * (2 * qp + 2) + 2 * np + np * (Polynomial.C (codeBlocks k) * (2 * qp + 2)) + 4
    with hwpdef
  have hqpeval : ∀ n : ℕ, qp.eval n = (C + 1) * n + (D + 1 + Fintype.card tm.Q) := by
    intro n
    rw [hqpdef]
    simp
  have hnpeval : ∀ n : ℕ, np.eval n = A * (n + 1) ^ B := by
    intro n
    rw [hnpdef]
    simp
  have hqp : ∀ n, n + S n + 1 ≤ qp.eval n := by
    intro n
    have h1 : S n ≤ C * Nat.log 2 n + D := hCD n
    have h2 : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
    have h3 : C * Nat.log 2 n ≤ C * n := Nat.mul_le_mul_left _ h2
    rw [hqpeval n]
    have h4 : (C + 1) * n = C * n + n := by ring
    omega
  have hcardq : ∀ n, Fintype.card tm.Q ≤ blockWidth (qp.eval n) := by
    intro n
    rw [blockWidth, hqpeval n]
    omega
  have hnp : ∀ n, Fintype.card (Code tm.Q k n (S n)) ≤ np.eval n := by
    intro n
    rw [hnpeval n]
    exact hAB n
  have hwp : ∀ n, 2 * (2 * qp.eval n + 2) + 2 * np.eval n
      + np.eval n * recordWidth k (qp.eval n) + 4 ≤ wp.eval n := by
    intro n
    rw [hwpdef, recordWidth, blockRuler_length, blockWidth]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_C]
    rw [show 2 * (qp.eval n + 1) = 2 * qp.eval n + 2 from by ring]
  refine mem_P_of_decisionFn (f := fun x => nlVerdict tm qp np x)
    (nlVerdictFn_mem_FP tm hdec qp np wp hqp hcardq hnp hwp) fun x => ?_
  show x ∈ Lang ↔ ∃ b ∈ nlVerdict tm qp np x, b = true
  rw [← nlVerdict_eq_true_iff tm hdec qp np hqp hcardq hnp x]
  constructor
  · intro h
    exact ⟨true, by rw [h]; simp, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    rcases nlVerdict_flag tm qp np x with h | h
    · exact h
    · rw [h] at hb
      simp at hb

end Complexity
