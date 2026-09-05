/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.VerifierLang

/-!
# Checking that a witness is consistent

A witness records an answer for every query slot. It comes from an actual proof
only if slots reading the same proof position carry the same answer, and that is
what this module checks: four nested loops over a pair of coin strings and a
pair of query indices.

The check never looks at a position as a number. `posAt` returns each query
position as its own serialization, so slots reading the same position are
recognised by comparing strings — and a slot past the end of a query list is
recognised by that string being empty.

## Main definitions

- `Complexity.consLang` — the consistency check, as a language of `pair x w`

## Main results

- `Complexity.consLang_mem_P` — the check is polynomial time
-/

@[expose] public section

namespace Complexity

section Consistency

variable (V : PCPVerifier) (f : List Bool → List Bool) (r : ℕ → ℕ) (Q : ℕ)

/-! ### Reading the nested loop input

The innermost input is `pair (pair (pair (pair (pair x w) ρ) ρ') i) i'`, with
the four loop indices in unary. -/

/-- Strip the last two indices. -/
def conY2 (y : List Bool) : List Bool := pairFst (pairFst y)

/-- Strip the last three indices. -/
def conY1 (y : List Bool) : List Bool := pairFst (conY2 y)

/-- The original `pair x w`. -/
def conY0 (y : List Bool) : List Bool := pairFst (conY1 y)

/-- The input. -/
def conX (y : List Bool) : List Bool := pairFst (conY0 y)

/-- The witness. -/
def conW (y : List Bool) : List Bool := pairSnd (conY0 y)

/-- The first coin index. -/
def conC1 (y : List Bool) : ℕ := (pairSnd (conY1 y)).length

/-- The second coin index. -/
def conC2 (y : List Bool) : ℕ := (pairSnd (conY2 y)).length

/-- The first query index. -/
def conC3 (y : List Bool) : ℕ := (pairSnd (pairFst y)).length

/-- The second query index. -/
def conC4 (y : List Bool) : ℕ := (pairSnd y).length

theorem conY2_mem_FP : conY2 ∈ FP :=
  mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP

theorem conY1_mem_FP : conY1 ∈ FP :=
  mem_FP_comp conY2_mem_FP Cobham.fstBlock_mem_FP

theorem conY0_mem_FP : conY0 ∈ FP :=
  mem_FP_comp conY1_mem_FP Cobham.fstBlock_mem_FP

theorem conX_mem_FP : conX ∈ FP :=
  mem_FP_comp conY0_mem_FP Cobham.fstBlock_mem_FP

theorem conW_mem_FP : conW ∈ FP :=
  mem_FP_comp conY0_mem_FP Cobham.sndBlock_mem_FP

theorem unary_conC1_mem_FP : (fun y => List.replicate (conC1 y) true) ∈ FP := by
  have := mem_FP_comp (mem_FP_comp conY1_mem_FP Cobham.sndBlock_mem_FP) unaryLength_mem_FP
  exact this

theorem unary_conC2_mem_FP : (fun y => List.replicate (conC2 y) true) ∈ FP := by
  have := mem_FP_comp (mem_FP_comp conY2_mem_FP Cobham.sndBlock_mem_FP) unaryLength_mem_FP
  exact this

theorem unary_conC3_mem_FP : (fun y => List.replicate (conC3 y) true) ∈ FP := by
  have := mem_FP_comp
    (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP) unaryLength_mem_FP
  exact this

theorem unary_conC4_mem_FP : (fun y => List.replicate (conC4 y) true) ∈ FP := by
  have := mem_FP_comp Cobham.sndBlock_mem_FP unaryLength_mem_FP
  exact this

/-! ### The check -/

/-- The first coin string. -/
noncomputable def conRho (y : List Bool) : List Bool :=
  coinStr (r (conX y).length) (conC1 y)

/-- The second coin string. -/
noncomputable def conRho' (y : List Bool) : List Bool :=
  coinStr (r (conX y).length) (conC2 y)

/-- The position the first slot queries, as a string. -/
noncomputable def conP (y : List Bool) : List Bool :=
  posAt (f (pair (conX y) (conRho r y))) (conC3 y)

/-- The position the second slot queries, as a string. -/
noncomputable def conP' (y : List Bool) : List Bool :=
  posAt (f (pair (conX y) (conRho' r y))) (conC4 y)

/-- The answer recorded in the first slot. -/
def conB (y : List Bool) : List Bool :=
  wBlock (conW y) (conC1 y * Q + conC3 y) 1

/-- The answer recorded in the second slot. -/
def conB' (y : List Bool) : List Bool :=
  wBlock (conW y) (conC2 y * Q + conC4 y) 1

/-- The verdict of one iteration: when both slots are real and query the same
position, their answers must agree. -/
noncomputable def conChk (y : List Bool) : List Bool :=
  Cobham.selectHead
    (andBit (Cobham.eqFlag (conP f r y) (conP' f r y))
      (notBit (emptyFlag (conP f r y))))
    (Cobham.eqFlag (conB Q y) (conB' Q y)) [true]

/-! ### Polynomial time -/

variable (hf : f ∈ FP)
  (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP)

include hr in
theorem conRho_mem_FP : conRho r ∈ FP := by
  have ht : (fun y : List Bool => List.replicate (r (conX y).length) true) ∈ FP := by
    have := mem_FP_comp conX_mem_FP hr
    exact this
  exact coinStr_mem_FP ht unary_conC1_mem_FP

include hr in
theorem conRho'_mem_FP : conRho' r ∈ FP := by
  have ht : (fun y : List Bool => List.replicate (r (conX y).length) true) ∈ FP := by
    have := mem_FP_comp conX_mem_FP hr
    exact this
  exact coinStr_mem_FP ht unary_conC2_mem_FP

include hf hr in
theorem conP_mem_FP : conP f r ∈ FP := by
  have hb : (fun y => f (pair (conX y) (conRho r y))) ∈ FP := by
    have := mem_FP_comp (Cobham.pairFn_mem_FP conX_mem_FP (conRho_mem_FP r hr)) hf
    exact this
  have := posAt_mem_FP unary_conC3_mem_FP hb
  refine mem_FP_of_eq this fun y => ?_
  rw [conP, List.length_replicate]

include hf hr in
theorem conP'_mem_FP : conP' f r ∈ FP := by
  have hb : (fun y => f (pair (conX y) (conRho' r y))) ∈ FP := by
    have := mem_FP_comp (Cobham.pairFn_mem_FP conX_mem_FP (conRho'_mem_FP r hr)) hf
    exact this
  have := posAt_mem_FP unary_conC4_mem_FP hb
  refine mem_FP_of_eq this fun y => ?_
  rw [conP', List.length_replicate]

/-- The offset of a slot in the witness, in unary. -/
theorem offset_mem_FP {c d : List Bool → ℕ}
    (hc : (fun y => List.replicate (c y) true) ∈ FP)
    (hd : (fun y => List.replicate (d y) true) ∈ FP) :
    (fun y => List.replicate (c y * Q + d y) false) ∈ FP := by
  have hQ : (fun _ : List Bool => List.replicate Q false) ∈ FP :=
    Cobham.const_replicate_mem_FP Q
  have hmul : (fun y => List.replicate ((c y) * Q) false) ∈ FP := by
    have := Cobham.mulLenFn_mem_FP hc hQ
    refine mem_FP_of_eq this fun y => ?_
    rw [List.length_replicate, List.length_replicate]
  have hzero : (fun y => List.replicate (d y) false) ∈ FP := by
    have := zeroBlockFn_mem_FP hd
    refine mem_FP_of_eq this fun y => ?_
    rw [List.length_replicate]
  have := Cobham.appendFn_mem_FP hmul hzero
  refine mem_FP_of_eq this fun y => ?_
  rw [← List.replicate_add]

theorem conB_mem_FP : conB Q ∈ FP := by
  have hs := offset_mem_FP Q unary_conC1_mem_FP unary_conC3_mem_FP
  have hl : (fun _ : List Bool => [false]) ∈ FP := constFn_mem_FP [false]
  have := wBlock_mem_FP conW_mem_FP hs hl
  refine mem_FP_of_eq this fun y => ?_
  rw [conB, List.length_replicate]
  rfl

theorem conB'_mem_FP : conB' Q ∈ FP := by
  have hs := offset_mem_FP Q unary_conC2_mem_FP unary_conC4_mem_FP
  have hl : (fun _ : List Bool => [false]) ∈ FP := constFn_mem_FP [false]
  have := wBlock_mem_FP conW_mem_FP hs hl
  refine mem_FP_of_eq this fun y => ?_
  rw [conB', List.length_replicate]
  rfl

include hf hr in
theorem conChk_mem_FP : conChk f r Q ∈ FP := by
  refine Cobham.selectHeadFn_mem_FP ?_ ?_ (constFn_mem_FP [true])
  · exact andBitFn_mem_FP (eqFlagFn_mem_FP (conP_mem_FP f r hf hr) (conP'_mem_FP f r hf hr))
      (notBitFn_mem_FP (emptyFlagFn_mem_FP (conP_mem_FP f r hf hr)))
  · exact eqFlagFn_mem_FP (conB_mem_FP Q) (conB'_mem_FP Q)

/-- One iteration of the consistency check. -/
noncomputable def consInner : Language := {y | ∃ b ∈ conChk f r Q y, b = true}

include hf hr in
theorem consInner_mem_P : consInner f r Q ∈ P :=
  mem_P_of_decisionFn (conChk_mem_FP f r Q hf hr) fun _ => Iff.rfl

/-- The two inner loops, over the pair of query indices. -/
noncomputable def consL3 : Language :=
  {y | ∀ i' < Q, pair y (List.replicate i' true) ∈ consInner f r Q}

/-- The outer of the two query-index loops. -/
noncomputable def consL2 : Language :=
  {y | ∀ i < Q, pair y (List.replicate i true) ∈ consL3 f r Q}

/-- The outer loop over the second coin string. -/
noncomputable def consL1 : Language :=
  {y | ∀ c' < 2 ^ r (pairFst (pairFst y)).length,
    pair y (List.replicate c' true) ∈ consL2 f r Q}

/-- **The consistency check**, as a language of `pair x w`. -/
noncomputable def consLang : Language :=
  {z | ∀ c < 2 ^ r (pairFst z).length,
    pair z (List.replicate c true) ∈ consL1 f r Q}

open scoped Complexity in
include hf hr in
theorem consLang_mem_P (hrlog : r =O fun n => Nat.log 2 n) : consLang f r Q ∈ P := by
  have hQ : (fun _ : List Bool => List.replicate Q true) ∈ FP :=
    constFn_mem_FP (List.replicate Q true)
  have hQ' : (fun z : List Bool => List.replicate Q true) ∈ FP := hQ
  have h3 : consL3 f r Q ∈ P :=
    forall_unary_mem_P (consInner_mem_P f r Q hf hr) hQ
  have h2 : consL2 f r Q ∈ P := forall_unary_mem_P h3 hQ'
  have hexp : (fun z : List Bool =>
      List.replicate (2 ^ r (pairFst z).length) true) ∈ FP := by
    have := mem_FP_comp Cobham.fstBlock_mem_FP (unaryExp_mem_FP_of_bigO_log hr hrlog)
    exact this
  have hexp2 : (fun y : List Bool =>
      List.replicate (2 ^ r (pairFst (pairFst y)).length) true) ∈ FP := by
    have := mem_FP_comp Cobham.fstBlock_mem_FP hexp
    exact this
  have h1 : consL1 f r Q ∈ P := forall_unary_mem_P h2 hexp2
  exact forall_unary_mem_P h1 hexp

/-! ### What one iteration says -/

theorem exists_eqFlag_iff (a b : List Bool) :
    (∃ z ∈ Cobham.eqFlag a b, z = true) ↔ a = b := by
  rcases Cobham.eqFlag_flag a b with h | h
  · rw [h]
    simp only [List.mem_singleton, exists_eq_left]
    exact ⟨fun _ => (Cobham.eqFlag_eq_true_iff a b).mp h, fun _ => trivial⟩
  · rw [h]
    simp only [List.mem_singleton, exists_eq_left, false_iff, Bool.false_eq_true]
    intro hab
    rw [(Cobham.eqFlag_eq_true_iff a b).mpr hab] at h
    simp at h

theorem mem_consInner_iff (y : List Bool) :
    y ∈ consInner f r Q
      ↔ (conP f r y = conP' f r y ∧ conP f r y ≠ [] → conB Q y = conB' Q y) := by
  rw [consInner, Set.mem_ofPred_eq, conChk]
  by_cases hcase : conP f r y = conP' f r y ∧ conP f r y ≠ []
  · obtain ⟨heq, hne⟩ := hcase
    have h1 : Cobham.eqFlag (conP f r y) (conP' f r y) = [true] :=
      (Cobham.eqFlag_eq_true_iff _ _).mpr heq
    have h2 : emptyFlag (conP f r y) = [false] := by
      cases hp : conP f r y with
      | nil => exact absurd hp hne
      | cons b t => rw [emptyFlag_cons]
    rw [h1, h2]
    simp only [notBit, andBit, caseBit₀_cons, Bool.cond_false, Bool.cond_true]
    rw [selectHead_cons_true, exists_eqFlag_iff]
    exact ⟨fun h _ => h, fun h => h ⟨heq, hne⟩⟩
  · have hflag : andBit (Cobham.eqFlag (conP f r y) (conP' f r y))
        (notBit (emptyFlag (conP f r y))) = [false] := by
      by_cases heq : conP f r y = conP' f r y
      · have hne : conP f r y = [] := by
          by_contra hne
          exact hcase ⟨heq, hne⟩
        rw [hne, emptyFlag_nil]
        simp only [notBit, andBit, caseBit₀_cons]
        rcases Cobham.eqFlag_flag ([] : List Bool) (conP' f r y) with h | h <;>
          rw [h] <;> simp
      · have h1 : Cobham.eqFlag (conP f r y) (conP' f r y) = [false] := by
          rcases Cobham.eqFlag_flag (conP f r y) (conP' f r y) with h | h
          · exact absurd ((Cobham.eqFlag_eq_true_iff _ _).mp h) heq
          · exact h
        rw [h1]
        simp [andBit]
    rw [hflag, selectHead_cons_false]
    simp only [List.mem_singleton, exists_eq_left]
    exact ⟨fun _ h => absurd h hcase, fun _ => trivial⟩


/-- The packed input of one iteration. -/
def conArg (x w : List Bool) (c c' i i' : ℕ) : List Bool :=
  pair (pair (pair (pair (pair x w) (List.replicate c true)) (List.replicate c' true))
    (List.replicate i true)) (List.replicate i' true)

@[simp] theorem conX_arg (x w : List Bool) (c c' i i' : ℕ) :
    conX (conArg x w c c' i i') = x := by
  rw [conArg, conX, conY0, conY1, conY2]
  simp only [pairFst_pair]

@[simp] theorem conW_arg (x w : List Bool) (c c' i i' : ℕ) :
    conW (conArg x w c c' i i') = w := by
  rw [conArg, conW, conY0, conY1, conY2]
  simp only [pairFst_pair, pairSnd_pair]

@[simp] theorem conC1_arg (x w : List Bool) (c c' i i' : ℕ) :
    conC1 (conArg x w c c' i i') = c := by
  rw [conArg, conC1, conY1, conY2]
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]

@[simp] theorem conC2_arg (x w : List Bool) (c c' i i' : ℕ) :
    conC2 (conArg x w c c' i i') = c' := by
  rw [conArg, conC2, conY2]
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]

@[simp] theorem conC3_arg (x w : List Bool) (c c' i i' : ℕ) :
    conC3 (conArg x w c c' i i') = i := by
  rw [conArg, conC3]
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]

@[simp] theorem conC4_arg (x w : List Bool) (c c' i i' : ℕ) :
    conC4 (conArg x w c c' i i') = i' := by
  rw [conArg, conC4]
  simp only [pairSnd_pair, List.length_replicate]

/-! ### The pieces on a packed argument -/

variable (hfspec : ∀ x rr : List Bool,
  f (pair x rr) = DataEncode.bitstringEncode (V.positions x rr))

theorem conRho_arg {x w : List Bool} {c c' i i' : ℕ} (hc : c < 2 ^ r x.length) :
    conRho r (conArg x w c c' i i')
      = BitString.toList (PCPVerifier.coinOfIndex (t := r x.length) ⟨c, hc⟩) := by
  rw [conRho, conX_arg, conC1_arg, coinStr_eq hc, toList_coinOfIndex]

theorem conRho'_arg {x w : List Bool} {c c' i i' : ℕ} (hc' : c' < 2 ^ r x.length) :
    conRho' r (conArg x w c c' i i')
      = BitString.toList (PCPVerifier.coinOfIndex (t := r x.length) ⟨c', hc'⟩) := by
  rw [conRho', conX_arg, conC2_arg, coinStr_eq hc', toList_coinOfIndex]

include hfspec in
theorem conP_arg {x w : List Bool} {c c' i i' : ℕ} (hc : c < 2 ^ r x.length) :
    conP f r (conArg x w c c' i i')
      = posAt (DataEncode.bitstringEncode
          (V.positions x (BitString.toList
            (PCPVerifier.coinOfIndex (t := r x.length) ⟨c, hc⟩)))) i := by
  rw [conP, conX_arg, conC3_arg, conRho_arg r hc, hfspec]

include hfspec in
theorem conP'_arg {x w : List Bool} {c c' i i' : ℕ} (hc' : c' < 2 ^ r x.length) :
    conP' f r (conArg x w c c' i i')
      = posAt (DataEncode.bitstringEncode
          (V.positions x (BitString.toList
            (PCPVerifier.coinOfIndex (t := r x.length) ⟨c', hc'⟩)))) i' := by
  rw [conP', conX_arg, conC4_arg, conRho'_arg r hc', hfspec]

theorem conB_arg {x w : List Bool} {c c' i i' : ℕ} (hk : c * Q + i < w.length) :
    conB Q (conArg x w c c' i i') = [w.getD (c * Q + i) false] := by
  rw [conB, conW_arg, conC1_arg, conC3_arg, wBlock_one hk]

theorem conB'_arg {x w : List Bool} {c c' i i' : ℕ} (hk : c' * Q + i' < w.length) :
    conB' Q (conArg x w c c' i i') = [w.getD (c' * Q + i') false] := by
  rw [conB', conW_arg, conC2_arg, conC4_arg, wBlock_one hk]

/-! ### Unfolding the loops -/

theorem mem_consLang_iff_forall (x w : List Bool) :
    pair x w ∈ consLang f r Q
      ↔ ∀ c < 2 ^ r x.length, ∀ c' < 2 ^ r x.length, ∀ i < Q, ∀ i' < Q,
          conArg x w c c' i i' ∈ consInner f r Q := by
  rw [consLang, Set.mem_ofPred_eq, pairFst_pair]
  refine forall_congr' fun c => forall_congr' fun _ => ?_
  rw [consL1, Set.mem_ofPred_eq, pairFst_pair, pairFst_pair]
  refine forall_congr' fun c' => forall_congr' fun _ => ?_
  rw [consL2, Set.mem_ofPred_eq]
  refine forall_congr' fun i => forall_congr' fun _ => ?_
  rw [consL3, Set.mem_ofPred_eq]
  rfl

/-! ### The check is consistency -/

include hfspec in
/-- **The consistency check says exactly what it should.** -/
theorem mem_consLang_iff {x w : List Bool}
    (hw : w.length = 2 ^ r x.length * Q)
    (hQ : ∀ rr : List Bool, (V.positions x rr).length ≤ Q) :
    pair x w ∈ consLang f r Q
      ↔ V.Consistent (r x.length) x (V.tableOf (r x.length) Q x w) := by
  have hfit : ∀ c i : ℕ, c < 2 ^ r x.length → i < Q → c * Q + i < w.length := by
    intro c i hc hi
    rw [hw]
    calc c * Q + i < c * Q + Q := by omega
      _ = (c + 1) * Q := by ring
      _ ≤ 2 ^ r x.length * Q := Nat.mul_le_mul_right _ hc
  rw [mem_consLang_iff_forall]
  constructor
  · intro hR ρ ρ' i i' p hp hp'
    have hc : PCPVerifier.coinIndex ρ < 2 ^ r x.length := PCPVerifier.coinIndex_lt ρ
    have hc' : PCPVerifier.coinIndex ρ' < 2 ^ r x.length := PCPVerifier.coinIndex_lt ρ'
    have hi : i < (V.positions x (BitString.toList ρ)).length := by
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at hp
      exact absurd hp (by simp)
    have hi' : i' < (V.positions x (BitString.toList ρ')).length := by
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at hp'
      exact absurd hp' (by simp)
    have hiQ : i < Q := lt_of_lt_of_le hi (hQ _)
    have hiQ' : i' < Q := lt_of_lt_of_le hi' (hQ _)
    have hpi : (V.positions x (BitString.toList ρ))[i]'hi = p := by
      rw [List.getElem?_eq_getElem hi] at hp
      exact Option.some.inj hp
    have hpi' : (V.positions x (BitString.toList ρ'))[i']'hi' = p := by
      rw [List.getElem?_eq_getElem hi'] at hp'
      exact Option.some.inj hp'
    have hstep := hR _ hc _ hc' i hiQ i' hiQ'
    rw [mem_consInner_iff, conP_arg V f r hfspec hc, conP'_arg V f r hfspec hc',
      PCPVerifier.coinOfIndex_coinIndex ρ hc,
      PCPVerifier.coinOfIndex_coinIndex ρ' hc'] at hstep
    have hbits := hstep ⟨by rw [posAt_eq_of_lt hi, posAt_eq_of_lt hi', hpi, hpi'],
      posAt_ne_nil hi⟩
    rw [conB_arg Q (hfit _ _ hc hiQ), conB'_arg Q (hfit _ _ hc' hiQ')] at hbits
    rw [getElem?_tableOf V _ _ _ _ _ hi, getElem?_tableOf V _ _ _ _ _ hi']
    have : w.getD (PCPVerifier.coinIndex ρ * Q + i) false
        = w.getD (PCPVerifier.coinIndex ρ' * Q + i') false := by
      simpa using hbits
    rw [this]
  · intro hC c hc c' hc' i hi i' hi'
    rw [mem_consInner_iff, conP_arg V f r hfspec hc, conP'_arg V f r hfspec hc',
      conB_arg Q (hfit _ _ hc hi), conB'_arg Q (hfit _ _ hc' hi')]
    rintro ⟨heq, hne⟩
    set ρ := PCPVerifier.coinOfIndex (t := r x.length) ⟨c, hc⟩ with hρ
    set ρ' := PCPVerifier.coinOfIndex (t := r x.length) ⟨c', hc'⟩ with hρ'
    have hin : i < (V.positions x (BitString.toList ρ)).length := by
      by_contra hcon
      exact hne (posAt_eq_nil (by omega))
    have hin' : i' < (V.positions x (BitString.toList ρ')).length := by
      by_contra hcon
      rw [posAt_eq_nil (l := V.positions x (BitString.toList ρ')) (by omega)] at heq
      exact hne heq
    have hpe : (V.positions x (BitString.toList ρ))[i]'hin
        = (V.positions x (BitString.toList ρ'))[i']'hin' :=
      (posAt_eq_iff hin hin').mp heq
    have hcons := hC ρ ρ' i i' ((V.positions x (BitString.toList ρ))[i]'hin)
      (by rw [List.getElem?_eq_getElem hin]) (by rw [List.getElem?_eq_getElem hin', hpe])
    rw [getElem?_tableOf V _ _ _ _ _ hin, getElem?_tableOf V _ _ _ _ _ hin',
      coinIndex_coinOfIndex, coinIndex_coinOfIndex] at hcons
    simpa using Option.some.inj hcons

end Consistency

end Complexity
