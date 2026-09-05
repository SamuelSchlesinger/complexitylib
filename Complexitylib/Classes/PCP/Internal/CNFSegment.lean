/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.CNFCount
public import Complexitylib.Classes.PCP.Internal.PositionsFP

/-!
# Cutting out one clause of an encoded formula

Reading the `j`-th clause of an encoded formula is the same two-bit scan that
counts the clauses, with two additions: a target index to compare against, and a
buffer that collects tokens while the count matches.

The state is `pair (pair target count) (pair collected unread)`.

## Main definitions

- `Complexity.segStep` — one two-bit step of the extraction
- `Complexity.segFrom` — the tokens of one segment

## Main results

- `Complexity.segStep_mem_FP` — the extraction is polynomial time
- `Complexity.segAtFn_mem_FP`, `Complexity.segAtFn_eq` — the packaged
  extraction
- `Complexity.litSegFn_eq` — the `p`-th literal of the `j`-th clause
- `Complexity.litVarFn_eq`, `Complexity.litSignFn_eq` — its variable and sign
-/

@[expose] public section

namespace Complexity

/-- The tokens of the segment with index `t`, having already passed `c`
separators, where the separator is the token `s0 s1`. -/
def segFrom (s0 s1 : Bool) (t c : ℕ) : List Bool → List Bool
  | b0 :: b1 :: r =>
      if b0 = s0 ∧ b1 = s1 then segFrom s0 s1 t (c + 1) r
      else if c = t then b0 :: b1 :: segFrom s0 s1 t c r else segFrom s0 s1 t c r
  | _ => []

@[simp] theorem segFrom_nil (s0 s1 : Bool) (t c : ℕ) : segFrom s0 s1 t c [] = [] := rfl

theorem segFrom_cons₂ (s0 s1 : Bool) (t c : ℕ) (b0 b1 : Bool) (r : List Bool) :
    segFrom s0 s1 t c (b0 :: b1 :: r)
      = if b0 = s0 ∧ b1 = s1 then segFrom s0 s1 t (c + 1) r
        else if c = t then b0 :: b1 :: segFrom s0 s1 t c r else segFrom s0 s1 t c r := rfl

/-- The target index carried by the state. -/
def segTgt (z : List Bool) : List Bool := pairFst (pairFst z)

/-- The number of separators already passed. -/
def segCnt (z : List Bool) : List Bool := pairSnd (pairFst z)

/-- The tokens collected so far. -/
def segColl (z : List Bool) : List Bool := pairFst (pairSnd z)

/-- The unread suffix. -/
def segRest (z : List Bool) : List Bool := pairSnd (pairSnd z)

/-- Does the string begin with the bit `b`, as a flag? -/
def matchBit (b : Bool) (s : List Bool) : List Bool :=
  if b then Cobham.selectHead s [true] [false] else Cobham.selectHead s [false] [true]

theorem matchBit_mem_FP (b : Bool) {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => matchBit b (a z)) ∈ FP := by
  cases b
  · exact Cobham.selectHeadFn_mem_FP ha (constFn_mem_FP [false]) (constFn_mem_FP [true])
  · exact Cobham.selectHeadFn_mem_FP ha (constFn_mem_FP [true]) (constFn_mem_FP [false])

theorem matchBit_cons (b c : Bool) (t : List Bool) :
    matchBit b (c :: t) = if c = b then [true] else [false] := by
  cases b <;> cases c <;> simp [matchBit, selectHead_cons]

/-- Is this token the separator? -/
def segIsSep (s0 s1 : Bool) (z : List Bool) : List Bool :=
  andBit (matchBit s0 (segRest z)) (matchBit s1 (dropOne (segRest z)))

/-- Are we inside the segment we want? -/
def segHere (z : List Bool) : List Bool :=
  Cobham.lenEqFlag (segCnt z) (segTgt z)

/-- One two-bit step of the extraction. -/
def segStep (s0 s1 : Bool) (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (segRest z)) z
    (pair
      (pair (segTgt z)
        (Cobham.selectHead (segIsSep s0 s1 z) (true :: segCnt z) (segCnt z)))
      (pair
        (Cobham.selectHead (segIsSep s0 s1 z) (segColl z)
          (Cobham.selectHead (segHere z)
            (segColl z ++ (segRest z).take 2) (segColl z)))
        (dropOne (dropOne (segRest z)))))

theorem segTgt_mem_FP : segTgt ∈ FP :=
  mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP

theorem segCnt_mem_FP : segCnt ∈ FP :=
  mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP

theorem segColl_mem_FP : segColl ∈ FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP

theorem segRest_mem_FP : segRest ∈ FP :=
  mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP

theorem segIsSep_mem_FP (s0 s1 : Bool) : segIsSep s0 s1 ∈ FP :=
  andBitFn_mem_FP (matchBit_mem_FP s0 segRest_mem_FP)
    (matchBit_mem_FP s1 (dropOneFn_mem_FP segRest_mem_FP))

theorem segHere_mem_FP : segHere ∈ FP :=
  andBitFn_mem_FP (lenLeFlagFn_mem_FP segCnt_mem_FP segTgt_mem_FP)
    (lenLeFlagFn_mem_FP segTgt_mem_FP segCnt_mem_FP)

theorem segStep_mem_FP (s0 s1 : Bool) : segStep s0 s1 ∈ FP := by
  have htake : (fun z : List Bool => (segRest z).take 2) ∈ FP := by
    have := Cobham.takeLenFn_mem_FP (constFn_mem_FP [false, false]) segRest_mem_FP
    refine mem_FP_of_eq this fun z => ?_
    rfl
  refine Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP segRest_mem_FP) id_mem_FP ?_
  refine Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP segTgt_mem_FP ?_)
    (Cobham.pairFn_mem_FP ?_ (dropOneFn_mem_FP (dropOneFn_mem_FP segRest_mem_FP)))
  · exact Cobham.selectHeadFn_mem_FP (segIsSep_mem_FP s0 s1)
      (mem_FP_comp segCnt_mem_FP (Cobham.cons_mem_FP true)) segCnt_mem_FP
  · refine Cobham.selectHeadFn_mem_FP (segIsSep_mem_FP s0 s1) segColl_mem_FP ?_
    exact Cobham.selectHeadFn_mem_FP segHere_mem_FP
      (Cobham.appendFn_mem_FP segColl_mem_FP htake) segColl_mem_FP

/-! ### What the scan collects -/

variable (s0 s1 : Bool)

@[simp] theorem segStep_nil (tgt cnt coll : List Bool) :
    segStep s0 s1 (pair (pair tgt cnt) (pair coll [])) = pair (pair tgt cnt) (pair coll []) := by
  have hr : segRest (pair (pair tgt cnt) (pair coll [])) = [] := by
    rw [segRest, pairSnd_pair, pairSnd_pair]
  rw [segStep, hr, emptyFlag_nil, selectHead_cons_true]

theorem segStep_cons₂ (tgt cnt coll : List Bool) (b0 b1 : Bool) (r : List Bool) :
    segStep s0 s1 (pair (pair tgt cnt) (pair coll (b0 :: b1 :: r)))
      = if b0 = s0 ∧ b1 = s1 then
          pair (pair tgt (true :: cnt)) (pair coll r)
        else pair (pair tgt cnt)
          (pair (if cnt.length = tgt.length then coll ++ [b0, b1] else coll) r) := by
  have hr : segRest (pair (pair tgt cnt) (pair coll (b0 :: b1 :: r))) = b0 :: b1 :: r := by
    rw [segRest, pairSnd_pair, pairSnd_pair]
  have ht : segTgt (pair (pair tgt cnt) (pair coll (b0 :: b1 :: r))) = tgt := by
    rw [segTgt, pairFst_pair, pairFst_pair]
  have hc : segCnt (pair (pair tgt cnt) (pair coll (b0 :: b1 :: r))) = cnt := by
    rw [segCnt, pairFst_pair, pairSnd_pair]
  have hl : segColl (pair (pair tgt cnt) (pair coll (b0 :: b1 :: r))) = coll := by
    rw [segColl, pairSnd_pair, pairFst_pair]
  have hsep : segIsSep s0 s1 (pair (pair tgt cnt) (pair coll (b0 :: b1 :: r)))
      = if b0 = s0 ∧ b1 = s1 then [true] else [false] := by
    rw [segIsSep, hr]
    simp only [dropOne, List.drop_succ_cons, List.drop_zero]
    rw [matchBit_cons, matchBit_cons]
    by_cases h0 : b0 = s0 <;> by_cases h1 : b1 = s1 <;> simp [h0, h1, andBit]
  have hhere : segHere (pair (pair tgt cnt) (pair coll (b0 :: b1 :: r)))
      = if cnt.length = tgt.length then [true] else [false] := by
    rw [segHere, hc, ht]
    by_cases h : cnt.length = tgt.length
    · rw [ite_eq_left h, Cobham.lenEqFlag_eq_true_iff]
      exact h
    · rw [ite_eq_right h]
      rcases Cobham.lenEqFlag_flag cnt tgt with hf | hf
      · rw [Cobham.lenEqFlag_eq_true_iff] at hf
        exact absurd hf h
      · exact hf
  rw [segStep, hr, hsep, hhere, ht, hc, hl, emptyFlag_cons, selectHead_cons_false]
  by_cases hcase : b0 = s0 ∧ b1 = s1
  · rw [ite_eq_left hcase, ite_eq_left hcase, selectHead_cons_true, selectHead_cons_true]
    simp [dropOne]
  · rw [ite_eq_right hcase, ite_eq_right hcase, selectHead_cons_false, selectHead_cons_false]
    by_cases hh : cnt.length = tgt.length
    · rw [ite_eq_left hh, ite_eq_left hh, selectHead_cons_true]
      simp [dropOne]
    · rw [ite_eq_right hh, ite_eq_right hh, selectHead_cons_false]
      simp [dropOne]

/-- **The scan collects the segment.** -/
theorem segStep_iterate : ∀ (k : ℕ) (tgt cnt coll s : List Bool),
    s.length ≤ 2 * k → Even s.length →
    segColl ((segStep s0 s1)^[k] (pair (pair tgt cnt) (pair coll s)))
      = coll ++ segFrom s0 s1 tgt.length cnt.length s := by
  intro k
  induction k with
  | zero =>
      intro tgt cnt coll s hs _
      have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rw [Function.iterate_zero_apply, segColl, pairSnd_pair, pairFst_pair]
      simp
  | succ k ih =>
      intro tgt cnt coll s hs hev
      rw [Function.iterate_succ_apply]
      match s with
      | [] => rw [segStep_nil, ih tgt cnt coll [] (by simp) (by simp)]
      | [b] => exact absurd hev (by simp [Nat.even_add_one])
      | b0 :: b1 :: r =>
          have hr : r.length ≤ 2 * k := by
            simp only [List.length_cons] at hs
            omega
          have hrev : Even r.length := by
            simp only [List.length_cons] at hev
            rcases hev with ⟨m, hm⟩
            exact ⟨m - 1, by omega⟩
          rw [segStep_cons₂, segFrom_cons₂]
          by_cases hcase : b0 = s0 ∧ b1 = s1
          · rw [ite_eq_left hcase, ite_eq_left hcase, ih tgt (true :: cnt) coll r hr hrev]
            simp
          · rw [ite_eq_right hcase, ite_eq_right hcase]
            by_cases hh : cnt.length = tgt.length
            · rw [ite_eq_left hh, ite_eq_left hh, ih tgt cnt _ r hr hrev]
              simp
            · rw [ite_eq_right hh, ite_eq_right hh, ih tgt cnt coll r hr hrev]

theorem even_length_segFrom (s0 s1 : Bool) (t : ℕ) :
    ∀ (n : ℕ) (s : List Bool) (c : ℕ), s.length ≤ n → Even s.length →
      Even (segFrom s0 s1 t c s).length := by
  intro n
  induction n with
  | zero =>
      intro s c hs _
      have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      simp
  | succ n ih =>
      intro s c hs hev
      match s with
      | [] => simp
      | [b] => exact absurd hev (by simp [Nat.even_add_one])
      | b0 :: b1 :: r =>
          rw [segFrom_cons₂]
          have hr : r.length ≤ n := by
            simp only [List.length_cons] at hs
            omega
          have hrev : Even r.length := by
            simp only [List.length_cons] at hev
            rcases hev with ⟨m, hm⟩
            exact ⟨m - 1, by omega⟩
          by_cases hcase : b0 = s0 ∧ b1 = s1
          · rw [ite_eq_left hcase]
            exact ih r (c + 1) hr hrev
          · rw [ite_eq_right hcase]
            by_cases hh : c = t
            · rw [ite_eq_left hh]
              simp only [List.length_cons]
              rcases ih r c hr hrev with ⟨m, hm⟩
              exact ⟨m + 1, by omega⟩
            · rw [ite_eq_right hh]
              exact ih r c hr hrev

/-! ### The scan as one function -/

theorem segStep_one (tgt cnt coll s : List Bool) :
    ∃ cnt' coll' s', segStep s0 s1 (pair (pair tgt cnt) (pair coll s))
        = pair (pair tgt cnt') (pair coll' s')
      ∧ cnt'.length ≤ cnt.length + 1 ∧ coll'.length ≤ coll.length + 2
      ∧ s'.length ≤ s.length := by
  have hr : segRest (pair (pair tgt cnt) (pair coll s)) = s := by
    rw [segRest, pairSnd_pair, pairSnd_pair]
  have ht : segTgt (pair (pair tgt cnt) (pair coll s)) = tgt := by
    rw [segTgt, pairFst_pair, pairFst_pair]
  have hc : segCnt (pair (pair tgt cnt) (pair coll s)) = cnt := by
    rw [segCnt, pairFst_pair, pairSnd_pair]
  have hl : segColl (pair (pair tgt cnt) (pair coll s)) = coll := by
    rw [segColl, pairSnd_pair, pairFst_pair]
  match s with
  | [] =>
      exact ⟨cnt, coll, [], segStep_nil s0 s1 tgt cnt coll, by omega, by omega, le_refl _⟩
  | b :: t =>
      rw [segStep, hr, emptyFlag_cons, selectHead_cons_false, ht, hc, hl]
      refine ⟨_, _, _, rfl, ?_, ?_, ?_⟩
      · refine le_trans (length_selectHead_le _ _ _) ?_
        simp
      · refine le_trans (length_selectHead_le _ _ _) ?_
        simp only [max_le_iff]
        refine ⟨by omega, ?_⟩
        refine le_trans (length_selectHead_le _ _ _) ?_
        simp only [max_le_iff]
        refine ⟨?_, by omega⟩
        rw [List.length_append]
        have h2 : ((b :: t).take 2).length ≤ 2 := by
          rw [List.length_take]
          omega
        omega
      · rw [dropOne, dropOne, List.length_drop, List.length_drop]
        omega

theorem segStep_shape : ∀ (k : ℕ) (tgt cnt coll s : List Bool),
    ∃ cnt' coll' s', (segStep s0 s1)^[k] (pair (pair tgt cnt) (pair coll s))
        = pair (pair tgt cnt') (pair coll' s')
      ∧ cnt'.length ≤ cnt.length + k ∧ coll'.length ≤ coll.length + 2 * k
      ∧ s'.length ≤ s.length := by
  intro k
  induction k with
  | zero => intro tgt cnt coll s; exact ⟨cnt, coll, s, rfl, by omega, by omega, le_refl _⟩
  | succ k ih =>
      intro tgt cnt coll s
      rw [Function.iterate_succ_apply]
      obtain ⟨cnt₁, coll₁, s₁, h1, hc1, hl1, hs1⟩ := segStep_one s0 s1 tgt cnt coll s
      rw [h1]
      obtain ⟨cnt', coll', s', h2, hc2, hl2, hs2⟩ := ih tgt cnt₁ coll₁ s₁
      exact ⟨cnt', coll', s', h2, by omega, by omega, by omega⟩

/-- **The packaged extraction**, on `pair (unary index) encoding`. -/
noncomputable def segAtFn (s0 s1 : Bool) (z : List Bool) : List Bool :=
  segColl ((segStep s0 s1)^[(pairSnd z).length]
    (pair (pair (pairFst z) []) (pair [] (pairSnd z))))

theorem segAtFn_mem_FP : segAtFn s0 s1 ∈ FP := by
  have hf : (fun z : List Bool => pairFst z) ∈ FP := Cobham.fstBlock_mem_FP
  have hs : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
  have hinit : (fun z : List Bool =>
      pair (pair (pairFst z) []) (pair [] (pairSnd z))) ∈ FP :=
    Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP hf (constFn_mem_FP []))
      (Cobham.pairFn_mem_FP (constFn_mem_FP []) hs)
  have hwidth : (fun z : List Bool => polyRuler (Polynomial.C 11 * Polynomial.X
      + Polynomial.C 8) (id z)) ∈ FP := polyRulerFn_mem_FP _ id_mem_FP
  have hbound : ∀ z : List Bool, ∀ k ≤ (pairSnd z).length,
      ((segStep s0 s1)^[k]
          (pair (pair (pairFst z) []) (pair [] (pairSnd z)))).length
        ≤ (polyRuler (Polynomial.C 11 * Polynomial.X + Polynomial.C 8) (id z)).length := by
    intro z k hk
    obtain ⟨cnt', coll', s', h1, hc, hl, hss⟩ :=
      segStep_shape s0 s1 k (pairFst z) [] [] (pairSnd z)
    have hfz : (pairFst z).length ≤ z.length := fstBlock_length_le z
    have hsz : (pairSnd z).length ≤ z.length := sndBlock_length_le z
    rw [h1, pair_length, pair_length, pair_length, polyRuler_length]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, id, List.length_nil, Nat.zero_add] at *
    omega
  have hiter := Cobham.iterate_mem_FP (segStep_mem_FP s0 s1) hinit hs hwidth hbound
  have := mem_FP_comp hiter segColl_mem_FP
  exact this

theorem segAtFn_eq {j : ℕ} {e : List Bool} (h : Even e.length) :
    segAtFn s0 s1 (pair (List.replicate j true) e) = segFrom s0 s1 j 0 e := by
  rw [segAtFn, pairFst_pair, pairSnd_pair,
    segStep_iterate s0 s1 e.length _ _ _ e (by omega) h, List.length_replicate,
    List.length_nil]
  simp

/-! ### Down to a literal -/

/-- **The `p`-th literal of the `j`-th clause**, on
`pair (pair (unary j) (unary p)) encoding`. -/
noncomputable def litSegFn (z : List Bool) : List Bool :=
  segAtFn false true
    (pair (pairSnd (pairFst z))
      (segAtFn true false (pair (pairFst (pairFst z)) (pairSnd z))))

theorem litSegFn_mem_FP : litSegFn ∈ FP := by
  have hj : (fun z : List Bool => pairFst (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hp : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have he : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
  have hcl : (fun z : List Bool => segAtFn true false
      (pair (pairFst (pairFst z)) (pairSnd z))) ∈ FP := by
    have := mem_FP_comp (Cobham.pairFn_mem_FP hj he) (segAtFn_mem_FP true false)
    exact this
  have := mem_FP_comp (Cobham.pairFn_mem_FP hp hcl) (segAtFn_mem_FP false true)
  exact this

theorem litSegFn_eq {j p : ℕ} {e : List Bool} (h : Even e.length) :
    litSegFn (pair (pair (List.replicate j true) (List.replicate p true)) e)
      = segFrom false true p 0 (segFrom true false j 0 e) := by
  rw [litSegFn, pairFst_pair, pairSnd_pair, pairFst_pair,
    pairSnd_pair, segAtFn_eq true false h,
    segAtFn_eq false true (even_length_segFrom true false j e.length e 0 (le_refl _) h)]

/-- The variable a literal names, in unary. -/
noncomputable def litVarFn (z : List Bool) : List Bool := halfFn ((litSegFn z).drop 2)

theorem litVarFn_mem_FP : litVarFn ∈ FP := by
  have hdrop : (fun z : List Bool => (litSegFn z).drop 2) ∈ FP := by
    have := dropLenFn_mem_FP (constFn_mem_FP [false, false]) litSegFn_mem_FP
    refine mem_FP_of_eq this fun z => ?_
    rfl
  have := mem_FP_comp hdrop halfFn_mem_FP
  exact this

theorem litVarFn_eq {j p : ℕ} {e : List Bool} (h : Even e.length) :
    litVarFn (pair (pair (List.replicate j true) (List.replicate p true)) e)
      = List.replicate
        (((segFrom false true p 0 (segFrom true false j 0 e)).length - 2) / 2) true := by
  rw [litVarFn, litSegFn_eq h, halfFn_eq, List.length_drop]

/-- The sign a literal carries, as a flag. -/
noncomputable def litSignFn (z : List Bool) : List Bool :=
  Cobham.selectHead (litSegFn z) [true] [false]

theorem litSignFn_mem_FP : litSignFn ∈ FP :=
  Cobham.selectHeadFn_mem_FP litSegFn_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP [false])

theorem litSignFn_eq {j p : ℕ} {e : List Bool} (h : Even e.length) :
    litSignFn (pair (pair (List.replicate j true) (List.replicate p true)) e)
      = Cobham.selectHead (segFrom false true p 0 (segFrom true false j 0 e))
        [true] [false] := by
  rw [litSignFn, litSegFn_eq h]

end Complexity
