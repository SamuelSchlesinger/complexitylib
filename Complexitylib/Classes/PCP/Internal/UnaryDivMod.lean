/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.CoinEnum
public import Complexitylib.Classes.Containments.Internal.NLSearchAssemble

/-!
# Division with remainder, in unary

Every index decomposition in an algorithmic constraint graph is a division:
which edge of the original graph, which step of the walk, which copy of the
gadget. This module divides one unary number by another in polynomial time, by
counting up and rolling the remainder over.

## Main definitions

- `Complexity.dmStep` — one tick of the count

## Main results

- `Complexity.dmStep_iterate` — the count divides
- `Complexity.halfFn_mem_FP`, `Complexity.halfFn_eq` — halving a length
-/

@[expose] public section

namespace Complexity

/-- One tick: extend the remainder, and roll it over into the quotient when it
reaches the divisor. The state is `pair (pair quotient remainder) divisor`. -/
def dmStep (st : List Bool) : List Bool :=
  pair (pair
      (Cobham.selectHead
        (Cobham.lenEqFlag (true :: pairSnd (pairFst st)) (pairSnd st))
        (true :: pairFst (pairFst st))
        (pairFst (pairFst st)))
      (Cobham.selectHead
        (Cobham.lenEqFlag (true :: pairSnd (pairFst st)) (pairSnd st))
        [] (true :: pairSnd (pairFst st))))
    (pairSnd st)

theorem dmStep_mem_FP : dmStep ∈ FP := by
  have hq : (fun st : List Bool => pairFst (pairFst st)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hr : (fun st : List Bool => pairSnd (pairFst st)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hb : (fun st : List Bool => pairSnd st) ∈ FP := Cobham.sndBlock_mem_FP
  have hr' : (fun st : List Bool => true :: pairSnd (pairFst st)) ∈ FP :=
    mem_FP_comp hr (Cobham.cons_mem_FP true)
  have hflag : (fun st : List Bool =>
      Cobham.lenEqFlag (true :: pairSnd (pairFst st))
        (pairSnd st)) ∈ FP := by
    exact andBitFn_mem_FP (lenLeFlagFn_mem_FP hr' hb) (lenLeFlagFn_mem_FP hb hr')
  exact Cobham.pairFn_mem_FP
    (Cobham.pairFn_mem_FP
      (Cobham.selectHeadFn_mem_FP hflag (mem_FP_comp hq (Cobham.cons_mem_FP true)) hq)
      (Cobham.selectHeadFn_mem_FP hflag (constFn_mem_FP []) hr')) hb

/-- **The count divides.** After `a` ticks the state holds `a / b` and `a % b`. -/
theorem dmStep_iterate {B : List Bool} (hb : 0 < B.length) :
    ∀ a : ℕ, dmStep^[a] (pair (pair [] []) B)
      = pair (pair (List.replicate (a / B.length) true)
          (List.replicate (a % B.length) true)) B := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply', ih, dmStep, pairSnd_pair,
        pairFst_pair, pairFst_pair, pairSnd_pair]
      set b := B.length with hbdef
      have hlen : (true :: List.replicate (a % b) true).length = a % b + 1 := by simp
      have hmod : a % b < b := Nat.mod_lt _ hb
      by_cases hcase : a % b + 1 = b
      · have hflag : Cobham.lenEqFlag (true :: List.replicate (a % b) true) B = [true] := by
          rw [Cobham.lenEqFlag_eq_true_iff, hlen]
          exact hcase
        rw [hflag, selectHead_cons_true, selectHead_cons_true]
        have hdm := Nat.div_add_mod a b
        have h1 : a + 1 = b * (a / b + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          omega
        have hq : (a + 1) / b = a / b + 1 := by
          rw [h1, Nat.mul_div_cancel_left _ hb]
        have hr : (a + 1) % b = 0 := by
          rw [h1, Nat.mul_mod_right]
        rw [hq, hr, List.replicate_succ]
        simp
      · have hflag : Cobham.lenEqFlag (true :: List.replicate (a % b) true) B = [false] := by
          rcases Cobham.lenEqFlag_flag (true :: List.replicate (a % b) true) B with h | h
          · rw [Cobham.lenEqFlag_eq_true_iff, hlen] at h
            exact absurd h hcase
          · exact h
        rw [hflag, selectHead_cons_false, selectHead_cons_false]
        have hdm := Nat.div_add_mod a b
        have hlt : a % b + 1 < b := by omega
        have h1 : a + 1 = b * (a / b) + (a % b + 1) := by omega
        have hq : (a + 1) / b = a / b := by
          rw [h1, Nat.mul_add_div hb, Nat.div_eq_of_lt hlt]
          omega
        have hr : (a + 1) % b = a % b + 1 := by
          rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
        rw [hq, hr, List.replicate_succ]

/-! ### Halving -/

theorem length_selectHead_le (s x y : List Bool) :
    (Cobham.selectHead s x y).length ≤ max x.length y.length := by
  rw [Cobham.selectHead]
  split
  · exact le_max_left _ _
  · split
    · exact le_max_right _ _
    · simp

theorem dmStep_one (q r b : List Bool) :
    ∃ q' r', dmStep (pair (pair q r) b) = pair (pair q' r') b
      ∧ q'.length ≤ q.length + 1 ∧ r'.length ≤ r.length + 1 := by
  have hq : pairFst (pairFst (pair (pair q r) b)) = q := by
    rw [pairFst_pair, pairFst_pair]
  have hr : pairSnd (pairFst (pair (pair q r) b)) = r := by
    rw [pairFst_pair, pairSnd_pair]
  have hb : pairSnd (pair (pair q r) b) = b := pairSnd_pair _ _
  rw [dmStep, hq, hr, hb]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine le_trans (length_selectHead_le _ _ _) ?_
    simp
  · refine le_trans (length_selectHead_le _ _ _) ?_
    simp

theorem dmStep_shape : ∀ (k : ℕ) (q r b : List Bool),
    ∃ q' r', dmStep^[k] (pair (pair q r) b) = pair (pair q' r') b
      ∧ q'.length ≤ q.length + k ∧ r'.length ≤ r.length + k := by
  intro k
  induction k with
  | zero => intro q r b; exact ⟨q, r, rfl, by omega, by omega⟩
  | succ k ih =>
      intro q r b
      rw [Function.iterate_succ_apply]
      obtain ⟨q₁, r₁, h1, hq1, hr1⟩ := dmStep_one q r b
      rw [h1]
      obtain ⟨q', r', h2, hq2, hr2⟩ := ih q₁ r₁ b
      exact ⟨q', r', h2, by omega, by omega⟩

/-- The counting run: divide a length by a fixed divisor. -/
noncomputable def dmRun (b s : List Bool) : List Bool :=
  dmStep^[s.length] (pair (pair [] []) b)

/-- The quotient of a length by a fixed divisor, in unary. -/
noncomputable def divFn (b s : List Bool) : List Bool :=
  pairFst (pairFst (dmRun b s))

/-- The remainder of a length by a fixed divisor, in unary. -/
noncomputable def modFn (b s : List Bool) : List Bool :=
  pairSnd (pairFst (dmRun b s))

theorem dmRun_mem_FP (b : List Bool) : dmRun b ∈ FP := by
  have hinit : (fun _ : List Bool => pair (pair [] []) b) ∈ FP := constFn_mem_FP _
  have hwidth : (fun z : List Bool => polyRuler (Polynomial.C 6 * Polynomial.X
      + Polynomial.C (b.length + 6)) (id z)) ∈ FP := polyRulerFn_mem_FP _ id_mem_FP
  have hbound : ∀ z : List Bool, ∀ k ≤ z.length,
      (dmStep^[k] (pair (pair [] []) b)).length
        ≤ (polyRuler (Polynomial.C 6 * Polynomial.X
            + Polynomial.C (b.length + 6)) (id z)).length := by
    intro z k hk
    obtain ⟨q', r', h1, hq, hr⟩ := dmStep_shape k [] [] b
    rw [h1, pair_length, pair_length, polyRuler_length]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, id, List.length_nil, Nat.zero_add] at *
    omega
  have hiter := Cobham.iterate_mem_FP dmStep_mem_FP hinit id_mem_FP hwidth hbound
  exact hiter

theorem divFn_mem_FP (b : List Bool) : divFn b ∈ FP := by
  have := mem_FP_comp (mem_FP_comp (dmRun_mem_FP b) Cobham.fstBlock_mem_FP)
    Cobham.fstBlock_mem_FP
  exact this

theorem modFn_mem_FP (b : List Bool) : modFn b ∈ FP := by
  have := mem_FP_comp (mem_FP_comp (dmRun_mem_FP b) Cobham.fstBlock_mem_FP)
    Cobham.sndBlock_mem_FP
  exact this

theorem divFn_eq {b : List Bool} (hb : 0 < b.length) (s : List Bool) :
    divFn b s = List.replicate (s.length / b.length) true := by
  rw [divFn, dmRun, dmStep_iterate hb s.length, pairFst_pair, pairFst_pair]

theorem modFn_eq {b : List Bool} (hb : 0 < b.length) (s : List Bool) :
    modFn b s = List.replicate (s.length % b.length) true := by
  rw [modFn, dmRun, dmStep_iterate hb s.length, pairFst_pair, pairSnd_pair]

/-! ### Dividing by a length read from the input -/

theorem fstBlock_len_le (z : List Bool) : (pairFst z).length ≤ z.length := by
  induction z using pairFst.induct <;> simp [pairFst] <;> omega

theorem sndBlock_len_le (z : List Bool) : (pairSnd z).length ≤ z.length := by
  rcases hu : unpair? z with _ | ⟨p, q⟩
  · rw [show pairSnd z = [] from by rw [pairSnd, hu]]
    simp
  · have hz : z = pair p q := unpair?_eq_some_iff.mp hu
    rw [show pairSnd z = q from by rw [pairSnd, hu], hz, pair_length]
    omega

/-- The counting run with the divisor read from the argument: `pair b s`. -/
noncomputable def dmRun2 (z : List Bool) : List Bool :=
  dmStep^[(pairSnd z).length] (pair (pair [] []) (pairFst z))

/-- The quotient of one length by another, in unary. -/
noncomputable def divFn2 (z : List Bool) : List Bool :=
  pairFst (pairFst (dmRun2 z))

/-- The remainder of one length by another, in unary. -/
noncomputable def modFn2 (z : List Bool) : List Bool :=
  pairSnd (pairFst (dmRun2 z))

theorem dmRun2_mem_FP : dmRun2 ∈ FP := by
  have hinit : (fun z : List Bool => pair (pair [] []) (pairFst z)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP (pair [] [])) Cobham.fstBlock_mem_FP
  have hwidth : (fun z : List Bool => polyRuler (Polynomial.C 7 * Polynomial.X
      + Polynomial.C 6) (id z)) ∈ FP := polyRulerFn_mem_FP _ id_mem_FP
  have hbound : ∀ z : List Bool, ∀ k ≤ (pairSnd z).length,
      (dmStep^[k] (pair (pair [] []) (pairFst z))).length
        ≤ (polyRuler (Polynomial.C 7 * Polynomial.X + Polynomial.C 6) (id z)).length := by
    intro z k hk
    obtain ⟨q', r', h1, hq, hr⟩ := dmStep_shape k [] [] (pairFst z)
    have hf : (pairFst z).length ≤ z.length := fstBlock_len_le z
    have hs : (pairSnd z).length ≤ z.length := sndBlock_len_le z
    rw [h1, pair_length, pair_length, polyRuler_length]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, id, List.length_nil, Nat.zero_add] at *
    omega
  have hiter := Cobham.iterate_mem_FP dmStep_mem_FP hinit Cobham.sndBlock_mem_FP hwidth hbound
  exact hiter

theorem divFn2_mem_FP : divFn2 ∈ FP := by
  have := mem_FP_comp (mem_FP_comp dmRun2_mem_FP Cobham.fstBlock_mem_FP)
    Cobham.fstBlock_mem_FP
  exact this

theorem modFn2_mem_FP : modFn2 ∈ FP := by
  have := mem_FP_comp (mem_FP_comp dmRun2_mem_FP Cobham.fstBlock_mem_FP)
    Cobham.sndBlock_mem_FP
  exact this

theorem divFn2_eq {b : List Bool} (hb : 0 < b.length) (s : List Bool) :
    divFn2 (pair b s) = List.replicate (s.length / b.length) true := by
  rw [divFn2, dmRun2, pairSnd_pair, pairFst_pair, dmStep_iterate hb s.length,
    pairFst_pair, pairFst_pair]

theorem modFn2_eq {b : List Bool} (hb : 0 < b.length) (s : List Bool) :
    modFn2 (pair b s) = List.replicate (s.length % b.length) true := by
  rw [modFn2, dmRun2, pairSnd_pair, pairFst_pair, dmStep_iterate hb s.length,
    pairFst_pair, pairSnd_pair]

/-- **Halving a length**, in unary. -/
noncomputable def halfFn (s : List Bool) : List Bool := divFn [false, false] s

theorem halfFn_mem_FP : halfFn ∈ FP := divFn_mem_FP _

theorem halfFn_eq (s : List Bool) : halfFn s = List.replicate (s.length / 2) true := by
  rw [halfFn, divFn_eq (by simp)]
  rfl

end Complexity
