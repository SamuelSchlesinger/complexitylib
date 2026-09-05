/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.PosScan
public import Complexitylib.Classes.PCP.Internal.UnaryExp
public import Complexitylib.Classes.PCP.Internal.BoundedQuant

/-!
# The witness layout of a PCP verifier

A witness for a PCP verifier is a table of answers, one fixed-width block per
coin string. This module fixes that layout and reads it back: the block for a
coin string, cut down to the number of queries actually made, is exactly the
answer list `SubsetNP.tableOf` names.

It also records that the query bound can be taken to be a *constant*. A bound
`q =O 1` need not be a computable function, but it is eventually bounded and
takes finitely many values before that, so a single number bounds every query
list — which is what an algorithm can actually use.

## Main definitions

- `Complexity.wBlock` — the witness block for one coin string

## Main results

- `Complexity.exists_const_query_bound` — a constant bounds every query list
- `Complexity.tableOf_eq_wBlock` — the block is the answer list
- `Complexity.accLang_mem_P` — checking every coin string is polynomial time
-/

@[expose] public section

namespace Complexity

open scoped Complexity in
/-- **A constant bounds every query list.** This is what makes the witness
layout uniform: each block has the same fixed width. -/
theorem exists_const_query_bound {V : PCPVerifier} {q : ℕ → ℕ}
    (hV : V.QueryBounded q) (hq : q =O fun _ => 1) :
    ∃ K : ℕ, ∀ x ρ : List Bool, (V.positions x ρ).length ≤ K := by
  rw [BigO, Asymptotics.isBigO_iff] at hq
  obtain ⟨C, hC⟩ := hq
  rw [Filter.eventually_atTop] at hC
  obtain ⟨N, hN⟩ := hC
  refine ⟨max ⌈C⌉₊ ((Finset.range (N + 1)).sup q), fun x ρ => ?_⟩
  refine le_trans (hV x ρ) ?_
  by_cases h : x.length < N + 1
  · exact le_trans (Finset.le_sup (f := q) (Finset.mem_range.mpr h)) (le_max_right _ _)
  · have hb := hN x.length (by omega)
    simp only [Real.norm_natCast, Nat.cast_one, norm_one, mul_one] at hb
    have hqc : q x.length ≤ ⌈C⌉₊ := by exact_mod_cast le_trans hb (Nat.le_ceil C)
    exact le_trans hqc (le_max_left _ _)

/-- The witness block starting at `start` and holding `len` answers. -/
def wBlock (w : List Bool) (start len : ℕ) : List Bool := (w.drop start).take len

theorem wBlock_mem_FP {w s l : List Bool → List Bool}
    (hw : w ∈ FP) (hs : s ∈ FP) (hl : l ∈ FP) :
    (fun z => wBlock (w z) (s z).length (l z).length) ∈ FP :=
  Cobham.takeLenFn_mem_FP hl (dropLenFn_mem_FP hs hw)

theorem length_wBlock {w : List Bool} {start len : ℕ} (h : start + len ≤ w.length) :
    (wBlock w start len).length = len := by
  rw [wBlock, List.length_take, List.length_drop]
  omega

theorem getElem_wBlock {w : List Bool} {start len : ℕ} (h : start + len ≤ w.length)
    {i : ℕ} (hi : i < len) :
    (wBlock w start len)[i]'(by rw [length_wBlock h]; exact hi) = w.getD (start + i) false := by
  have hlt : start + i < w.length := by omega
  simp only [wBlock]
  rw [List.getElem_take, List.getElem_drop]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  rfl

/-- **The block is the answer list.** With the answers for coin index `c` laid
out in the slots `c * Q, …`, the witness block is exactly the table
`SubsetNP.tableOf` reads. -/
theorem tableOf_eq_wBlock (V : PCPVerifier) (t Q : ℕ) (x w : List Bool)
    (ρ : Fin t → Bool)
    (h : PCPVerifier.coinIndex ρ * Q + (V.positions x (BitString.toList ρ)).length
      ≤ w.length) :
    V.tableOf t Q x w ρ
      = wBlock w (PCPVerifier.coinIndex ρ * Q)
          (V.positions x (BitString.toList ρ)).length := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · rw [V.length_tableOf t Q x w ρ, length_wBlock h]
  · have hi : i < (V.positions x (BitString.toList ρ)).length := by
      rwa [V.length_tableOf t Q x w ρ] at h1
    rw [getElem_wBlock h hi]
    show (List.map _ (List.range _))[i] = _
    erw [List.getElem_map, List.getElem_range]

/-- A one-bit block is the bit it holds. -/
theorem wBlock_one {w : List Bool} {k : ℕ} (h : k < w.length) :
    wBlock w k 1 = [w.getD k false] := by
  rw [wBlock, List.drop_eq_getElem_cons h]
  simp only [List.take_succ_cons, List.take_zero]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- Reading a slot of the table. -/
theorem getElem?_tableOf (V : PCPVerifier) (t Q : ℕ) (x w : List Bool)
    (ρ : Fin t → Bool) {i : ℕ} (hi : i < (V.positions x (BitString.toList ρ)).length) :
    (V.tableOf t Q x w ρ)[i]? = some (w.getD (PCPVerifier.coinIndex ρ * Q + i) false) := by
  rw [PCPVerifier.tableOf, List.getElem?_map, List.getElem?_range hi]
  rfl

/-! ### Acceptance on every coin string

The check is a loop over coin indices. Each iteration recovers the coin string
from its index, reads the verifier's query list to learn how many answers this
coin string uses, cuts that many out of the witness block, and asks the verdict.
-/

section Acceptance

variable (V : PCPVerifier) (f : List Bool → List Bool) (r : ℕ → ℕ) (Q : ℕ)

/-- The input of one iteration is `pair (pair x w) (unary c)`. -/
def accX (y : List Bool) : List Bool := pairFst (pairFst y)

/-- The witness, out of the iteration's input. -/
def accW (y : List Bool) : List Bool := pairSnd (pairFst y)

/-- The coin string named by the iteration's index. -/
noncomputable def accCoin (y : List Bool) : List Bool :=
  coinStr (r (accX y).length) (pairSnd y).length

/-- The verifier's view: input and coins paired with the answers read off the
witness block. -/
noncomputable def accView (y : List Bool) : List Bool :=
  pair (pair (accX y) (accCoin r y))
    (wBlock (accW y) ((pairSnd y).length * Q)
      (posCount (f (pair (accX y) (accCoin r y)))).length)

theorem accX_mem_FP : accX ∈ FP :=
  mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP

theorem accW_mem_FP : accW ∈ FP :=
  mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP

theorem accCoin_mem_FP
    (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP) :
    accCoin r ∈ FP := by
  have ht : (fun y : List Bool => List.replicate (r (accX y).length) true) ∈ FP := by
    have := mem_FP_comp accX_mem_FP hr
    exact this
  have hc : (fun y : List Bool => List.replicate (pairSnd y).length true) ∈ FP := by
    have := mem_FP_comp Cobham.sndBlock_mem_FP unaryLength_mem_FP
    exact this
  exact coinStr_mem_FP ht hc

theorem accView_mem_FP (hf : f ∈ FP)
    (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP) :
    accView f r Q ∈ FP := by
  have hcoin := accCoin_mem_FP r hr
  have hview : (fun y => pair (accX y) (accCoin r y)) ∈ FP :=
    Cobham.pairFn_mem_FP accX_mem_FP hcoin
  have hfv : (fun y => f (pair (accX y) (accCoin r y))) ∈ FP := by
    have := mem_FP_comp hview hf
    exact this
  have hcount : (fun y => posCount (f (pair (accX y) (accCoin r y)))) ∈ FP :=
    posCount_mem_FP hfv
  have hoff : (fun y : List Bool =>
      List.replicate ((pairSnd y).length * Q) false) ∈ FP := by
    have hb : (fun _ : List Bool => List.replicate Q false) ∈ FP :=
      Cobham.const_replicate_mem_FP Q
    have := Cobham.mulLenFn_mem_FP Cobham.sndBlock_mem_FP hb
    refine mem_FP_of_eq this fun y => ?_
    rw [List.length_replicate]
  have hblk : (fun y => wBlock (accW y)
      (List.replicate ((pairSnd y).length * Q) false).length
      (posCount (f (pair (accX y) (accCoin r y)))).length) ∈ FP :=
    wBlock_mem_FP accW_mem_FP hoff hcount
  refine Cobham.pairFn_mem_FP hview (mem_FP_of_eq hblk fun y => ?_)
  rw [List.length_replicate]

/-- One iteration's condition: the verifier accepts the view. -/
noncomputable def accInner : Language := accView f r Q ⁻¹' V.verdict

theorem accInner_mem_P (hf : f ∈ FP)
    (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP) :
    accInner V f r Q ∈ P :=
  mem_P_preimage (accView_mem_FP f r Q hf hr) V.verdict_mem

/-- **Acceptance on every coin string**, as a language of `pair x w`. -/
noncomputable def accLang : Language :=
  {z : List Bool | ∀ c < 2 ^ r (pairFst z).length,
    pair z (List.replicate c true) ∈ accInner V f r Q}

open scoped Complexity in
theorem accLang_mem_P (hf : f ∈ FP)
    (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP)
    (hrlog : r =O fun n => Nat.log 2 n) :
    accLang V f r Q ∈ P := by
  have hlen : (fun z : List Bool =>
      List.replicate (2 ^ r (pairFst z).length) true) ∈ FP := by
    have := mem_FP_comp Cobham.fstBlock_mem_FP (unaryExp_mem_FP_of_bigO_log hr hrlog)
    exact this
  exact forall_unary_mem_P (accInner_mem_P V f r Q hf hr) hlen

/-- What one iteration looks at, on a well-formed input. -/
theorem accView_pair
    (hfspec : ∀ x rr : List Bool,
      f (pair x rr) = DataEncode.bitstringEncode (V.positions x rr))
    {x w : List Bool} {c : ℕ} (hc : c < 2 ^ r x.length)
    (hw : w.length = 2 ^ r x.length * Q)
    (hQ : ∀ rr : List Bool, (V.positions x rr).length ≤ Q) :
    accView f r Q (pair (pair x w) (List.replicate c true))
      = pair (pair x (BitString.toList (PCPVerifier.coinOfIndex (t := r x.length) ⟨c, hc⟩)))
          (V.tableOf (r x.length) Q x w
            (PCPVerifier.coinOfIndex (t := r x.length) ⟨c, hc⟩)) := by
  set ρ := PCPVerifier.coinOfIndex (t := r x.length) ⟨c, hc⟩ with hρ
  have hX : accX (pair (pair x w) (List.replicate c true)) = x := by
    rw [accX, pairFst_pair, pairFst_pair]
  have hW : accW (pair (pair x w) (List.replicate c true)) = w := by
    rw [accW, pairFst_pair, pairSnd_pair]
  have hC : (pairSnd (pair (pair x w) (List.replicate c true))).length = c := by
    rw [pairSnd_pair, List.length_replicate]
  have hcoin : accCoin r (pair (pair x w) (List.replicate c true)) = BitString.toList ρ := by
    rw [accCoin, hX, hC, coinStr_eq hc, hρ, toList_coinOfIndex]
  have hidx : PCPVerifier.coinIndex ρ = c := coinIndex_coinOfIndex _
  have hlen : (posCount (f (pair x (BitString.toList ρ)))).length
      = (V.positions x (BitString.toList ρ)).length := by
    rw [hfspec, posCount_eq, List.length_replicate]
  have hfit : PCPVerifier.coinIndex ρ * Q
      + (V.positions x (BitString.toList ρ)).length ≤ w.length := by
    rw [hidx, hw]
    have h1 : c + 1 ≤ 2 ^ r x.length := hc
    have h2 : (V.positions x (BitString.toList ρ)).length ≤ Q := hQ _
    calc c * Q + (V.positions x (BitString.toList ρ)).length
        ≤ c * Q + Q := by omega
      _ = (c + 1) * Q := by ring
      _ ≤ 2 ^ r x.length * Q := Nat.mul_le_mul_right _ h1
  rw [accView, hX, hW, hC, hcoin, hlen, ← hidx, ← tableOf_eq_wBlock V _ _ _ _ _ hfit]

/-- **Acceptance on every coin string.** -/
theorem mem_accLang_iff
    (hfspec : ∀ x rr : List Bool,
      f (pair x rr) = DataEncode.bitstringEncode (V.positions x rr))
    {x w : List Bool} (hw : w.length = 2 ^ r x.length * Q)
    (hQ : ∀ rr : List Bool, (V.positions x rr).length ≤ Q) :
    pair x w ∈ accLang V f r Q
      ↔ ∀ ρ : Fin (r x.length) → Bool,
          pair (pair x (BitString.toList ρ)) (V.tableOf (r x.length) Q x w ρ) ∈ V.verdict := by
  have hfst : pairFst (pair x w) = x := pairFst_pair x w
  constructor
  · intro h ρ
    have hc : PCPVerifier.coinIndex ρ < 2 ^ r x.length := PCPVerifier.coinIndex_lt ρ
    have := h (PCPVerifier.coinIndex ρ) (by rwa [hfst])
    rw [accInner, Set.mem_preimage, accView_pair V f r Q hfspec hc hw hQ,
      PCPVerifier.coinOfIndex_coinIndex ρ hc] at this
    exact this
  · intro h c hc
    rw [hfst] at hc
    rw [accInner, Set.mem_preimage, accView_pair V f r Q hfspec hc hw hQ]
    exact h _

end Acceptance

end Complexity
