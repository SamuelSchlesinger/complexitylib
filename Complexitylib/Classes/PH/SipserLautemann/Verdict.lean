/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham
public import Complexitylib.Classes.P.Cobham.Internal.FstBlock
public import Complexitylib.Classes.P.Cobham.Internal.SndBlock
public import Complexitylib.Classes.P.Cobham.Internal.BlockLoop
public import Complexitylib.Classes.PH.SipserLautemann.Matrix

/-!
# Bridging the string computation and the counting definitions

The amplified verdict is defined by counting blocks of a seed *function*
`Fin (k * T) → Bool` inside a `Finset`; the algebra computes with the seed as a
*string*. This file identifies the two views: a block of the string decodes to
the corresponding block of the function, so the algebra's unary count is the
`blockEventCount` of the amplification lemmas.

## Main results

- `Lautemann.getD_take_drop` — reading inside a block of a string
- `Lautemann.seedOfList_blockAtIdx` — the decoded block is the function's block
- `Lautemann.blockEventCount_seedOfList` — the two counts agree
-/

@[expose] public section

namespace Complexity

namespace Lautemann

variable {k : ℕ}

/-- Reading inside a block of a string reads the underlying string. -/
theorem getD_take_drop (s : List Bool) (a b j : ℕ) (hj : j < b) :
    ((s.drop a).take b).getD j false = s.getD (a + j) false := by
  rw [List.getD, List.getD, List.getElem?_take_of_lt hj, List.getElem?_drop]

/-- The block of a decoded seed is the decoding of the block of the string. -/
theorem seedOfList_blockAtIdx (T : ℕ) (s : List Bool) (i : ℕ) (t : Fin T) :
    seedOfList T (Cobham.blockAtIdx T s i) t = s.getD (i * T + t.val) false := by
  rw [seedOfList, Cobham.blockAtIdx]
  exact getD_take_drop s (i * T) T t.val t.isLt

/-- The blocks of a decoded long seed are the decodings of its string blocks. -/
theorem blocksEquiv_seedOfList (runs T : ℕ) (s : List Bool) (i : Fin runs) :
    blocksEquiv runs T (seedOfList (runs * T) s) i
      = seedOfList T (Cobham.blockAtIdx T s i.val) := by
  funext t
  rw [blocksEquiv_apply, seedOfList_blockAtIdx, seedOfList]
  congr 1
  show t.val + T * i.val = i.val * T + t.val
  rw [Nat.mul_comm]
  omega

/-- Path acceptance is membership of the decoded choice string in the
single-trial accepting event. -/
theorem pathAccepts_iff (tm : NTM k) (x c : List Bool) :
    Cobham.PathAccepts tm x c
      ↔ seedOfList c.length c ∈ NTM.repeatAcceptEvent tm x c.length := by
  have hfun : (fun j : Fin c.length => c[j.val]'j.isLt) = seedOfList c.length c := by
    funext j
    rw [seedOfList, List.getD, List.getElem?_eq_getElem j.isLt, Option.getD_some]
  rw [Cobham.PathAccepts, hfun, NTM.repeatAcceptEvent]
  simp

/-- The block count of a decoded seed is a sum over block indices. -/
theorem blockEventCount_seedOfList {T : ℕ} (E : Finset (Fin T → Bool)) (runs : ℕ)
    (s : List Bool) :
    blockEventCount E (seedOfList (runs * T) s)
      = ∑ j ∈ Finset.range runs,
          (if seedOfList T (Cobham.blockAtIdx T s j) ∈ E then 1 else 0) := by
  rw [blockEventCount, Finset.card_filter, ← Fin.sum_univ_eq_sum_range
    (fun j => if seedOfList T (Cobham.blockAtIdx T s j) ∈ E then 1 else 0) runs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blocksEquiv_seedOfList]

/-- Inside a seed of exactly `runs` blocks, every block is full. -/
theorem blockAtIdx_length (T : ℕ) (s : List Bool) (j runs : ℕ)
    (hs : s.length = runs * T) (hj : j < runs) :
    (Cobham.blockAtIdx T s j).length = T := by
  have hmul : j * T + T ≤ runs * T := by
    have h := Nat.mul_le_mul_right T (Nat.succ_le_of_lt hj)
    rwa [Nat.succ_mul] at h
  rw [Cobham.blockAtIdx, List.length_take, List.length_drop, hs]
  omega

/-- **The algebra's count is the amplification lemmas' block count.** -/
theorem acceptCountAux_length_eq (tm : NTM k) (u x τ s ρ : List Bool) (runs : ℕ)
    (hρ : ρ.length = runs) (hs : s.length = runs * τ.length)
    (hu : x.length + τ.length + Fintype.card tm.Q + 3 ≤ u.length) :
    (Cobham.acceptCountAux tm u x τ s ρ).length
      = blockEventCount (NTM.repeatAcceptEvent tm x τ.length)
          (seedOfList (runs * τ.length) s) := by
  rw [Cobham.acceptCountAux_length, blockEventCount_seedOfList, hρ]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hblen : (Cobham.blockAtIdx τ.length s j).length = τ.length :=
    blockAtIdx_length τ.length s j runs hs hj
  have hacc : Cobham.acceptChoiceFn tm u x (Cobham.blockAtIdx τ.length s j) = [true]
      ↔ seedOfList τ.length (Cobham.blockAtIdx τ.length s j)
          ∈ NTM.repeatAcceptEvent tm x τ.length := by
    rw [Cobham.acceptChoiceFn_eq_true_iff tm u x (Cobham.blockAtIdx τ.length s j)
      (by rw [hblen]; omega), pathAccepts_iff, hblen]
  by_cases h : Cobham.acceptChoiceFn tm u x (Cobham.blockAtIdx τ.length s j) = [true]
  · rw [ite_eq_left h, ite_eq_left (hacc.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun hmem => h (hacc.mpr hmem))]

/-- **The algebra's majority flag is the amplified majority verdict.** -/
theorem majorityFlag_eq_true_iff' (tm : NTM k) (u x τ s ρ : List Bool) (runs : ℕ)
    (hρ : ρ.length = runs) (hs : s.length = runs * τ.length)
    (hu : x.length + τ.length + Fintype.card tm.Q + 3 ≤ u.length) :
    Cobham.majorityFlag tm u x τ s ρ = [true]
      ↔ blockMajority (NTM.repeatAcceptEvent tm x τ.length)
          (seedOfList (runs * τ.length) s) = true := by
  rw [Cobham.majorityFlag_eq_true_iff, acceptCountAux_length_eq tm u x τ s ρ runs hρ hs hu,
    hρ, blockMajority]
  simp only [decide_eq_true_eq]

/-! ## The shift action -/

/-- Reading inside a padded block reads the block. -/
theorem getD_padTo (σ b : List Bool) (j : ℕ) (hj : j < σ.length) :
    (padTo σ b).getD j false = b.getD j false := by
  rcases Nat.lt_or_ge j b.length with hb | hb
  · rw [padTo, List.getD, List.getD, List.getElem?_take_of_lt hj,
      List.getElem?_append_left hb]
  · have h1 : (padTo σ b)[j]? = some false := by
      rw [padTo, List.getElem?_take_of_lt hj,
        List.getElem?_append_right hb, List.getElem?_replicate]
      rw [ite_eq_left (by omega)]
    rw [List.getD, h1, List.getD, List.getElem?_eq_none hb]
    rfl

/-- The decoded exclusive-or is the shift action on decoded seeds. -/
theorem seedOfList_xorSuffix (m : ℕ) (r blk : List Bool) (hr : r.length = m)
    (hblk : blk.length = m) :
    seedOfList m (Cobham.xorSuffix r blk) = shift (seedOfList m r) (seedOfList m blk) := by
  funext j
  rw [Cobham.xorSuffix_eq_zipWith_of_length r blk (by omega), shift, seedOfList,
    seedOfList, seedOfList]
  have hj : j.val < (List.zipWith xor r blk).length := by
    rw [List.length_zipWith]
    omega
  have hjr : j.val < r.length := by omega
  have hjb : j.val < blk.length := by omega
  rw [List.getD, List.getElem?_eq_getElem hj, Option.getD_some, List.getElem_zipWith,
    List.getD, List.getElem?_eq_getElem hjr, Option.getD_some,
    List.getD, List.getElem?_eq_getElem hjb, Option.getD_some]

/-- The decoded padded block is the decoded shift vector. -/
theorem seedOfList_padTo_block (t m : ℕ) (σ w : List Bool) (hσ : σ.length = m)
    (i : Fin t) :
    seedOfList m (padTo σ (Cobham.blockAtIdx m w i.val))
      = shiftsOfList t m w i := by
  funext j
  rw [seedOfList, shiftsOfList, getD_padTo σ _ j.val (by rw [hσ]; exact j.isLt),
    Cobham.blockAtIdx, getD_take_drop w (i.val * m) m j.val j.isLt]

/-! ## The rulers -/

/-- The clock string for the path simulations: long enough for every block. -/
noncomputable def clockStr (pt : Polynomial ℕ) (q : ℕ) (x : List Bool) : List Bool :=
  x ++ (Cobham.polyLen pt x ++ List.replicate (q + 3) false)

@[simp] theorem clockStr_length (pt : Polynomial ℕ) (q : ℕ) (x : List Bool) :
    (clockStr pt q x).length = x.length + pt.eval x.length + (q + 3) := by
  rw [clockStr, List.length_append, List.length_append, Cobham.polyLen_length,
    List.length_replicate]
  omega

/-- The ruler whose length is the number of amplification trials. -/
noncomputable def runsStr (pt : Polynomial ℕ) (x : List Bool) : List Bool :=
  List.replicate 133 false
    ++ Complexity.smash (List.replicate 12 false) (Cobham.polyLen pt x)

@[simp] theorem runsStr_length (pt : Polynomial ℕ) (x : List Bool) :
    (runsStr pt x).length = ampRuns pt.eval x.length := by
  rw [runsStr, List.length_append, List.length_replicate, smash_length,
    List.length_replicate, Cobham.polyLen_length, ampRuns, ampExp]
  ring

/-- The ruler whose length is the amplified seed length. -/
noncomputable def seedStr (pt : Polynomial ℕ) (x : List Bool) : List Bool :=
  Complexity.smash (runsStr pt x) (Cobham.polyLen pt x)

@[simp] theorem seedStr_length (pt : Polynomial ℕ) (x : List Bool) :
    (seedStr pt x).length = ampRuns pt.eval x.length * pt.eval x.length := by
  rw [seedStr, smash_length, runsStr_length, Cobham.polyLen_length]

/-- The ruler whose length is the number of shifts. -/
noncomputable def shiftStr (pt : Polynomial ℕ) (x : List Bool) : List Bool :=
  false :: seedStr pt x

@[simp] theorem shiftStr_length (pt : Polynomial ℕ) (x : List Bool) :
    (shiftStr pt x).length = ampShifts pt.eval x.length := by
  rw [shiftStr, List.length_cons, seedStr_length, ampShifts]

/-! ## The verdict as an algebra function -/

/-- The matrix verdict, computed from the decoded components with the rulers
above: check the seed's length, then take the disjunction over shift blocks of
the amplified majority verdict. -/
noncomputable def matrixFn (tm : NTM k) (pt : Polynomial ℕ) (b : Bool) (z : List Bool) :
    List Bool :=
  caseBit₀
    (Cobham.lenEqFlag (pairSnd z)
      (seedStr pt (pairFst (pairFst z))))
    (Cobham.anyShiftAux tm b
      (clockStr pt (Fintype.card tm.Q) (pairFst (pairFst z)))
      (pairFst (pairFst z))
      (Cobham.polyLen pt (pairFst (pairFst z)))
      (runsStr pt (pairFst (pairFst z)))
      (seedStr pt (pairFst (pairFst z)))
      (pairSnd z) (pairSnd (pairFst z))
      (shiftStr pt (pairFst (pairFst z))))
    [true]

/-- A flag matching a Boolean, in the two polarities. -/
private theorem flag_iff_bool {fl : List Bool} {c b : Bool}
    (hflag : fl = [true] ∨ fl = [false]) (h : fl = [true] ↔ c = true) :
    (bif b then fl else notBit fl) = [true] ↔ c = b := by
  cases b
  · rw [Bool.cond_false, Cobham.notBit_eq_true_iff hflag]
    rcases hflag with hf | hf
    · have hc : c = true := h.mp hf
      rw [hf, hc]
      simp
    · rw [hf]
      simp only [true_iff]
      cases hc : c
      · rfl
      · rw [hc] at h
        exact absurd (h.mpr rfl) (by rw [hf]; simp)
  · rw [Bool.cond_true]
    exact h

/-- **The per-shift verdict is the amplified majority at that shift.** -/
theorem verdictFlag_shift_iff (tm : NTM k) (pt : Polynomial ℕ) (b : Bool)
    (x w r : List Bool)
    (hr : r.length = ampRuns pt.eval x.length * pt.eval x.length)
    (i : Fin (ampShifts pt.eval x.length)) :
    Cobham.verdictFlag tm b (clockStr pt (Fintype.card tm.Q) x) x (Cobham.polyLen pt x)
        (Cobham.xorSuffix r (padTo (seedStr pt x)
          (Cobham.blockAtIdx (seedStr pt x).length w i.val))) (runsStr pt x) = [true]
      ↔ blockMajority (NTM.repeatAcceptEvent tm x (pt.eval x.length))
          (shift (seedOfList (ampRuns pt.eval x.length * pt.eval x.length) r)
            (shiftsOfList (ampShifts pt.eval x.length)
              (ampRuns pt.eval x.length * pt.eval x.length) w i)) = b := by
  have hσ : (seedStr pt x).length = ampRuns pt.eval x.length * pt.eval x.length :=
    seedStr_length pt x
  have hblk : Cobham.blockAtIdx (seedStr pt x).length w i.val
      = Cobham.blockAtIdx (ampRuns pt.eval x.length * pt.eval x.length) w i.val := by
    rw [hσ]
  have hslen : (Cobham.xorSuffix r (padTo (seedStr pt x)
      (Cobham.blockAtIdx (seedStr pt x).length w i.val))).length
      = ampRuns pt.eval x.length * pt.eval x.length := by
    rw [Cobham.xorSuffix_length, hr]
  have hseed : seedOfList (ampRuns pt.eval x.length * pt.eval x.length)
        (Cobham.xorSuffix r (padTo (seedStr pt x)
          (Cobham.blockAtIdx (seedStr pt x).length w i.val)))
      = shift (seedOfList (ampRuns pt.eval x.length * pt.eval x.length) r)
          (shiftsOfList (ampShifts pt.eval x.length)
            (ampRuns pt.eval x.length * pt.eval x.length) w i) := by
    rw [hblk, seedOfList_xorSuffix _ r _ hr (by rw [padTo_length, hσ]),
      seedOfList_padTo_block (ampShifts pt.eval x.length)
        (ampRuns pt.eval x.length * pt.eval x.length) (seedStr pt x) w hσ i]
  have hmaj := majorityFlag_eq_true_iff' tm (clockStr pt (Fintype.card tm.Q) x) x
    (Cobham.polyLen pt x)
    (Cobham.xorSuffix r (padTo (seedStr pt x)
      (Cobham.blockAtIdx (seedStr pt x).length w i.val)))
    (runsStr pt x) (ampRuns pt.eval x.length) (runsStr_length pt x)
    (by rw [hslen, Cobham.polyLen_length])
    (by rw [clockStr_length, Cobham.polyLen_length]; omega)
  rw [Cobham.polyLen_length] at hmaj
  rw [hseed] at hmaj
  exact flag_iff_bool (Cobham.majorityFlag_flag _ _ _ _ _ _) hmaj

/-- The verdict computation on the three decoded components. -/
private theorem matrixFn_aux (tm : NTM k) (pt : Polynomial ℕ) (b : Bool) (x w r : List Bool) :
    caseBit₀ (Cobham.lenEqFlag r (seedStr pt x))
      (Cobham.anyShiftAux tm b (clockStr pt (Fintype.card tm.Q) x) x (Cobham.polyLen pt x)
        (runsStr pt x) (seedStr pt x) r w (shiftStr pt x)) [true]
      = [matrixVerdictOn tm pt.eval b x w r] := by
  rw [matrixVerdictOn]
  by_cases hlen : r.length = ampRuns pt.eval x.length * pt.eval x.length
  · have hflag : Cobham.lenEqFlag r (seedStr pt x) = [true] := by
      rw [Cobham.lenEqFlag_eq_true_iff, seedStr_length]
      exact hlen
    rw [hflag, ite_eq_left hlen, caseBit₀_cons, Bool.cond_true]
    have hiff : Cobham.anyShiftAux tm b (clockStr pt (Fintype.card tm.Q) x) x
        (Cobham.polyLen pt x) (runsStr pt x) (seedStr pt x) r w (shiftStr pt x) = [true]
        ↔ ∃ i : Fin (ampShifts pt.eval x.length),
            blockMajority (NTM.repeatAcceptEvent tm x (pt.eval x.length))
              (shift (seedOfList (ampRuns pt.eval x.length * pt.eval x.length) r)
                (shiftsOfList (ampShifts pt.eval x.length)
                  (ampRuns pt.eval x.length * pt.eval x.length) w i)) = b := by
      rw [Cobham.anyShiftAux_eq_true_iff, shiftStr_length]
      constructor
      · rintro ⟨i, hi, hv⟩
        exact ⟨⟨i, hi⟩, (verdictFlag_shift_iff tm pt b x w r hlen ⟨i, hi⟩).mp hv⟩
      · rintro ⟨i, hb⟩
        exact ⟨i.val, i.isLt, (verdictFlag_shift_iff tm pt b x w r hlen i).mpr hb⟩
    rcases Cobham.anyShiftAux_flag tm b (clockStr pt (Fintype.card tm.Q) x) x
      (Cobham.polyLen pt x) (runsStr pt x) (seedStr pt x) r w (shiftStr pt x) with h | h
    · rw [h, decide_eq_true (hiff.mp h)]
    · rw [h, decide_eq_false ?_]
      intro hex
      rw [hiff.mpr hex] at h
      exact absurd h (by simp)
  · have hflag : Cobham.lenEqFlag r (seedStr pt x) = [false] := by
      rcases Cobham.lenEqFlag_flag r (seedStr pt x) with h | h
      · rw [Cobham.lenEqFlag_eq_true_iff, seedStr_length] at h
        exact absurd h hlen
      · exact h
    rw [hflag, ite_eq_right hlen, caseBit₀_cons, Bool.cond_false]

/-- **The algebra function computes the matrix verdict.** -/
theorem matrixFn_eq (tm : NTM k) (pt : Polynomial ℕ) (b : Bool) (z : List Bool) :
    matrixFn tm pt b z = [matrixVerdict tm pt.eval b z] :=
  matrixFn_aux tm pt b _ _ _

/-! ## Membership in the algebra -/

/-- The pair decoders are in the algebra, being polynomial-time. -/
theorem fstBlock_cobham {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool => pairFst (g v) :=
  (Cobham.comp (FP_subset_CobhamFP Cobham.fstBlock_mem_FP)
    fun _ : Fin 1 => hg).of_eq fun _ => rfl

theorem sndBlock_cobham {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool => pairSnd (g v) :=
  (Cobham.comp (FP_subset_CobhamFP Cobham.sndBlock_mem_FP)
    fun _ : Fin 1 => hg).of_eq fun _ => rfl

theorem clockStr_mem {n : ℕ} (pt : Polynomial ℕ) (q : ℕ)
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool => clockStr pt q (g v) :=
  (Cobham.appendFn hg
    (Cobham.appendFn (Cobham.polyLen_mem pt hg) (Cobham.const _))).of_eq fun _ => rfl

theorem runsStr_mem {n : ℕ} (pt : Polynomial ℕ)
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool => runsStr pt (g v) :=
  (Cobham.appendFn (Cobham.const _)
    (Cobham.comp₂ Cobham.smash (Cobham.const _) (Cobham.polyLen_mem pt hg))).of_eq fun _ => rfl

theorem seedStr_mem {n : ℕ} (pt : Polynomial ℕ)
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool => seedStr pt (g v) :=
  (Cobham.comp₂ Cobham.smash (runsStr_mem pt hg) (Cobham.polyLen_mem pt hg)).of_eq fun _ => rfl

theorem shiftStr_mem {n : ℕ} (pt : Polynomial ℕ)
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool => shiftStr pt (g v) :=
  (Cobham.comp (Cobham.bit false) fun _ : Fin 1 => seedStr_mem pt hg).of_eq fun _ => rfl

/-- **The matrix verdict is in the algebra.** -/
theorem matrixFn_mem (tm : NTM k) (pt : Polynomial ℕ) (b : Bool) :
    Cobham fun v : Fin 1 → List Bool => matrixFn tm pt b (v 0) := by
  have hz : Cobham fun v : Fin 1 → List Bool => v 0 := Cobham.proj 0
  have hx : Cobham fun v : Fin 1 → List Bool =>
      pairFst (pairFst (v 0)) := fstBlock_cobham (fstBlock_cobham hz)
  have hw : Cobham fun v : Fin 1 → List Bool =>
      pairSnd (pairFst (v 0)) := sndBlock_cobham (fstBlock_cobham hz)
  have hr : Cobham fun v : Fin 1 → List Bool => pairSnd (v 0) := sndBlock_cobham hz
  exact (Cobham.iteFn (Cobham.lenEqFlag_mem hr (seedStr_mem pt hx))
    (Cobham.anyShiftAux_mem tm b (clockStr_mem pt (Fintype.card tm.Q) hx) hx
      (Cobham.polyLen_mem pt hx) (runsStr_mem pt hx) (seedStr_mem pt hx) hr hw
      (shiftStr_mem pt hx))
    (Cobham.const [true])).of_eq fun _ => rfl

/-- **The matrix verdict is polynomial-time computable.** -/
theorem matrixVerdict_mem_FP (tm : NTM k) (pt : Polynomial ℕ) (b : Bool) :
    (fun z => [matrixVerdict tm pt.eval b z]) ∈ FP :=
  CobhamFP_subset_FP ((matrixFn_mem tm pt b).of_eq fun v => matrixFn_eq tm pt b (v 0))

end Lautemann

end Complexity
