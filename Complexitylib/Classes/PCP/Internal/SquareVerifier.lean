/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.PosScan
public import Complexitylib.Classes.EventProb

/-!
# Running a verifier twice

Dinur's amplification leaves a constant gap, which need not be as large as the
one half the `PCP` classes ask for. Independent repetition closes that: two runs
on independent coins reject a non-member with probability `1 - (1 - s)²`, and
repeating the doubling a constant number of times drives the error below any
threshold.

The coin string of the doubled verifier is split by the *per-run* coin count,
a function of the input length, rather than by halving the string. That keeps
the split point polynomial-time computable from the input alone, which is what
the `positions` and `verdict` conditions need.

## Main definitions

- `Complexity.PCPVerifier.squareAt` — two independent runs
- `Complexity.PCPWith` — the class with an explicit soundness error

## Main results

- `Complexity.PCPVerifier.positions_squareAt`,
  `Complexity.PCPVerifier.mem_verdict_squareAt` — what the doubled verifier does
- `Complexity.PCPWith_square`, `Complexity.mem_PCP_of_PCPWith` — any soundness
  error below one can be driven under one half
-/

@[expose] public section

namespace Complexity

namespace PCPVerifier

variable (V : PCPVerifier) (t : ℕ → ℕ)

/-- The coins of the first run. -/
def fstCoins (t : ℕ → ℕ) (x ρ : List Bool) : List Bool := ρ.take (t x.length)

/-- The coins of the second run. -/
def sndCoins (t : ℕ → ℕ) (x ρ : List Bool) : List Bool := ρ.drop (t x.length)

/-- The queries of two independent runs, one after the other. -/
def sqPositions (x ρ : List Bool) : List ℕ :=
  V.positions x (fstCoins t x ρ) ++ V.positions x (sndCoins t x ρ)

/-- The input, out of a verdict argument `pair (pair x ρ) a`. -/
def vX (z : List Bool) : List Bool := pairFst (pairFst z)

/-- The coins, out of a verdict argument. -/
def vR (z : List Bool) : List Bool := pairSnd (pairFst z)

/-- The answers, out of a verdict argument. -/
def vA (z : List Bool) : List Bool := pairSnd z

/-- The verdict of the doubled verifier: both runs accept. The answers of the
first run are the first `|positions|` of them. -/
def sqVerdict : Language :=
  {z | pair (pair (vX z) (fstCoins t (vX z) (vR z)))
        ((vA z).take (V.positions (vX z) (fstCoins t (vX z) (vR z))).length) ∈ V.verdict
    ∧ pair (pair (vX z) (sndCoins t (vX z) (vR z)))
        ((vA z).drop (V.positions (vX z) (fstCoins t (vX z) (vR z))).length) ∈ V.verdict}

/-! ### The pieces are polynomial time -/

section FP

variable {V t}
variable {f : List Bool → List Bool}
variable (ht : (fun x : List Bool => List.replicate (t x.length) true) ∈ FP)

theorem vX_mem_FP : vX ∈ FP := mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP

theorem vR_mem_FP : vR ∈ FP := mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP

theorem vA_mem_FP : vA ∈ FP := Cobham.sndBlock_mem_FP

include ht in
theorem fstCoinsFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => fstCoins t (a z) (b z)) ∈ FP := by
  have hlen : (fun z => List.replicate (t (a z).length) true) ∈ FP := by
    have := mem_FP_comp ha ht
    exact this
  have := Cobham.takeLenFn_mem_FP hlen hb
  refine mem_FP_of_eq this fun z => ?_
  rw [fstCoins, List.length_replicate]

include ht in
theorem sndCoinsFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => sndCoins t (a z) (b z)) ∈ FP := by
  have hlen : (fun z => List.replicate (t (a z).length) true) ∈ FP := by
    have := mem_FP_comp ha ht
    exact this
  have := dropLenFn_mem_FP hlen hb
  refine mem_FP_of_eq this fun z => ?_
  rw [sndCoins, List.length_replicate]

include ht in
/-- The doubled verifier's query list is polynomial-time computable. -/
theorem sqPositions_mem (hf : f ∈ FP)
    (hfspec : ∀ x rr : List Bool,
      f (pair x rr) = DataEncode.bitstringEncode (V.positions x rr)) :
    ∃ g ∈ FP, ∀ x ρ : List Bool,
      g (pair x ρ) = DataEncode.bitstringEncode (sqPositions V t x ρ) := by
  have hx : (fun z : List Bool => pairFst z) ∈ FP := Cobham.fstBlock_mem_FP
  have hr : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
  have h1 : (fun z : List Bool => f (pair (pairFst z)
      (fstCoins t (pairFst z) (pairSnd z)))) ∈ FP := by
    have := mem_FP_comp
      (Cobham.pairFn_mem_FP hx (fstCoinsFn_mem_FP ht hx hr)) hf
    exact this
  have h2 : (fun z : List Bool => f (pair (pairFst z)
      (sndCoins t (pairFst z) (pairSnd z)))) ∈ FP := by
    have := mem_FP_comp
      (Cobham.pairFn_mem_FP hx (sndCoinsFn_mem_FP ht hx hr)) hf
    exact this
  refine ⟨fun z => false :: (posInner (f (pair (pairFst z)
      (fstCoins t (pairFst z) (pairSnd z))))
      ++ posInner (f (pair (pairFst z)
      (sndCoins t (pairFst z) (pairSnd z))))) ++ [true], ?_, ?_⟩
  · have hcat := Cobham.appendFn_mem_FP (posInner_mem_FP h1) (posInner_mem_FP h2)
    have hcons := mem_FP_comp hcat (Cobham.cons_mem_FP false)
    have := Cobham.appendFn_mem_FP hcons (constFn_mem_FP [true])
    refine mem_FP_of_eq this fun z => ?_
    simp
  · intro x ρ
    show false :: (posInner (f (pair (pairFst (pair x ρ))
        (fstCoins t (pairFst (pair x ρ)) (pairSnd (pair x ρ)))))
        ++ posInner (f (pair (pairFst (pair x ρ))
        (sndCoins t (pairFst (pair x ρ)) (pairSnd (pair x ρ)))))) ++ [true]
      = _
    rw [pairFst_pair, pairSnd_pair, hfspec, hfspec, sqPositions,
      bitstringEncode_append]

include ht in
/-- The doubled verifier's verdict is polynomial-time decidable. -/
theorem sqVerdict_mem_P (hf : f ∈ FP)
    (hfspec : ∀ x rr : List Bool,
      f (pair x rr) = DataEncode.bitstringEncode (V.positions x rr)) :
    sqVerdict V t ∈ P := by
  have hc1 : (fun z => fstCoins t (vX z) (vR z)) ∈ FP :=
    fstCoinsFn_mem_FP ht vX_mem_FP vR_mem_FP
  have hc2 : (fun z => sndCoins t (vX z) (vR z)) ∈ FP :=
    sndCoinsFn_mem_FP ht vX_mem_FP vR_mem_FP
  have hfv : (fun z => f (pair (vX z) (fstCoins t (vX z) (vR z)))) ∈ FP := by
    have := mem_FP_comp (Cobham.pairFn_mem_FP vX_mem_FP hc1) hf
    exact this
  have hn : (fun z => posCount (f (pair (vX z) (fstCoins t (vX z) (vR z))))) ∈ FP :=
    posCount_mem_FP hfv
  have hnlen : ∀ z, (posCount (f (pair (vX z) (fstCoins t (vX z) (vR z))))).length
      = (V.positions (vX z) (fstCoins t (vX z) (vR z))).length := by
    intro z
    rw [hfspec, posCount_eq, List.length_replicate]
  have hA : (fun z => pair (pair (vX z) (fstCoins t (vX z) (vR z)))
      ((vA z).take (V.positions (vX z) (fstCoins t (vX z) (vR z))).length)) ∈ FP := by
    have := Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP vX_mem_FP hc1)
      (Cobham.takeLenFn_mem_FP hn vA_mem_FP)
    refine mem_FP_of_eq this fun z => ?_
    rw [hnlen]
  have hB : (fun z => pair (pair (vX z) (sndCoins t (vX z) (vR z)))
      ((vA z).drop (V.positions (vX z) (fstCoins t (vX z) (vR z))).length)) ∈ FP := by
    have := Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP vX_mem_FP hc2)
      (dropLenFn_mem_FP hn vA_mem_FP)
    refine mem_FP_of_eq this fun z => ?_
    rw [hnlen]
  exact P_inter (mem_P_preimage hA V.verdict_mem) (mem_P_preimage hB V.verdict_mem)

end FP

/-- **Two independent runs**, as a verifier in its own right. -/
noncomputable def squareAt (V : PCPVerifier) (t : ℕ → ℕ)
    (ht : (fun x : List Bool => List.replicate (t x.length) true) ∈ FP) : PCPVerifier where
  positions := V.sqPositions t
  positions_mem := by
    obtain ⟨f, hf, hfspec⟩ := V.positions_mem
    exact sqPositions_mem ht hf hfspec
  verdict := V.sqVerdict t
  verdict_mem := by
    obtain ⟨f, hf, hfspec⟩ := V.positions_mem
    exact sqVerdict_mem_P ht hf hfspec

@[simp] theorem positions_squareAt (ht : (fun x : List Bool =>
    List.replicate (t x.length) true) ∈ FP) (x ρ : List Bool) :
    (V.squareAt t ht).positions x ρ = V.sqPositions t x ρ := rfl

theorem mem_verdict_squareAt (ht : (fun x : List Bool =>
    List.replicate (t x.length) true) ∈ FP) (z : List Bool) :
    z ∈ (V.squareAt t ht).verdict ↔ z ∈ V.sqVerdict t := Iff.rfl

/-! ### Splitting the coin string -/

theorem toList_take (a b : ℕ) (ρ : Fin (a + b) → Bool) :
    (BitString.toList ρ).take a = BitString.toList (blockFst a b ρ) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < a := by simpa using h2
  rw [List.getElem_take]
  rw [BitString.getElem_toList ρ ⟨i, by omega⟩,
    BitString.getElem_toList (blockFst a b ρ) ⟨i, hi⟩]
  rfl

theorem toList_drop (a b : ℕ) (ρ : Fin (a + b) → Bool) :
    (BitString.toList ρ).drop a = BitString.toList (blockSnd a b ρ) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < b := by simpa using h2
  rw [List.getElem_drop]
  rw [BitString.getElem_toList ρ ⟨a + i, by omega⟩,
    BitString.getElem_toList (blockSnd a b ρ) ⟨i, hi⟩]
  rfl

/-! ### What the doubled verifier accepts -/

theorem accepts_squareAt (ht : (fun x : List Bool =>
    List.replicate (t x.length) true) ∈ FP) (x π ρ : List Bool) :
    (V.squareAt t ht).Accepts x π ρ
      ↔ V.Accepts x π (fstCoins t x ρ) ∧ V.Accepts x π (sndCoins t x ρ) := by
  have hlen : (answers π (V.positions x (fstCoins t x ρ))).length
      = (V.positions x (fstCoins t x ρ)).length := by
    rw [answers, List.length_map]
  rw [Accepts, positions_squareAt, sqPositions, answers, List.map_append]
  show _ ∈ V.sqVerdict t ↔ _
  rw [sqVerdict, Set.mem_ofPred_eq]
  simp only [vX, vR, vA, pairFst_pair, pairSnd_pair]
  rw [show List.map (fun i => π.getD i false) (V.positions x (fstCoins t x ρ))
        = answers π (V.positions x (fstCoins t x ρ)) from rfl,
    show List.map (fun i => π.getD i false) (V.positions x (sndCoins t x ρ))
        = answers π (V.positions x (sndCoins t x ρ)) from rfl,
    ← hlen, List.take_left, List.drop_left]
  rfl

open Classical in
theorem acceptEvent_squareAt (ht : (fun x : List Bool =>
    List.replicate (t x.length) true) ∈ FP) (x π : List Bool) {T : ℕ}
    (hT : t x.length = T) :
    (V.squareAt t ht).acceptEvent (T + T) x π
      = Finset.univ.filter (fun ρ : Fin (T + T) → Bool =>
          V.Accepts x π (BitString.toList (blockFst T T ρ))
            ∧ V.Accepts x π (BitString.toList (blockSnd T T ρ))) := by
  classical
  ext ρ
  simp only [acceptEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [accepts_squareAt, fstCoins, sndCoins, hT, toList_take, toList_drop]

open Classical in
theorem eventProb_acceptEvent_squareAt (ht : (fun x : List Bool =>
    List.replicate (t x.length) true) ∈ FP) (x π : List Bool) {T : ℕ}
    (hT : t x.length = T) :
    eventProb ((V.squareAt t ht).acceptEvent (T + T) x π)
      = eventProb (V.acceptEvent T x π) * eventProb (V.acceptEvent T x π) := by
  classical
  rw [acceptEvent_squareAt V t ht x π hT]
  rw [eventProb_block (P := fun σ : Fin T → Bool => V.Accepts x π (BitString.toList σ))
    (Q := fun σ : Fin T → Bool => V.Accepts x π (BitString.toList σ))]
  rfl

end PCPVerifier

/-! ### Amplifying the class -/

/-- The `PCP` class with an explicit soundness error. -/
def PCPWith (r q : ℕ → ℕ) (s : ℚ) : Set Language :=
  {L | ∃ V : PCPVerifier, V.QueryBounded q ∧
    (∀ x ∈ L, ∃ π : List Bool, eventProb (V.acceptEvent (r x.length) x π) = 1) ∧
    (∀ x ∉ L, ∀ π : List Bool, eventProb (V.acceptEvent (r x.length) x π) ≤ s)}

theorem PCPWith_half (r q : ℕ → ℕ) : PCPWith r q (1 / 2) = PCP r q := rfl

/-- **Two runs square the error**, at twice the randomness and twice the
queries. -/
theorem PCPWith_square {r q : ℕ → ℕ} {s : ℚ} (hs : 0 ≤ s)
    (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP)
    {L : Language} (hL : L ∈ PCPWith r q s) :
    L ∈ PCPWith (fun n => r n + r n) (fun n => q n + q n) (s * s) := by
  obtain ⟨V, hQ, hcomp, hsound⟩ := hL
  refine ⟨V.squareAt r hr, ?_, ?_, ?_⟩
  · intro x ρ
    rw [PCPVerifier.positions_squareAt, PCPVerifier.sqPositions, List.length_append]
    exact Nat.add_le_add (hQ _ _) (hQ _ _)
  · intro x hx
    obtain ⟨π, hπ⟩ := hcomp x hx
    refine ⟨π, ?_⟩
    rw [PCPVerifier.eventProb_acceptEvent_squareAt V r hr x π rfl, hπ]
    norm_num
  · intro x hx π
    rw [PCPVerifier.eventProb_acceptEvent_squareAt V r hr x π rfl]
    exact mul_le_mul (hsound x hx π) (hsound x hx π) (eventProb_nonneg _) hs

/-! ### Driving the error below one half -/

theorem PCPWith_congr {r r' q q' : ℕ → ℕ} {s : ℚ} (hr : ∀ n, r n = r' n)
    (hq : ∀ n, q n = q' n) : PCPWith r q s = PCPWith r' q' s := by
  have h1 : r = r' := funext hr
  have h2 : q = q' := funext hq
  rw [h1, h2]

theorem PCPWith_mono {r q : ℕ → ℕ} {s s' : ℚ} (h : s ≤ s') :
    PCPWith r q s ⊆ PCPWith r q s' := by
  rintro L ⟨V, hQ, hc, hsound⟩
  exact ⟨V, hQ, hc, fun x hx π => le_trans (hsound x hx π) h⟩

theorem constructible_double {r : ℕ → ℕ}
    (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP) :
    (fun x : List Bool => List.replicate (r x.length + r x.length) true) ∈ FP := by
  have := Cobham.appendFn_mem_FP hr hr
  refine mem_FP_of_eq this fun x => ?_
  rw [← List.replicate_add]

/-- **Repeated doubling.** After `j` doublings the error is `s ^ (2 ^ j)`. -/
theorem PCPWith_iterate (j : ℕ) : ∀ {r q : ℕ → ℕ} {s : ℚ}, 0 ≤ s →
    (fun x : List Bool => List.replicate (r x.length) true) ∈ FP →
    ∀ {L : Language}, L ∈ PCPWith r q s →
      L ∈ PCPWith (fun n => 2 ^ j * r n) (fun n => 2 ^ j * q n) (s ^ 2 ^ j) := by
  induction j with
  | zero =>
      intro r q s _ _ L hL
      rw [PCPWith_congr (r' := r) (q' := q) (fun n => by ring) (fun n => by ring)]
      simpa using hL
  | succ j ih =>
      intro r q s hs hr L hL
      have hsq := PCPWith_square hs hr hL
      have hstep := ih (s := s * s) (by positivity) (constructible_double hr) hsq
      have hr' : ∀ n, 2 ^ j * (r n + r n) = 2 ^ (j + 1) * r n := by
        intro n; ring
      have hq' : ∀ n, 2 ^ j * (q n + q n) = 2 ^ (j + 1) * q n := by
        intro n; ring
      rw [PCPWith_congr hr' hq'] at hstep
      have hpow : (s * s) ^ 2 ^ j = s ^ 2 ^ (j + 1) := by
        rw [← sq, ← pow_mul, pow_succ]
        ring_nf
      rwa [hpow] at hstep

/-- **Any error below one can be driven under one half.** -/
theorem mem_PCP_of_PCPWith {r q : ℕ → ℕ} {s : ℚ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP)
    {L : Language} (hL : L ∈ PCPWith r q s) :
    ∃ j : ℕ, L ∈ PCP (fun n => 2 ^ j * r n) (fun n => 2 ^ j * q n) := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℚ) < 1 / 2) hs1
  refine ⟨m, ?_⟩
  have hle : s ^ 2 ^ m ≤ s ^ m := by
    refine pow_le_pow_of_le_one hs0 (le_of_lt hs1) ?_
    exact Nat.le_of_lt (Nat.lt_two_pow_self)
  rw [← PCPWith_half]
  exact PCPWith_mono (le_trans hle (le_of_lt hm)) (PCPWith_iterate m hs0 hr hL)

end Complexity
