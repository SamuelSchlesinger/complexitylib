/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitConvolutionUpdates

/-!
# Unrestricted depth-three lower bound: language bit reduction loop

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageBitReductionLoop.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

/-- Apply the shifted-modulus updates used in coefficient cancellation. -/
def modulusUpdateLoop (p : List Bool) (v : Bool) (shift : ℕ) : ℕ → List Bool → List Bool
  | 0, c => c
  | j + 1, c => xorListAt (modulusUpdateLoop p v shift j c)
      (shift + j) (v && p.getD j false)

@[simp] theorem modulusUpdateLoop_zero (p : List Bool) (v : Bool)
    (shift : ℕ) (c : List Bool) : modulusUpdateLoop p v shift 0 c = c := rfl

theorem modulusUpdateLoop_step (p : List Bool) (v : Bool) (shift j : ℕ) (c : List Bool) :
    modulusUpdateLoop p v shift (j + 1) c =
      xorListAt (modulusUpdateLoop p v shift j c) (shift + j) (v && p.getD j false) := rfl

@[simp] theorem modulusUpdateLoop_length (p : List Bool) (v : Bool)
    (shift j : ℕ) (c : List Bool) :
    (modulusUpdateLoop p v shift j c).length = c.length := by
  induction j with
  | zero => rfl
  | succ j ih => rw [modulusUpdateLoop_step, xorListAt_length, ih]

theorem modulusUpdateLoop_getD (p : List Bool) (v : Bool) (shift j : ℕ)
    (c : List Bool) (hbound : shift + j ≤ c.length) (k : ℕ) :
    (modulusUpdateLoop p v shift j c).getD k false =
      Bool.xor (c.getD k false)
        (if shift ≤ k ∧ k < shift + j then v && p.getD (k - shift) false else false) := by
  revert hbound
  induction j with
  | zero =>
      intro hbound
      have hk : ¬(shift ≤ k ∧ k < shift + 0) := by omega
      simp only [modulusUpdateLoop_zero, ite_eq_right hk, Bool.xor_false]
  | succ j ih =>
      intro hbound
      have hj : shift + j < (modulusUpdateLoop p v shift j c).length := by
        rw [modulusUpdateLoop_length]
        omega
      rw [modulusUpdateLoop_step, xorListAt_getD _ _ _ hj k, ih (by omega)]
      by_cases he : shift + j = k
      · have hprev : ¬(shift ≤ k ∧ k < shift + j) := by omega
        have hnext : shift ≤ k ∧ k < shift + (j + 1) := by omega
        have hsub : k - shift = j := by omega
        simp [he, hnext, hsub]
      · have hrange : (shift ≤ k ∧ k < shift + (j + 1)) ↔
            (shift ≤ k ∧ k < shift + j) := by omega
        simp only [ite_eq_right he, Bool.xor_false, hrange]

theorem modulusUpdateLoop_above (p : List Bool) (v : Bool) (shift j : ℕ)
    (c : List Bool) (hbound : shift + j ≤ c.length) (k : ℕ) (hk : shift + j ≤ k) :
    (modulusUpdateLoop p v shift j c).getD k false = c.getD k false := by
  rw [modulusUpdateLoop_getD p v shift j c hbound k]
  have hnot : ¬(shift ≤ k ∧ k < shift + j) := by omega
  simp only [ite_eq_right hnot, Bool.xor_false]

theorem modulusUpdateLoop_high (p : List Bool) (v : Bool) (shift : ℕ)
    (c : List Bool) (hbound : shift + p.length ≤ c.length) :
    (modulusUpdateLoop p v shift p.length c).getD (shift + p.length) false =
      c.getD (shift + p.length) false :=
  modulusUpdateLoop_above p v shift p.length c hbound _ le_rfl

/-- Cancel a leading coefficient through list updates. -/
def cancelByUpdates (p c : List Bool) (shift : ℕ) : List Bool :=
  (modulusUpdateLoop p (c.getD (shift + p.length) false) shift p.length c).set
    (shift + p.length) false

@[simp] theorem cancelByUpdates_length (p c : List Bool) (shift : ℕ) :
    (cancelByUpdates p c shift).length = c.length := by
  simp [cancelByUpdates]

theorem cancelByUpdates_getD (p c : List Bool) (shift : ℕ)
    (hbound : shift + p.length < c.length) (k : ℕ) :
    (cancelByUpdates p c shift).getD k false =
      if shift + p.length = k then false else
        Bool.xor (c.getD k false)
          (if shift ≤ k ∧ k < shift + p.length then
            c.getD (shift + p.length) false && p.getD (k - shift) false else false) := by
  have ht : shift + p.length <
      (modulusUpdateLoop p (c.getD (shift + p.length) false) shift p.length c).length := by
    simpa only [modulusUpdateLoop_length] using hbound
  by_cases he : shift + p.length = k
  · subst k
    rw [ite_eq_left rfl]
    unfold cancelByUpdates
    exact List.getD_eq_getElem?_getD.trans
      (congrArg (fun o : Option Bool => o.getD false)
        (List.getElem?_set_self (a := false) ht))
  · have hset : (cancelByUpdates p c shift).getD k false =
        (modulusUpdateLoop p (c.getD (shift + p.length) false) shift p.length c).getD k false := by
      simp only [cancelByUpdates, List.getD_eq_getElem?_getD, List.getElem?_set_ne he]
    rw [hset, modulusUpdateLoop_getD _ _ _ _ _ (Nat.le_of_lt hbound) k, ite_eq_right he]

/-- Compute the polynomial remainder through cancellation updates. -/
def reduceByUpdates (p : List Bool) : ℕ → List Bool → List Bool
  | 0, c => c
  | s + 1, c => reduceByUpdates p s (cancelByUpdates p c s)

@[simp] theorem reduceByUpdates_zero (p c : List Bool) : reduceByUpdates p 0 c = c := rfl

theorem reduceByUpdates_step (p c : List Bool) (s : ℕ) :
    reduceByUpdates p (s + 1) c = reduceByUpdates p s (cancelByUpdates p c s) := rfl

@[simp] theorem reduceByUpdates_length (p c : List Bool) (s : ℕ) :
    (reduceByUpdates p s c).length = c.length := by
  induction s generalizing c with
  | zero => rfl
  | succ s ih => rw [reduceByUpdates_step, ih, cancelByUpdates_length]

theorem cancelStep_read {r m : ℕ} (p : BitWord r) (a : BitWord m)
    (shift : ℕ) (hbound : shift + r < m) (i : Fin m) :
    cancelStep p (shift + r) a i =
      if shift + r = i.val then false else
        Bool.xor (a i)
          (if shift ≤ i.val ∧ i.val < shift + r then
            a ⟨shift + r, hbound⟩ && wordGet p (i.val - shift) else false) := by
  by_cases he : shift + r = i.val
  · rw [ite_eq_left he, he]
    exact cancelStep_at p a i (by omega)
  · have hk : r ≤ shift + r ∧ shift + r < m := ⟨by omega, hbound⟩
    have hsub : shift + r - r = shift := by omega
    by_cases ht : a ⟨shift + r, hbound⟩ = true
    · by_cases hw : shift ≤ i.val ∧ i.val < shift + r
      · have hj : i.val - shift < r := by omega
        simp [cancelStep, hk, ht, wordXor, shiftModulus, hsub,
          he, Ne.symm he, hw, wordGet, hj]
      · simp [cancelStep, hk, ht, wordXor, shiftModulus, hsub,
          he, Ne.symm he, hw]
    · have hf : a ⟨shift + r, hbound⟩ = false := Bool.eq_false_of_not_eq_true ht
      simp [cancelStep, hk, ht, he]

theorem cancelByUpdates_eq_cancelStep {r m : ℕ} (p : BitWord r) (a : BitWord m)
    (shift : ℕ) (hbound : shift + r < m) :
    cancelByUpdates (wordList p) (wordList a) shift =
      wordList (cancelStep p (shift + r) a) := by
  have hw : listWord m (cancelByUpdates (wordList p) (wordList a) shift) =
      cancelStep p (shift + r) a := by
    funext i
    change (cancelByUpdates (wordList p) (wordList a) shift).getD i.val false = _
    rw [cancelByUpdates_getD _ _ _ (by simpa only [wordList_length] using hbound)]
    rw [cancelStep_read p a shift hbound i]
    simp only [wordList_length, wordList_getD, wordGet_fin, wordGet_of_lt a hbound]
  calc
    cancelByUpdates (wordList p) (wordList a) shift =
        wordList (listWord m (cancelByUpdates (wordList p) (wordList a) shift)) :=
      (wordList_listWord _ (by simp)).symm
    _ = wordList (cancelStep p (shift + r) a) := congrArg wordList hw

theorem reduceLoop_below {r m : ℕ} (p : BitWord r) (k : ℕ) (a : BitWord m)
    (hk : k ≤ r) : reduceLoop p k a = a := by
  revert hk
  induction k generalizing a with
  | zero => intro hk; rfl
  | succ k ih =>
      intro hk
      have hskip : ¬(r ≤ k ∧ k < m) := by omega
      simpa only [reduceLoop, cancelStep, dite_eq_right hskip] using ih a (by omega)

theorem reduceByUpdates_word_eq {r m : ℕ} (p : BitWord r) (s : ℕ)
    (a : BitWord m) (hbound : r + s ≤ m) :
    reduceByUpdates (wordList p) s (wordList a) =
      wordList (reduceLoop p (r + s) a) := by
  revert hbound
  induction s generalizing a with
  | zero =>
      intro hbound
      simp only [reduceByUpdates_zero, Nat.add_zero, reduceLoop_below p r a le_rfl]
  | succ s ih =>
      intro hbound
      have hs : s + r < m := by omega
      have hs' : r + s ≤ m := by omega
      have hnext : r + (s + 1) = (r + s) + 1 := by omega
      calc
        reduceByUpdates (wordList p) (s + 1) (wordList a) =
            reduceByUpdates (wordList p) s (wordList (cancelStep p (s + r) a)) := by
          rw [reduceByUpdates_step, cancelByUpdates_eq_cancelStep p a s hs]
        _ = wordList (reduceLoop p (r + s) (cancelStep p (s + r) a)) := ih _ hs'
        _ = wordList (reduceLoop p (r + (s + 1)) a) := by
          rw [hnext, reduceLoop, Nat.add_comm s r]

theorem reduceByUpdates_eq_reduceLoop (p c : List Bool) (s : ℕ)
    (hbound : p.length + s ≤ c.length) :
    reduceByUpdates p s c =
      wordList (reduceLoop (listWord p.length p) (p.length + s) (listWord c.length c)) := by
  simpa only [wordList_listWord_length] using
    reduceByUpdates_word_eq (listWord p.length p) s (listWord c.length c) hbound

theorem reduceByUpdates_tail_false (p c : List Bool) (s : ℕ)
    (hfull : p.length + s = c.length) (i : ℕ) (hi : p.length ≤ i) :
    (reduceByUpdates p s c).getD i false = false := by
  rw [reduceByUpdates_eq_reduceLoop p c s (by omega), hfull, wordList_getD]
  by_cases him : i < c.length
  · rw [wordGet_of_lt _ him]
    exact reduceLoop_tail_false (listWord p.length p) c.length (listWord c.length c)
      (by
        intro j _ hj
        exact False.elim (Nat.not_le.mpr j.is_lt hj)) ⟨i, him⟩ hi
  · exact wordGet_of_le _ (Nat.le_of_not_lt him)

theorem wordList_wordResize_take {r m : ℕ} (a : BitWord m) (hr : r ≤ m) :
    wordList (wordResize r a) = (wordList a).take r := by
  apply List.ext_getElem
  · simp only [wordList_length, List.length_take, Nat.min_eq_left hr]
  · intro i hi hj
    have hir : i < r := by simpa only [wordList_length] using hi
    have hleft : (wordList (wordResize r a)).getD i false = wordGet a i := by
      rw [wordList_getD, wordGet_of_lt _ hir]
      rfl
    have hright : ((wordList a).take r).getD i false = wordGet a i := by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hir] using
        wordList_getD a i
    rw [List.getD_eq_getElem _ false hi] at hleft
    rw [List.getD_eq_getElem _ false hj] at hright
    exact hleft.trans hright.symm

theorem reduceByUpdates_take_eq_wordReduce (p c : List Bool)
    (hwidth : c.length = p.length + p.length) :
    (reduceByUpdates p p.length c).take p.length =
      wordList (wordReduce (listWord p.length p) (listWord c.length c)) := by
  rw [reduceByUpdates_eq_reduceLoop p c p.length (by omega), ← hwidth]
  rw [wordReduce, wordFreeze_eq, wordList_wordResize_take _ (by omega)]

theorem reduceByUpdates_convolve_eq_multiplyBitLists (r : ℕ) (p a b : List Bool)
    (hp : p.length = r) (ha : a.length = r) (hb : b.length = r) :
    (reduceByUpdates p r (convolveBitLists a b)).take r = multiplyBitLists r p a b := by
  have hwidth : (convolveBitLists a b).length = p.length + p.length := by
    simp only [convolveBitLists_length, ha, hb, hp]
  have h := reduceByUpdates_take_eq_wordReduce p (convolveBitLists a b) hwidth
  rw [convolveBitLists_length, hp] at h
  rw [convolveBitLists_eq, ha, hb] at h ⊢
  simpa only [listWord_wordList, multiplyBitLists, wordMulMod] using h

theorem reduceByUpdates_convolveByUpdates_eq_multiplyBitLists (r : ℕ)
    (p a b : List Bool) (hp : p.length = r) (ha : a.length = r) (hb : b.length = r) :
    (reduceByUpdates p r (convolveByUpdates a b)).take r = multiplyBitLists r p a b := by
  rw [convolveByUpdates_eq]
  exact reduceByUpdates_convolve_eq_multiplyBitLists r p a b hp ha hb

end DepthThreeLowerBound

end Complexity
