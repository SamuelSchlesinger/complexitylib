/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitConvolutionUpdates
public import Mathlib.Data.List.Range

/-!
# Unrestricted depth-three lower bound: language bit hash updates

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageBitHashUpdates.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

/-- Accumulate one row of the bit-level hash computation. -/
def hashUpdateRow (u x : List Bool) (i : ℕ) : List ℕ → List Bool → List Bool
  | [], c => c
  | j :: js, c => hashUpdateRow u x i js
      (xorListAt c i (u.getD (i + j) false && x.getD j false))

@[simp] theorem hashUpdateRow_nil (u x : List Bool) (i : ℕ) (c : List Bool) :
    hashUpdateRow u x i [] c = c := rfl

theorem hashUpdateRow_step (u x : List Bool) (i j : ℕ)
    (js : List ℕ) (c : List Bool) :
    hashUpdateRow u x i (j :: js) c = hashUpdateRow u x i js
      (xorListAt c i (u.getD (i + j) false && x.getD j false)) := rfl

@[simp] theorem hashUpdateRow_length (u x : List Bool) (i : ℕ)
    (js : List ℕ) (c : List Bool) :
    (hashUpdateRow u x i js c).length = c.length := by
  induction js generalizing c with
  | nil => rfl
  | cons j js ih => rw [hashUpdateRow_step, ih, xorListAt_length]

theorem hashUpdateRow_append (u x : List Bool) (i : ℕ)
    (js ks : List ℕ) (c : List Bool) :
    hashUpdateRow u x i (js ++ ks) c =
      hashUpdateRow u x i ks (hashUpdateRow u x i js c) := by
  induction js generalizing c with
  | nil => rfl
  | cons j js ih =>
      simp only [List.cons_append, hashUpdateRow_step, ih]

theorem hashUpdateRow_getD (u x : List Bool) (i : ℕ)
    (js : List ℕ) (c : List Bool) (k : ℕ) (hi : i < c.length) :
    (hashUpdateRow u x i js c).getD k false =
      Bool.xor (c.getD k false)
        (if i = k then xorBits (js.map fun j =>
          u.getD (i + j) false && x.getD j false) else false) := by
  induction js generalizing c with
  | nil => simp
  | cons j js ih =>
      have hi' : i <
          (xorListAt c i (u.getD (i + j) false && x.getD j false)).length := by
        simpa only [xorListAt_length] using hi
      rw [hashUpdateRow_step, ih _ hi',
        xorListAt_getD c i (u.getD (i + j) false && x.getD j false) hi k]
      by_cases hik : i = k <;>
        simp [hik, List.map_cons, xorBits_cons]

theorem hashUpdateRow_getD_self (u x : List Bool) (i : ℕ)
    (js : List ℕ) (c : List Bool) (hi : i < c.length) :
    (hashUpdateRow u x i js c).getD i false =
      Bool.xor (c.getD i false)
        (xorBits (js.map fun j => u.getD (i + j) false && x.getD j false)) := by
  simpa only [ite_eq_left rfl, ite_true] using hashUpdateRow_getD u x i js c i hi

theorem hashUpdateRow_getD_ne (u x : List Bool) (i : ℕ)
    (js : List ℕ) (c : List Bool) (k : ℕ) (hi : i < c.length) (hik : i ≠ k) :
    (hashUpdateRow u x i js c).getD k false = c.getD k false := by
  simpa only [ite_eq_right hik, Bool.xor_false] using hashUpdateRow_getD u x i js c k hi

/-- The bit contributed by one hash row at a selected output coordinate. -/
def hashRowBit (u x : List Bool) (i : ℕ) : Bool :=
  xorBits ((List.range x.length).map fun j =>
    u.getD (i + j) false && x.getD j false)

/-- Accumulate the rows of the bit-level hash computation. -/
def hashUpdateRows (u x : List Bool) : List ℕ → List Bool → List Bool
  | [], c => c
  | i :: is, c => hashUpdateRows u x is
      (hashUpdateRow u x i (List.range x.length) c)

@[simp] theorem hashUpdateRows_nil (u x : List Bool) (c : List Bool) :
    hashUpdateRows u x [] c = c := rfl

theorem hashUpdateRows_step (u x : List Bool) (i : ℕ)
    (is : List ℕ) (c : List Bool) :
    hashUpdateRows u x (i :: is) c = hashUpdateRows u x is
      (hashUpdateRow u x i (List.range x.length) c) := rfl

@[simp] theorem hashUpdateRows_length (u x : List Bool)
    (is : List ℕ) (c : List Bool) :
    (hashUpdateRows u x is c).length = c.length := by
  induction is generalizing c with
  | nil => rfl
  | cons i is ih => rw [hashUpdateRows_step, ih, hashUpdateRow_length]

theorem hashUpdateRows_append (u x : List Bool)
    (is ks : List ℕ) (c : List Bool) :
    hashUpdateRows u x (is ++ ks) c =
      hashUpdateRows u x ks (hashUpdateRows u x is c) := by
  induction is generalizing c with
  | nil => rfl
  | cons i is ih =>
      simp only [List.cons_append, hashUpdateRows_step, ih]

theorem hashUpdateRows_getD (u x : List Bool)
    (is : List ℕ) (c : List Bool) (k : ℕ)
    (hbound : ∀ i ∈ is, i < c.length) :
    (hashUpdateRows u x is c).getD k false =
      Bool.xor (c.getD k false)
        (xorBits (is.map fun i => if i = k then hashRowBit u x i else false)) := by
  induction is generalizing c with
  | nil => simp
  | cons i is ih =>
      have hi : i < c.length := hbound i (by simp)
      have hrest : ∀ i' ∈ is,
          i' < (hashUpdateRow u x i (List.range x.length) c).length := by
        intro i' hi'
        rw [hashUpdateRow_length]
        exact hbound i' (List.mem_cons_of_mem i hi')
      rw [hashUpdateRows_step, ih _ hrest,
        hashUpdateRow_getD u x i (List.range x.length) c k hi]
      simp only [hashRowBit, List.map_cons, xorBits_cons, Bool.xor_assoc]

theorem hashUpdateRow_range'_append (u x : List Bool) (i s m n : ℕ) (c : List Bool) :
    hashUpdateRow u x i (List.range' s (m + n)) c =
      hashUpdateRow u x i (List.range' (s + m) n)
        (hashUpdateRow u x i (List.range' s m) c) := by
  rw [← List.range'_append_1, hashUpdateRow_append]

theorem hashUpdateRow_range'_prefix (u x : List Bool) (i s m n : ℕ)
    (c : List Bool) (hm : m ≤ n) :
    hashUpdateRow u x i (List.range' (s + m) (n - m))
        (hashUpdateRow u x i (List.range' s m) c) =
      hashUpdateRow u x i (List.range' s n) c := by
  rw [← hashUpdateRow_range'_append, Nat.add_sub_of_le hm]

theorem hashUpdateRow_range'_step (u x : List Bool) (i s n : ℕ) (c : List Bool) :
    hashUpdateRow u x i (List.range' s (n + 1)) c =
      hashUpdateRow u x i (List.range' (s + 1) n)
        (xorListAt c i (u.getD (i + s) false && x.getD s false)) := by
  rw [List.range'_succ, hashUpdateRow_step]

theorem hashUpdateRow_range'_snoc (u x : List Bool) (i s n : ℕ) (c : List Bool) :
    hashUpdateRow u x i (List.range' s (n + 1)) c =
      xorListAt (hashUpdateRow u x i (List.range' s n) c) i
        (u.getD (i + (s + n)) false && x.getD (s + n) false) := by
  rw [List.range'_concat, hashUpdateRow_append]
  simp only [Nat.one_mul, hashUpdateRow_step, hashUpdateRow_nil]

theorem hashUpdateRows_range'_append (u x : List Bool) (s m n : ℕ) (c : List Bool) :
    hashUpdateRows u x (List.range' s (m + n)) c =
      hashUpdateRows u x (List.range' (s + m) n)
        (hashUpdateRows u x (List.range' s m) c) := by
  rw [← List.range'_append_1, hashUpdateRows_append]

theorem hashUpdateRows_range'_prefix (u x : List Bool) (s m n : ℕ)
    (c : List Bool) (hm : m ≤ n) :
    hashUpdateRows u x (List.range' (s + m) (n - m))
        (hashUpdateRows u x (List.range' s m) c) =
      hashUpdateRows u x (List.range' s n) c := by
  rw [← hashUpdateRows_range'_append, Nat.add_sub_of_le hm]

theorem hashUpdateRows_range'_step (u x : List Bool) (s n : ℕ) (c : List Bool) :
    hashUpdateRows u x (List.range' s (n + 1)) c =
      hashUpdateRows u x (List.range' (s + 1) n)
        (hashUpdateRow u x s (List.range x.length) c) := by
  rw [List.range'_succ, hashUpdateRows_step]

theorem hashUpdateRows_range'_snoc (u x : List Bool) (s n : ℕ) (c : List Bool) :
    hashUpdateRows u x (List.range' s (n + 1)) c =
      hashUpdateRow u x (s + n) (List.range x.length)
        (hashUpdateRows u x (List.range' s n) c) := by
  rw [List.range'_concat, hashUpdateRows_append]
  simp only [Nat.one_mul, hashUpdateRows_step, hashUpdateRows_nil]

theorem hashUpdateRow_range_succ (u x : List Bool) (i j : ℕ) (c : List Bool) :
    hashUpdateRow u x i (List.range (j + 1)) c =
      xorListAt (hashUpdateRow u x i (List.range j) c) i
        (u.getD (i + j) false && x.getD j false) := by
  simpa only [List.range_eq_range', Nat.zero_add] using
    hashUpdateRow_range'_snoc u x i 0 j c

theorem hashUpdateRows_range_succ (u x : List Bool) (i : ℕ) (c : List Bool) :
    hashUpdateRows u x (List.range (i + 1)) c =
      hashUpdateRow u x i (List.range x.length)
        (hashUpdateRows u x (List.range i) c) := by
  simpa only [List.range_eq_range', Nat.zero_add] using
    hashUpdateRows_range'_snoc u x 0 i c

theorem hashReadIndex_lt {d r i j : ℕ} (hi : i < r) (hj : j < d) :
    i + j < d + r - 1 := by omega

private theorem xorBits_map_single_index (is : List ℕ) (hn : is.Nodup)
    (k : ℕ) (f : ℕ → Bool) :
    xorBits (is.map fun i => if i = k then f i else false) =
      if k ∈ is then f k else false := by
  induction is with
  | nil => simp
  | cons i is ih =>
      have hnodup := List.nodup_cons.mp hn
      rw [List.map_cons, xorBits_cons, ih hnodup.2]
      by_cases hik : i = k
      · subst i
        simp [hnodup.1]
      · simp [hik, Ne.symm hik]

theorem hashUpdateRows_getD_nodup (u x : List Bool)
    (is : List ℕ) (c : List Bool) (k : ℕ)
    (hbound : ∀ i ∈ is, i < c.length) (hn : is.Nodup) :
    (hashUpdateRows u x is c).getD k false =
      Bool.xor (c.getD k false) (if k ∈ is then hashRowBit u x k else false) := by
  rw [hashUpdateRows_getD u x is c k hbound,
    xorBits_map_single_index is hn k (hashRowBit u x)]

/-- Compute the binary hash by successive bit-list updates. -/
def hashByUpdates (r : ℕ) (u x : List Bool) : List Bool :=
  hashUpdateRows u x (List.range r) (List.replicate r false)

@[simp] theorem hashByUpdates_length (r : ℕ) (u x : List Bool) :
    (hashByUpdates r u x).length = r := by simp [hashByUpdates]

theorem hashByUpdates_getD (r : ℕ) (u x : List Bool) (k : ℕ) :
    (hashByUpdates r u x).getD k false =
      if k < r then hashRowBit u x k else false := by
  have hbound : ∀ i ∈ List.range r, i < (List.replicate r false).length := by
    intro i hi
    simpa only [List.length_replicate] using List.mem_range.mp hi
  unfold hashByUpdates
  rw [hashUpdateRows_getD_nodup u x (List.range r) (List.replicate r false)
    k hbound List.nodup_range]
  simp

theorem hashRowBit_ofFn {d r : ℕ} (u : BitWord (d + r - 1)) (x : BitWord d)
    (i : Fin r) :
    hashRowBit (List.ofFn u) (List.ofFn x) i.val = wordHash u x i := by
  unfold hashRowBit
  rw [List.length_ofFn, ← ofFn_nat_eq_map_range]
  simp only [wordHash, wordFreeze_eq]
  apply congrArg xorBits
  apply congrArg List.ofFn
  funext j
  have hu : i.val + j.val < d + r - 1 := (BinaryHash.sumIndex i j).is_lt
  change ((wordList u).getD (i.val + j.val) false && (wordList x).getD j.val false) =
    (u (BinaryHash.sumIndex i j) && x j)
  simp only [wordList_getD, wordGet_of_lt u hu, wordGet_fin, BinaryHash.sumIndex]

theorem hashByUpdates_ofFn_eq {d r : ℕ} (u : BitWord (d + r - 1)) (x : BitWord d) :
    hashByUpdates r (List.ofFn u) (List.ofFn x) = List.ofFn (wordHash u x) := by
  apply List.ext_getElem
  · simp
  · intro k hk hl
    have hkr : k < r := by simpa only [List.length_ofFn] using hl
    have hleft := hashByUpdates_getD r (List.ofFn u) (List.ofFn x) k
    rw [ite_eq_left hkr, List.getD_eq_getElem _ _ hk] at hleft
    simpa using hleft.trans (hashRowBit_ofFn u x ⟨k, hkr⟩)

end DepthThreeLowerBound

end Complexity
