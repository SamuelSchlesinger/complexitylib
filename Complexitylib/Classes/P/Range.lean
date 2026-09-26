/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Range.Defs
public import Complexitylib.Encoding.DataEncode
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Complexitylib.Classes.P.PairWithInput
import Complexitylib.Classes.P.UnaryLength
import Complexitylib.Classes.P.Range.Internal

/-!
# Polynomial-time loops over a range of indices

Many polynomial-time functions are easiest to describe one index at a time: the
encodings of these entries, one after another; the number of indices at which a
test passes; the least such index; the largest of these values. A loop over the
indices `0, 1, …, n - 1` is given by a rule `E`, which reads `pair z (1^i)` (the
loop's input `z` and the index `i` in unary) and outputs what the loop
contributes at index `i`. The loops read the count and the input from one string
`pair (1^n) z`. Counts, indices and values are written in unary, as strings of
`true`s whose length is the number.

The one construction is **concatenation over a range** (`catRange_mem_FP`): if
the rule is polynomial-time, then so is running it on every index below the
count and concatenating the outputs. No bound on the loop's state has to be
supplied, because a polynomial-time rule has polynomially long outputs and the
loop runs at most as often as its argument is long. The rest are corollaries:
the count may be any polynomial-time function of the input
(`flatMap_range_mem_FP`), and the encoding of a list (`listEncFn_mem_FP`), a
count (`countOver_mem_FP`), a bounded search (`findFirst_mem_FP`), a maximum
(`maxFn_mem_FP`) and a function given one output bit at a time
(`bitwise_mem_FP`) are all polynomial-time.

## Main results

- `catRange_mem_FP` — concatenation over a range is polynomial-time
- `flatMap_range_mem_FP` — the same, over a range given by a polynomial-time
  count
- `listEncFn_mem_FP`, `listEncFn_eq_bitstringEncode` — writing the encoding of
  a list from a rule for its entries
- `countOver_mem_FP`, `length_countOver` — the total output length, in unary
- `findFirst_mem_FP`, `length_findFirst_eq` — the least index at which the rule
  outputs anything
- `maxFn_mem_FP`, `maxFn_eq` — the greatest output length
- `bitwise_mem_FP` — a function given by its length and a rule for each bit
-/

@[expose] public section

namespace Complexity

/-! ## Concatenation -/

/-- On `pair (1^n) x`, concatenation over a range runs the rule on `pair x (1^i)`
for each `i < n`. -/
@[simp] theorem catRange_pair (E : List Bool → List Bool) (x : List Bool) (n : ℕ) :
    catRange E (pair (List.replicate n true) x)
      = (List.range n).flatMap fun i => E (pair x (List.replicate i true)) := by
  rw [catRange, pairFst_pair, pairSnd_pair, List.length_replicate]

/-- The length of a concatenation over a range is the sum of the output
lengths. -/
theorem length_catRange_pair (E : List Bool → List Bool) (x : List Bool) (n : ℕ) :
    (catRange E (pair (List.replicate n true) x)).length
      = ∑ i ∈ Finset.range n, (E (pair x (List.replicate i true))).length := by
  rw [catRange_eq_entryCat, pairFst_pair, pairSnd_pair, List.length_replicate,
    length_entryCat]

/-- **Concatenation over a range is polynomial-time.** If the rule `E` is
polynomial-time, then so is the map from `pair u z` to the outputs of `E` on
`pair z (1^i)` for `i < |u|`, concatenated. -/
theorem catRange_mem_FP {E : List Bool → List Bool} (hE : E ∈ FP) : catRange E ∈ FP :=
  catRange_mem_FP_internal hE

/-- **Concatenation over a polynomial-time range.** If `E` and `m` are
polynomial-time, then so is `z ↦ E ⟨z, 1^0⟩ E ⟨z, 1^1⟩ ⋯ E ⟨z, 1^(|m z| - 1)⟩`. -/
theorem flatMap_range_mem_FP {E m : List Bool → List Bool} (hE : E ∈ FP) (hm : m ∈ FP) :
    (fun z => (List.range (m z).length).flatMap fun i =>
      E (pair z (List.replicate i true))) ∈ FP := by
  refine mem_FP_of_eq (mem_FP_comp (mem_FP_pairWithInput hm) (catRange_mem_FP hE))
    fun z => ?_
  rw [Function.comp_apply, catRange, pairFst_pair, pairSnd_pair]

/-! ## Encoding a list -/

/-- **The list encoder is polynomial-time** whenever its rule is. -/
theorem listEncFn_mem_FP {E : List Bool → List Bool} (hE : E ∈ FP) : listEncFn E ∈ FP :=
  mem_FP_of_eq (Cobham.appendFn_mem_FP
    (mem_FP_comp (catRange_mem_FP hE) (Cobham.cons_mem_FP false))
    (constFn_mem_FP [true])) fun _ => rfl

/-- **The list encoder writes the list.** If the count is the length of `l` and
the rule writes the encoding of each entry of `l`, then the encoder writes the
encoding of `l`. -/
theorem listEncFn_eq_bitstringEncode {α : Type} [DataEncode α]
    {E : List Bool → List Bool} {z : List Bool} (l : List α)
    (hn : (pairFst z).length = l.length)
    (h : ∀ i, ∀ hi : i < l.length,
      E (pair (pairSnd z) (List.replicate i true))
        = DataEncode.bitstringEncode (l[i]'hi)) :
    listEncFn E z = DataEncode.bitstringEncode l := by
  rw [listEncFn_eq, hn, ← bitstringEncode_of_entries l h]

/-! ## Counting -/

/-- **Counting over a range is polynomial-time.** -/
theorem countOver_mem_FP {E : List Bool → List Bool} (hE : E ∈ FP) : countOver E ∈ FP :=
  mem_FP_comp (catRange_mem_FP hE) unaryLength_mem_FP

/-- The count is the sum of the output lengths. -/
theorem length_countOver (E : List Bool → List Bool) (x : List Bool) (n : ℕ) :
    (countOver E (pair (List.replicate n true) x)).length
      = ∑ i ∈ Finset.range n, (E (pair x (List.replicate i true))).length := by
  rw [countOver, List.length_replicate, length_catRange_pair]

/-- The count is written in marks. -/
theorem countOver_eq_replicate (E : List Bool → List Bool) (z : List Bool) :
    countOver E z = List.replicate (countOver E z).length true := by
  rw [countOver, List.length_replicate]

/-! ## Searching -/

@[simp] theorem isEmptyMark_nil : isEmptyMark [] = [true] := rfl

@[simp] theorem isEmptyMark_cons (b : Bool) (t : List Bool) : isEmptyMark (b :: t) = [] :=
  rfl

theorem length_isEmptyMark (s : List Bool) :
    (isEmptyMark s).length = if s = [] then 1 else 0 := by
  cases s <;> rfl

theorem isEmptyMark_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => isEmptyMark (f z)) ∈ FP :=
  isEmptyMark_mem_FP_internal hf

/-- **Searching over a range is polynomial-time.** -/
theorem findFirst_mem_FP {E : List Bool → List Bool} (hE : E ∈ FP) : findFirst E ∈ FP := by
  have harg := Cobham.pairFn_mem_FP
    (Cobham.appendFn_mem_FP Cobham.sndBlock_mem_FP (constFn_mem_FP [true]))
    Cobham.fstBlock_mem_FP
  have hcomp : (fun w : List Bool =>
      countOver E (pair (pairSnd w ++ [true]) (pairFst w))) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp harg (countOver_mem_FP hE)) fun _ => rfl
  exact countOver_mem_FP (isEmptyMark_mem_FP hcomp)

/-- The search's answer is written in marks. -/
theorem findFirst_eq_replicate (E : List Bool → List Bool) (z : List Bool) :
    findFirst E z = List.replicate (findFirst E z).length true := by
  rw [findFirst, countOver, List.length_replicate]

/-- The search counts the indices `j` at which the rule has output nothing on the
indices up to `j`. -/
theorem length_findFirst (E : List Bool → List Bool) (x : List Bool) (n : ℕ) :
    (findFirst E (pair (List.replicate n true) x)).length
      = ∑ j ∈ Finset.range n,
          if (∑ k ∈ Finset.range (j + 1), (E (pair x (List.replicate k true))).length) = 0
            then 1 else 0 := by
  rw [findFirst, length_countOver]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pairSnd_pair, pairFst_pair, ← List.replicate_succ', length_isEmptyMark]
  by_cases h : (∑ k ∈ Finset.range (j + 1), (E (pair x (List.replicate k true))).length) = 0
  · rw [ite_eq_left h, ite_eq_left]
    have := length_countOver E x (j + 1)
    exact List.eq_nil_of_length_eq_zero (by rw [this, h])
  · rw [ite_eq_right h, ite_eq_right]
    intro hnil
    exact h (by rw [← length_countOver E x (j + 1), hnil, List.length_nil])

/-- **The search returns the least index the rule answers at.** -/
theorem length_findFirst_eq {E : List Bool → List Bool} {x : List Bool} {n c : ℕ}
    (hc : c < n) (hhit : (E (pair x (List.replicate c true))).length ≠ 0)
    (hmin : ∀ k < c, (E (pair x (List.replicate k true))).length = 0) :
    (findFirst E (pair (List.replicate n true) x)).length = c := by
  classical
  rw [length_findFirst]
  have hterm : ∀ j ∈ Finset.range n,
      (if (∑ k ∈ Finset.range (j + 1), (E (pair x (List.replicate k true))).length) = 0
          then 1 else 0)
        = (if j < c then 1 else 0) := by
    intro j _
    by_cases hj : j < c
    · rw [ite_eq_left hj, ite_eq_left]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_range] at hk
      exact hmin k (by omega)
    · rw [ite_eq_right hj, ite_eq_right]
      intro hzero
      refine hhit ?_
      have hcm : c ∈ Finset.range (j + 1) := Finset.mem_range.mpr (by omega)
      exact (Finset.sum_eq_zero_iff.mp hzero) c hcm
  rw [Finset.sum_congr rfl hterm, ← Finset.card_filter]
  have hfilter : (Finset.range n).filter (fun j => j < c) = Finset.range c := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter, Finset.card_range]

/-! ## The maximum -/

/-- Every value is at most the maximum. -/
theorem le_maxOver {f : List Bool → List Bool} {z : List Bool} :
    ∀ (n i : ℕ), i < n → (f (pair z (List.replicate i true))).length ≤ maxOver f z n := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      rw [maxOver]
      rcases Nat.lt_or_ge i n with h | h
      · exact le_trans (ih i h) (le_max_left _ _)
      · have : i = n := by omega
        subst this
        exact le_max_right _ _

/-- The maximum is attained, when there is anything to maximise over. -/
theorem maxOver_attained {f : List Bool → List Bool} {z : List Bool} :
    ∀ n : ℕ, 0 < n →
      ∃ i < n, (f (pair z (List.replicate i true))).length = maxOver f z n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        refine ⟨0, by omega, ?_⟩
        rw [maxOver, maxOver]
        simp
      · obtain ⟨i, hi, hval⟩ := ih hn
        rw [maxOver]
        rcases Nat.lt_or_ge (maxOver f z n) (f (pair z (List.replicate n true))).length with h | h
        · refine ⟨n, by omega, ?_⟩
          rw [max_eq_right (le_of_lt h)]
        · refine ⟨i, by omega, ?_⟩
          rw [hval, max_eq_left h]

/-- The maximum is at most any common bound on the values. -/
theorem maxOver_le {f : List Bool → List Bool} {z : List Bool} {B : ℕ} :
    ∀ n, (∀ i < n, (f (pair z (List.replicate i true))).length ≤ B) → maxOver f z n ≤ B := by
  intro n
  induction n with
  | zero => intro _; simp [maxOver]
  | succ n ih =>
      intro h
      rw [maxOver, max_le_iff]
      exact ⟨ih fun i hi => h i (by omega), h n (by omega)⟩

/-- **Taking a maximum over a range is polynomial-time.** -/
theorem maxFn_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) : maxFn f ∈ FP := by
  refine mem_FP_of_eq (mem_FP_comp (mem_FP_pairWithInput (countOver_mem_FP hf))
    (countOver_mem_FP (maxProbe_mem_FP hf))) fun z => ?_
  unfold maxFn
  rfl

/-- **`maxFn` computes the maximum**, in unary. -/
theorem maxFn_eq (f : List Bool → List Bool) {n : ℕ} {z : List Bool} :
    (maxFn f (pair (List.replicate n true) z)).length = maxOver f z n := by
  classical
  set S := (catRange f (pair (List.replicate n true) z)).length with hS
  have hle : maxOver f z n ≤ S := maxOver_le n fun i hi => by
    rw [hS, length_catRange_pair]
    exact Finset.single_le_sum (f := fun i => (f (pair z (List.replicate i true))).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
  change (countOver (maxProbe f)
    (pair (List.replicate S true) (pair (List.replicate n true) z))).length = _
  rw [length_countOver, Finset.sum_congr rfl fun j _ => length_maxProbe_pair f z n j,
    ← Finset.card_filter]
  have hfilter : (Finset.range S).filter (fun j => j < maxOver f z n)
      = Finset.range (maxOver f z n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter, Finset.card_range]

/-! ## One bit at a time -/

/-- **A function described bit by bit is polynomial-time.** If the output length
is computable in unary and each output bit is computable from the input and the
position in unary, the function itself is in `FP`. -/
theorem bitwise_mem_FP {len : List Bool → ℕ} {b : List Bool → ℕ → Bool}
    (hlen : (fun x => List.replicate (len x) true) ∈ FP)
    {G : List Bool → List Bool} (hG : G ∈ FP)
    (hGspec : ∀ x i, G (pair x (List.replicate i true)) = [b x i]) :
    (fun x => (List.range (len x)).map (b x)) ∈ FP := by
  refine mem_FP_of_eq (flatMap_range_mem_FP hG hlen) fun x => ?_
  simp only [List.length_replicate, hGspec]
  exact List.map_eq_flatMap.symm

end Complexity
