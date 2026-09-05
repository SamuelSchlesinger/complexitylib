/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.UnaryList
public import Complexitylib.Classes.PCP.Internal.ListEncode
public import Complexitylib.Classes.PCP.Internal.PositionsFP

/-!
# Writing out a table

Every stage of an algorithmic reduction writes a list: the edges of a graph, the
entries of a rotation table, the records of a gadget. `ListEncode` runs the loop
that does it, but asks for a bound on the loop's own state; this module
discharges that bound from the rule alone, since a polynomial-time rule has
polynomially bounded output and the loop runs no more often than its argument is
long.

## Main results

- `Complexity.materialize_mem_FP` — a record rule makes the list encoder
  polynomial time
- `Complexity.materialize_eq` — and it writes the list it is meant to
- `Complexity.countOver`, `Complexity.length_countOver` — the same loop used to
  add up a rule's outputs, which is how a bounded count is taken
- `Complexity.findFirst`, `Complexity.length_findFirst` — and, run twice, how a
  bounded search is made
- `Complexity.ifEqLen`, `Complexity.ifLtLen` — comparing two unary numbers, and
  branching on the answer
- `Complexity.length_findFirst_eq` — the search returns the least index the rule
  answers at
-/

@[expose] public section

namespace Complexity

/-- **A record rule materializes a list in polynomial time.** No bound need be
supplied: a polynomial-time rule already has polynomially bounded output, and
the loop runs only as many times as its own argument is long. -/
theorem materialize_mem_FP {E : List Bool → List Bool} (hE : E ∈ FP) : listEncFn E ∈ FP := by
  obtain ⟨q, hq⟩ := Cobham.output_length_poly_of_mem_FP hE
  set Q : Polynomial ℕ := q.comp (3 * Polynomial.X + Polynomial.C 2) with hQ
  refine listEncFn_mem_FP hE
    (4 * Polynomial.X * Q + 3 * Polynomial.X + Polynomial.C 6) fun z k hk => ?_
  have hfz : (pairFst z).length ≤ z.length := fstBlock_length_le z
  have hsz : (pairSnd z).length ≤ z.length := sndBlock_length_le z
  have hkz : k ≤ z.length := le_trans hk hfz
  have hrec : ∀ i < k, (E (pair (pairSnd z) (List.replicate i true))).length
      ≤ Q.eval z.length := by
    intro i hi
    refine le_trans (hq _) ?_
    have hlen : (pair (pairSnd z) (List.replicate i true)).length
        ≤ 3 * z.length + 2 := by
      rw [pair_length, List.length_replicate]
      omega
    have := polynomial_eval_mono_nat q hlen
    rw [hQ, Polynomial.eval_comp]
    simpa using this
  have hcat : (entryCat E (pairSnd z) k).length ≤ k * Q.eval z.length :=
    length_entryCat_le E _ _ k hrec
  have hstate : ((listStep E)^[k] (pair (pair [] []) (pairSnd z))).length
      = 2 * (2 * (entryCat E (pairSnd z) k).length + 2 + k) + 2
        + (pairSnd z).length := by
    rw [listStep_iterate, pair_length, pair_length, List.length_replicate]
  have heval : (4 * Polynomial.X * Q + 3 * Polynomial.X + Polynomial.C 6).eval z.length
      = 4 * (z.length * Q.eval z.length) + 3 * z.length + 6 := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hC : (entryCat E (pairSnd z) k).length ≤ z.length * Q.eval z.length :=
    le_trans hcat (Nat.mul_le_mul_right _ hkz)
  rw [hstate, heval]
  set A := z.length * Q.eval z.length with hA
  omega

/-- **The list encoder writes the list.** -/
theorem materialize_eq {α : Type} [DataEncode α] {E : List Bool → List Bool}
    (l : List α) (x : List Bool)
    (h : ∀ i, ∀ hi : i < l.length,
      E (pair x (List.replicate i true)) = DataEncode.bitstringEncode (l[i]'hi)) :
    listEncFn E (pair (List.replicate l.length true) x) = DataEncode.bitstringEncode l :=
  listEncFn_eq_bitstringEncode l (by rw [pairFst_pair, List.length_replicate])
    (by rw [pairSnd_pair]; exact h)

/-! ### Adding up -/

theorem length_entryCat (E : List Bool → List Bool) (x : List Bool) (n : ℕ) :
    (entryCat E x n).length
      = ∑ i ∈ Finset.range n, (E (pair x (List.replicate i true))).length := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [entryCat_succ, List.length_append, ih, Finset.sum_range_succ]

/-- The total length of a rule's outputs over a range, in unary. Running the
rule for its length alone is how a loop counts: a rule that answers `[true]` or
`[]` counts the indices where it says yes. -/
noncomputable def countOver (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  marks (dropOne (dropOne (listEncFn E z)))

theorem countOver_mem_FP {E : List Bool → List Bool} (hE : E ∈ FP) : countOver E ∈ FP :=
  marks_mem_FP (dropOneFn_mem_FP (dropOneFn_mem_FP (materialize_mem_FP hE)))

theorem length_countOver (E : List Bool → List Bool) (x : List Bool) (n : ℕ) :
    (countOver E (pair (List.replicate n true) x)).length
      = ∑ i ∈ Finset.range n, (E (pair x (List.replicate i true))).length := by
  rw [countOver, marks_eq, List.length_replicate, dropOne, dropOne, List.length_drop,
    List.length_drop, listEncFn_eq, pairFst_pair, pairSnd_pair,
    List.length_replicate, List.length_append, List.length_cons, length_entryCat]
  simp

/-! ### Comparing -/

/-- `x` when the two strings have the same length, `y` otherwise. -/
noncomputable def ifEqLen (a b x y : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.emptyFlag (b.drop a.length ++ a.drop b.length)) x y

theorem ifEqLen_pos {a b : List Bool} (h : a.length = b.length) (x y : List Bool) :
    ifEqLen a b x y = x := by
  have hb : b.drop a.length = [] := by
    refine List.eq_nil_of_length_eq_zero ?_
    rw [List.length_drop, h]
    omega
  have ha : a.drop b.length = [] := by
    refine List.eq_nil_of_length_eq_zero ?_
    rw [List.length_drop, h]
    omega
  rw [ifEqLen, hb, ha, List.append_nil, Cobham.selectHead_emptyFlag_nil]

theorem ifEqLen_neg {a b : List Bool} (h : a.length ≠ b.length) (x y : List Bool) :
    ifEqLen a b x y = y := by
  have hne : b.drop a.length ++ a.drop b.length ≠ [] := by
    intro hnil
    have h1 := List.append_eq_nil_iff.mp hnil
    have hb : (b.drop a.length).length = 0 := by rw [h1.1]; rfl
    have ha : (a.drop b.length).length = 0 := by rw [h1.2]; rfl
    rw [List.length_drop] at ha hb
    omega
  obtain ⟨c, t, hct⟩ : ∃ c t, b.drop a.length ++ a.drop b.length = c :: t := by
    cases hcase : b.drop a.length ++ a.drop b.length with
    | nil => exact absurd hcase hne
    | cons c t => exact ⟨c, t, rfl⟩
  rw [ifEqLen, hct, Cobham.selectHead_emptyFlag_cons]

theorem ifEqLen_mem_FP {a b x y : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hx : x ∈ FP) (hy : y ∈ FP) : (fun z => ifEqLen (a z) (b z) (x z) (y z)) ∈ FP := by
  have hd1 := dropLenFn_mem_FP ha hb
  have hd2 := dropLenFn_mem_FP hb ha
  exact Cobham.selectHeadFn_mem_FP
    (Cobham.emptyFlag_mem_FP (Cobham.appendFn_mem_FP hd1 hd2)) hx hy

/-- `x` when the first string is shorter than the second, `y` otherwise. -/
noncomputable def ifLtLen (a b x y : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.emptyFlag (b.drop a.length)) y x

theorem ifLtLen_pos {a b : List Bool} (h : a.length < b.length) (x y : List Bool) :
    ifLtLen a b x y = x := by
  obtain ⟨c, t, hct⟩ : ∃ c t, b.drop a.length = c :: t := by
    cases hcase : b.drop a.length with
    | nil =>
        have : (b.drop a.length).length = 0 := by rw [hcase]; rfl
        rw [List.length_drop] at this
        omega
    | cons c t => exact ⟨c, t, rfl⟩
  rw [ifLtLen, hct, Cobham.selectHead_emptyFlag_cons]

theorem ifLtLen_neg {a b : List Bool} (h : ¬ a.length < b.length) (x y : List Bool) :
    ifLtLen a b x y = y := by
  have hb : b.drop a.length = [] := by
    refine List.eq_nil_of_length_eq_zero ?_
    rw [List.length_drop]
    omega
  rw [ifLtLen, hb, Cobham.selectHead_emptyFlag_nil]

theorem ifLtLen_mem_FP {a b x y : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hx : x ∈ FP) (hy : y ∈ FP) : (fun z => ifLtLen (a z) (b z) (x z) (y z)) ∈ FP :=
  Cobham.selectHeadFn_mem_FP
    (Cobham.emptyFlag_mem_FP (dropLenFn_mem_FP ha hb)) hy hx

/-- The count is written in marks. -/
theorem countOver_eq_replicate (E : List Bool → List Bool) (z : List Bool) :
    countOver E z = List.replicate (countOver E z).length true := by
  conv_lhs => rw [countOver, marks_eq]
  rw [countOver, marks_eq, List.length_replicate]

/-! ### Searching -/

/-- One mark when the string is empty, none otherwise. -/
noncomputable def isEmptyMark (s : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.emptyFlag s) [true] []

@[simp] theorem isEmptyMark_nil : isEmptyMark [] = [true] :=
  Cobham.selectHead_emptyFlag_nil _ _

@[simp] theorem isEmptyMark_cons (b : Bool) (t : List Bool) : isEmptyMark (b :: t) = [] :=
  Cobham.selectHead_emptyFlag_cons _ _ _ _

theorem length_isEmptyMark (s : List Bool) :
    (isEmptyMark s).length = if s = [] then 1 else 0 := by
  cases s with
  | nil => simp
  | cons b t => simp

theorem isEmptyMark_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => isEmptyMark (f z)) ∈ FP :=
  Cobham.selectHeadFn_mem_FP (Cobham.emptyFlag_mem_FP hf) (constFn_mem_FP [true])
    (constFn_mem_FP [])

/-- The least index below the bound at which the rule answers something, or the
bound itself when it never does: count the indices no answer has been seen up
to. -/
noncomputable def findFirst (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  countOver (fun w =>
    isEmptyMark (countOver E (pair (pairSnd w ++ [true]) (pairFst w)))) z

theorem findFirst_mem_FP {E : List Bool → List Bool} (hE : E ∈ FP) : findFirst E ∈ FP := by
  have harg := Cobham.pairFn_mem_FP
    (Cobham.appendFn_mem_FP Cobham.sndBlock_mem_FP (constFn_mem_FP [true]))
    Cobham.fstBlock_mem_FP
  have hcount : countOver E ∈ FP := countOver_mem_FP hE
  have hcomp : (fun w : List Bool =>
      countOver E (pair (pairSnd w ++ [true]) (pairFst w))) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp harg hcount) fun _ => rfl
  exact countOver_mem_FP (isEmptyMark_mem_FP hcomp)

/-- The search's answer is written in marks. -/
theorem findFirst_eq_replicate (E : List Bool → List Bool) (z : List Bool) :
    findFirst E z = List.replicate (findFirst E z).length true := by
  conv_lhs => rw [findFirst, countOver_eq_replicate]
  rw [← findFirst]

theorem length_findFirst (E : List Bool → List Bool) (x : List Bool) (n : ℕ) :
    (findFirst E (pair (List.replicate n true) x)).length
      = ∑ j ∈ Finset.range n,
          if (∑ k ∈ Finset.range (j + 1), (E (pair x (List.replicate k true))).length) = 0
            then 1 else 0 := by
  rw [findFirst, length_countOver]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pairSnd_pair, pairFst_pair, ← List.replicate_succ',
    length_isEmptyMark]
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

end Complexity
