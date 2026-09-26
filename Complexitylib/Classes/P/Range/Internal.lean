/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.Range.Defs
public import Complexitylib.Encoding.DataEncode
public import Complexitylib.Classes.P.Iterate
public import Complexitylib.Classes.P.Cobham.Internal
public import Complexitylib.Classes.Containments.Internal.FPBridge

/-!
# Loops over a range of indices — proof internals

The helper facts behind `Complexitylib.Classes.P.Range`. Concatenation over a
range is a loop whose state carries the output so far, the index in unary, and
the input; `iterate_mem_FP_of_polyBound` runs it, and the bound on its state
comes from the rule alone, since a polynomial-time rule has polynomially long
outputs and the loop runs at most as often as its argument is long. The rest is
the one-bit marks, and the arithmetic behind computing a maximum as a count.

## Contents

- `listStep`, `listStep_iterate` — the loop and what it accumulates
- `entryCat` — the accumulated output, indexed by the number of rounds
- `bitstringEncode_of_entries` — accumulating entry encodings encodes the list
- `catRange_mem_FP_internal` — concatenation over a range is polynomial-time
- `isEmptyMark_mem_FP_internal`, `nonemptyMark_mem_FP` — the one-bit marks
- `maxProbe_mem_FP`, `length_maxProbe_pair` — the test behind `maxFn`
-/

@[expose] public section

namespace Complexity

/-! ## The loop -/

/-- One step: append the next entry's encoding and advance the counter. The
state is `pair (pair accumulated counter) input`. -/
def listStep (E : List Bool → List Bool) (st : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst st)
      ++ E (pair (pairSnd st) (pairSnd (pairFst st))))
    (true :: pairSnd (pairFst st))) (pairSnd st)

theorem listStep_mem_FP {E : List Bool → List Bool} (hE : E ∈ FP) : listStep E ∈ FP := by
  have hacc : (fun st : List Bool => pairFst (pairFst st)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hctr : (fun st : List Bool => pairSnd (pairFst st)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hx : (fun st : List Bool => pairSnd st) ∈ FP := Cobham.sndBlock_mem_FP
  have hE' : (fun st : List Bool =>
      E (pair (pairSnd st) (pairSnd (pairFst st)))) ∈ FP :=
    mem_FP_comp (Cobham.pairFn_mem_FP hx hctr) hE
  exact Cobham.pairFn_mem_FP
    (Cobham.pairFn_mem_FP (Cobham.appendFn_mem_FP hacc hE')
      (mem_FP_comp hctr (Cobham.cons_mem_FP true))) hx

/-- The bits the loop has accumulated after `n` steps. -/
def entryCat (E : List Bool → List Bool) (x : List Bool) (n : ℕ) : List Bool :=
  (List.range n).flatMap fun i => E (pair x (List.replicate i true))

@[simp] theorem entryCat_zero (E : List Bool → List Bool) (x : List Bool) :
    entryCat E x 0 = [] := by
  rw [entryCat]
  simp

theorem entryCat_succ (E : List Bool → List Bool) (x : List Bool) (n : ℕ) :
    entryCat E x (n + 1) = entryCat E x n ++ E (pair x (List.replicate n true)) := by
  rw [entryCat, entryCat, List.range_succ, List.flatMap_append]
  simp

/-- Concatenation over a range is the loop's accumulation after as many rounds
as the count is long. -/
theorem catRange_eq_entryCat (E : List Bool → List Bool) (w : List Bool) :
    catRange E w = entryCat E (pairSnd w) (pairFst w).length := rfl

/-- **What the loop accumulates.** -/
theorem listStep_iterate (E : List Bool → List Bool) (x : List Bool) :
    ∀ n : ℕ, (listStep E)^[n] (pair (pair [] []) x)
      = pair (pair (entryCat E x n) (List.replicate n true)) x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, listStep, pairFst_pair,
        pairSnd_pair, pairFst_pair, pairSnd_pair,
        entryCat_succ, List.replicate_succ]

theorem length_entryCat_le (E : List Bool → List Bool) (x : List Bool) (b : ℕ) :
    ∀ n, (∀ i < n, (E (pair x (List.replicate i true))).length ≤ b) →
      (entryCat E x n).length ≤ n * b := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro h
      have hih := ih fun i hi => h i (by omega)
      rw [entryCat_succ, List.length_append]
      have hn := h n (by omega)
      have hexp : (n + 1) * b = n * b + b := by ring
      omega

theorem length_entryCat (E : List Bool → List Bool) (x : List Bool) (n : ℕ) :
    (entryCat E x n).length
      = ∑ i ∈ Finset.range n, (E (pair x (List.replicate i true))).length := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [entryCat_succ, List.length_append, ih, Finset.sum_range_succ]

/-- **Concatenation over a range is polynomial-time.** The loop's state after
`k` rounds holds `k` outputs of `E`, each polynomially long in `|z|`, and `k` is
at most `|z|`, so the states are polynomially bounded. -/
theorem catRange_mem_FP_internal {E : List Bool → List Bool} (hE : E ∈ FP) :
    catRange E ∈ FP := by
  obtain ⟨q, hq⟩ := Cobham.output_length_poly_of_mem_FP hE
  have hQ : PolyBound fun n => q.eval (3 * n + 2) :=
    (PolyBound.eval (q.comp (Polynomial.C 3 * Polynomial.X + Polynomial.C 2))).mono
      fun n => by simp [Polynomial.eval_comp]
  have hB : PolyBound fun n => 4 * (n * q.eval (3 * n + 2)) + 3 * n + 6 :=
    (((PolyBound.const 4).mul (PolyBound.id.mul hQ)).add
      ((PolyBound.const 3).mul PolyBound.id)).add (PolyBound.const 6)
  have hinit : (fun z : List Bool => pair (pair [] []) (pairSnd z)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP (pair [] [])) Cobham.sndBlock_mem_FP
  have hbound : ∀ z : List Bool, ∀ k ≤ (pairFst z).length,
      ((listStep E)^[k] (pair (pair [] []) (pairSnd z))).length
        ≤ 4 * (z.length * q.eval (3 * z.length + 2)) + 3 * z.length + 6 := by
    intro z k hk
    have hfz : (pairFst z).length ≤ z.length := pairFst_length_le z
    have hsz : (pairSnd z).length ≤ z.length := pairSnd_length_le z
    have hkz : k ≤ z.length := le_trans hk hfz
    have hrec : ∀ i < k, (E (pair (pairSnd z) (List.replicate i true))).length
        ≤ q.eval (3 * z.length + 2) := by
      intro i hi
      refine le_trans (hq _) (polynomial_eval_mono_nat q ?_)
      rw [pair_length, List.length_replicate]
      omega
    have hcat : (entryCat E (pairSnd z) k).length ≤ z.length * q.eval (3 * z.length + 2) :=
      le_trans (length_entryCat_le E _ _ k hrec) (Nat.mul_le_mul_right _ hkz)
    rw [listStep_iterate, pair_length, pair_length, List.length_replicate]
    omega
  have hiter := iterate_mem_FP_of_polyBound (listStep_mem_FP hE) hinit
    Cobham.fstBlock_mem_FP hB hbound
  refine mem_FP_of_eq (mem_FP_comp (mem_FP_comp hiter Cobham.fstBlock_mem_FP)
    Cobham.fstBlock_mem_FP) fun z => ?_
  simp only [Function.comp_apply]
  rw [listStep_iterate, pairFst_pair, pairFst_pair, catRange_eq_entryCat E z]

/-! ## Encoding a list -/

theorem listEncFn_eq (E : List Bool → List Bool) (z : List Bool) :
    listEncFn E z
      = false :: entryCat E (pairSnd z) (pairFst z).length ++ [true] := rfl

/-- **The accumulation is the encoding.** If each step writes the encoding of
the corresponding entry, the loop writes the inner part of the list's own
encoding. -/
theorem bitstringEncode_of_entries {α : Type} [DataEncode α]
    {E : List Bool → List Bool} {x : List Bool} (l : List α)
    (h : ∀ i, ∀ hi : i < l.length,
      E (pair x (List.replicate i true)) = DataEncode.bitstringEncode (l[i]'hi)) :
    DataEncode.bitstringEncode l = false :: entryCat E x l.length ++ [true] := by
  have hcat : entryCat E x l.length = (l.map DataEncode.bitstringEncode).flatten := by
    rw [entryCat]
    have : (List.range l.length).map (fun i => E (pair x (List.replicate i true)))
        = l.map DataEncode.bitstringEncode := by
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      have hi : i < l.length := by simpa using h2
      rw [List.getElem_map, List.getElem_map, List.getElem_range]
      exact h i hi
    rw [List.flatMap_def, this]
  rw [hcat, DataEncode.bitstringEncode_list, List.cons_append]

/-! ## One-bit marks -/

theorem isEmptyMark_mem_FP_internal {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => isEmptyMark (f z)) ∈ FP := by
  refine mem_FP_of_eq (Cobham.selectHeadFn_mem_FP (Cobham.emptyFlag_mem_FP hf)
    (constFn_mem_FP [true]) (constFn_mem_FP [])) fun z => ?_
  cases f z with
  | nil => exact Cobham.selectHead_emptyFlag_nil _ _
  | cons b t => exact Cobham.selectHead_emptyFlag_cons _ _ _ _

theorem nonemptyMark_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => nonemptyMark (f z)) ∈ FP := by
  refine mem_FP_of_eq (Cobham.selectHeadFn_mem_FP (Cobham.emptyFlag_mem_FP hf)
    (constFn_mem_FP []) (constFn_mem_FP [true])) fun z => ?_
  cases f z with
  | nil => exact Cobham.selectHead_emptyFlag_nil _ _
  | cons b t => exact Cobham.selectHead_emptyFlag_cons _ _ _ _

theorem length_nonemptyMark (s : List Bool) :
    (nonemptyMark s).length = if s = [] then 0 else 1 := by
  cases s <;> rfl

/-! ## The maximum as a count -/

theorem dropEntry_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) : dropEntry f ∈ FP := by
  have hz : (fun v : List Bool => pairFst (pairFst v)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hj : (fun v : List Bool => pairSnd (pairFst v)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hv : (fun v : List Bool => f (pair (pairFst (pairFst v)) (pairSnd v))) ∈ FP :=
    mem_FP_comp (Cobham.pairFn_mem_FP hz Cobham.sndBlock_mem_FP) hf
  exact dropLenFn_mem_FP hj hv

theorem maxProbe_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) : maxProbe f ∈ FP := by
  have hu : (fun w : List Bool => pairFst (pairFst w)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hz : (fun w : List Bool => pairSnd (pairFst w)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have harg := Cobham.pairFn_mem_FP hu (Cobham.pairFn_mem_FP hz Cobham.sndBlock_mem_FP)
  exact nonemptyMark_mem_FP (mem_FP_comp harg (catRange_mem_FP_internal (dropEntry_mem_FP hf)))

/-- `j` is below the maximum exactly when some value is longer than `j`. -/
theorem lt_maxOver_iff {f : List Bool → List Bool} {z : List Bool} {j : ℕ} :
    ∀ n, j < maxOver f z n ↔ ∃ i < n, j < (f (pair z (List.replicate i true))).length := by
  intro n
  induction n with
  | zero => simp [maxOver]
  | succ n ih =>
      rw [maxOver, lt_max_iff, ih]
      constructor
      · rintro (⟨i, hi, h⟩ | h)
        · exact ⟨i, by omega, h⟩
        · exact ⟨n, by omega, h⟩
      · rintro ⟨i, hi, h⟩
        rcases Nat.lt_or_ge i n with hin | hin
        · exact Or.inl ⟨i, hin, h⟩
        · exact Or.inr (by rwa [show i = n by omega] at h)

/-- **The test behind `maxFn`**: one mark when `j` is below the maximum. -/
theorem length_maxProbe_pair (f : List Bool → List Bool) (z : List Bool) (n j : ℕ) :
    (maxProbe f (pair (pair (List.replicate n true) z) (List.replicate j true))).length
      = if j < maxOver f z n then 1 else 0 := by
  classical
  rw [maxProbe, pairFst_pair, pairFst_pair, pairSnd_pair, pairSnd_pair, length_nonemptyMark]
  have hlen : (catRange (dropEntry f)
      (pair (List.replicate n true) (pair z (List.replicate j true)))).length
        = ∑ i ∈ Finset.range n, ((f (pair z (List.replicate i true))).length - j) := by
    rw [catRange_eq_entryCat, pairFst_pair, pairSnd_pair,
      List.length_replicate, length_entryCat]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dropEntry, pairFst_pair, pairFst_pair, pairSnd_pair, pairSnd_pair, List.length_drop,
      List.length_replicate]
  by_cases hj : j < maxOver f z n
  · obtain ⟨i, hi, hgt⟩ := (lt_maxOver_iff n).mp hj
    rw [ite_eq_left hj, ite_eq_right]
    intro hnil
    have hzero := congrArg List.length hnil
    rw [hlen, List.length_nil, Finset.sum_eq_zero_iff] at hzero
    have := hzero i (Finset.mem_range.mpr hi)
    omega
  · rw [ite_eq_right hj, ite_eq_left]
    refine List.eq_nil_of_length_eq_zero ?_
    rw [hlen, Finset.sum_eq_zero_iff]
    intro i hi
    have hle : ¬ j < (f (pair z (List.replicate i true))).length := fun h =>
      hj ((lt_maxOver_iff n).mpr ⟨i, Finset.mem_range.mp hi, h⟩)
    omega

end Complexity
