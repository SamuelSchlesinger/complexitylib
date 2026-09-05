/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.NatEncode

/-!
# Writing out a list of encoded entries

The encoding of a list is its entries' encodings run together inside one pair of
brackets. So a machine that can produce each entry's encoding can produce the
list's, by accumulating them in a loop.

The loop is `iterate_mem_FP`, and the state carries the accumulated bits, the
counter, and the input the entries are read from.

## Main definitions

- `Complexity.listStep` — append the next entry's encoding

## Main results

- `Complexity.listStep_iterate` — what the loop accumulates
- `Complexity.bitstringEncode_of_entries` — the accumulation is the encoding
- `Complexity.listEncFn_mem_FP`, `Complexity.listEncFn_eq` — the loop is
  polynomial time and writes the encoding
-/

@[expose] public section

namespace Complexity

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
      E (pair (pairSnd st) (pairSnd (pairFst st)))) ∈ FP := by
    have := mem_FP_comp (Cobham.pairFn_mem_FP hx hctr) hE
    exact this
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
  rw [hcat, DataEncode.bitstringEncode_def,
    show DataEncode.encode l = Data.l (l.map DataEncode.encode) from rfl,
    Data.toBits_l, List.map_map]
  congr 2

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

/-! ### The loop as one function -/

/-- **The list encoder**, on `pair (unary count) input`. -/
noncomputable def listEncFn (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  false :: pairFst (pairFst
    ((listStep E)^[(pairFst z).length] (pair (pair [] []) (pairSnd z))))
    ++ [true]

theorem listEncFn_mem_FP {E : List Bool → List Bool} (hE : E ∈ FP) (p : Polynomial ℕ)
    (hbound : ∀ z : List Bool, ∀ k ≤ (pairFst z).length,
      ((listStep E)^[k] (pair (pair [] []) (pairSnd z))).length
        ≤ p.eval z.length) :
    listEncFn E ∈ FP := by
  have hinit : (fun z : List Bool => pair (pair [] []) (pairSnd z)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP (pair [] [])) Cobham.sndBlock_mem_FP
  have hwidth : (fun z : List Bool => polyRuler p (id z)) ∈ FP :=
    polyRulerFn_mem_FP p id_mem_FP
  have hbound' : ∀ z : List Bool, ∀ k ≤ (pairFst z).length,
      ((listStep E)^[k] (pair (pair [] []) (pairSnd z))).length
        ≤ (polyRuler p (id z)).length := by
    intro z k hk
    rw [polyRuler_length]
    exact hbound z k hk
  have hiter := Cobham.iterate_mem_FP (listStep_mem_FP hE) hinit
    Cobham.fstBlock_mem_FP hwidth hbound'
  have hproj := mem_FP_comp (mem_FP_comp hiter Cobham.fstBlock_mem_FP)
    Cobham.fstBlock_mem_FP
  have hcons := mem_FP_comp hproj (Cobham.cons_mem_FP false)
  have := Cobham.appendFn_mem_FP hcons (constFn_mem_FP [true])
  refine mem_FP_of_eq this fun z => ?_
  rw [listEncFn]
  simp

theorem listEncFn_eq (E : List Bool → List Bool) (z : List Bool) :
    listEncFn E z
      = false :: entryCat E (pairSnd z) (pairFst z).length ++ [true] := by
  rw [listEncFn, listStep_iterate, pairFst_pair, pairFst_pair]

/-- **The loop writes the list's encoding.** -/
theorem listEncFn_eq_bitstringEncode {α : Type} [DataEncode α]
    {E : List Bool → List Bool} {z : List Bool} (l : List α)
    (hn : (pairFst z).length = l.length)
    (h : ∀ i, ∀ hi : i < l.length,
      E (pair (pairSnd z) (List.replicate i true))
        = DataEncode.bitstringEncode (l[i]'hi)) :
    listEncFn E z = DataEncode.bitstringEncode l := by
  rw [listEncFn_eq, hn, ← bitstringEncode_of_entries l h]

end Complexity
