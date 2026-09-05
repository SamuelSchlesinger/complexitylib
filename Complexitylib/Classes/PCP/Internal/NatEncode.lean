/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.StripTrailing
public import Complexitylib.Classes.PCP.Internal.PosScan

/-!
# Writing out an encoded bit list

`DataEncode` serializes a list of booleans as a substitution cipher inside one
pair of brackets: `false` becomes `01` and `true` becomes `0011`. Producing that
is a fold over the list, which `recFoldClamp` runs in polynomial time.

Since a natural number is encoded *as* its `Nat.bits`, this is also the last
step of encoding a number: count the value out in binary, drop the trailing
zeros, and run the cipher.

## Main definitions

- `Complexity.boolBits` — the two-symbol cipher

## Main results

- `Complexity.bitstringEncode_list` — the cipher describes the encoding
- `Complexity.flatBitsFn_mem_FP` — running it is polynomial time
- `Complexity.natEncodeFn_eq` — a number's encoding, from its value in unary
-/

@[expose] public section

namespace Complexity

/-- The serialization of a single boolean. -/
def boolBits (b : Bool) : List Bool := if b then [false, false, true, true] else [false, true]

theorem boolBits_eq (b : Bool) : boolBits b = (DataEncode.encode b).toBits := by
  cases b
  · show [false, true] = (Data.l []).toBits
    rw [Data.toBits_l]
    simp
  · show [false, false, true, true] = (Data.l [Data.l []]).toBits
    rw [Data.toBits_l]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil]
    rw [show (Data.l ([] : List Data)).toBits = [false, true] from by
      rw [Data.toBits_l]; simp]
    simp

@[simp] theorem length_boolBits (b : Bool) : (boolBits b).length ≤ 4 := by
  cases b <;> simp [boolBits]

/-- **The cipher describes the encoding.** -/
theorem bitstringEncode_list (l : List Bool) :
    DataEncode.bitstringEncode l = false :: (l.flatMap boolBits) ++ [true] := by
  rw [DataEncode.bitstringEncode_def,
    show DataEncode.encode l = Data.l (l.map DataEncode.encode) from rfl, Data.toBits_l,
    List.map_map]
  congr 2
  rw [List.flatMap_def]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  rw [Function.comp_apply, boolBits_eq]

/-! ### Running the cipher -/

/-- The fold step on a zero. -/
def blitZero (z : List Bool) : List Bool :=
  [false, true] ++ pairSnd (pairFst z)

/-- The fold step on a one. -/
def blitOne (z : List Bool) : List Bool :=
  [false, false, true, true] ++ pairSnd (pairFst z)

theorem blitZero_mem_FP : blitZero ∈ FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact Cobham.appendFn_mem_FP (constFn_mem_FP [false, true]) h

theorem blitOne_mem_FP : blitOne ∈ FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact Cobham.appendFn_mem_FP (constFn_mem_FP [false, false, true, true]) h

theorem length_flatMap_boolBits (l : List Bool) :
    (l.flatMap boolBits).length ≤ 4 * l.length := by
  induction l with
  | nil => simp
  | cons b t ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have := length_boolBits b
      omega

theorem recFoldClamp_flatBits (bound : ℕ) (W : List Bool) :
    ∀ l : List Bool, 4 * l.length ≤ bound →
      Cobham.recFoldClamp blitZero blitOne bound [] W l = l.flatMap boolBits := by
  intro l
  induction l with
  | nil =>
      intro _
      rw [Cobham.recFoldClamp]
      simp
  | cons b t ih =>
      intro hb
      have hb' : 4 * t.length ≤ bound := by
        simp only [List.length_cons] at hb
        omega
      rw [Cobham.recFoldClamp, ih hb']
      have hstate : pairSnd (pairFst
          (pair (pair W (t.flatMap boolBits)) t)) = t.flatMap boolBits := by
        rw [pairFst_pair, pairSnd_pair]
      have hlt := length_flatMap_boolBits t
      cases b
      · show (blitZero _).take bound = _
        rw [blitZero, hstate, List.flatMap_cons,
          show boolBits false = [false, true] from rfl]
        refine List.take_of_length_le ?_
        rw [List.length_append]
        simp only [List.length_cons, List.length_nil, List.length_cons] at hb ⊢
        omega
      · show (blitOne _).take bound = _
        rw [blitOne, hstate, List.flatMap_cons,
          show boolBits true = [false, false, true, true] from rfl]
        refine List.take_of_length_le ?_
        rw [List.length_append]
        simp only [List.length_cons, List.length_nil, List.length_cons] at hb ⊢
        omega

/-- The cipher applied to `pairSnd z`. -/
def flatBitsFn (z : List Bool) : List Bool :=
  Cobham.recFoldClamp blitZero blitOne (4 * z.length) [] (pairFst z)
    (pairSnd z)

theorem flatBitsFn_mem_FP : flatBitsFn ∈ FP := by
  have := Cobham.recFoldClamp_mem_FP blitZero_mem_FP blitOne_mem_FP
    (constFn_mem_FP []) (Polynomial.C 4 * Polynomial.X)
  refine mem_FP_of_eq this fun z => ?_
  rw [flatBitsFn]
  simp

theorem flatBitsFn_eq (z : List Bool) :
    flatBitsFn z = (pairSnd z).flatMap boolBits := by
  refine recFoldClamp_flatBits _ _ _ ?_
  have := sndBlock_length_le z
  omega

/-- **The encoding of a bit list, in polynomial time.** -/
def encodeListFn (z : List Bool) : List Bool := false :: flatBitsFn z ++ [true]

theorem encodeListFn_mem_FP : encodeListFn ∈ FP := by
  have hcons := mem_FP_comp flatBitsFn_mem_FP (Cobham.cons_mem_FP false)
  have := Cobham.appendFn_mem_FP hcons (constFn_mem_FP [true])
  refine mem_FP_of_eq this fun z => ?_
  rw [encodeListFn]
  simp

theorem encodeListFn_eq (z : List Bool) :
    encodeListFn z = DataEncode.bitstringEncode (pairSnd z) := by
  rw [encodeListFn, flatBitsFn_eq, bitstringEncode_list]

/-! ### A number's own encoding -/

/-- **The encoding of a natural number**, from a width and a value both given in
unary. -/
noncomputable def natEncodeFn (z : List Bool) : List Bool :=
  encodeListFn (pair [] (stripFn (pair []
    (coinStr (pairFst z).length (pairSnd z).length))))

theorem natEncodeFn_mem_FP : natEncodeFn ∈ FP := by
  have hw : (fun z : List Bool =>
      List.replicate (pairFst z).length true) ∈ FP := by
    have := mem_FP_comp Cobham.fstBlock_mem_FP unaryLength_mem_FP
    exact this
  have hv : (fun z : List Bool =>
      List.replicate (pairSnd z).length true) ∈ FP := by
    have := mem_FP_comp Cobham.sndBlock_mem_FP unaryLength_mem_FP
    exact this
  have hcoin := coinStr_mem_FP hw hv
  have h1 : (fun z => pair [] (coinStr (pairFst z).length
      (pairSnd z).length)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP []) hcoin
  have h2 := mem_FP_comp h1 stripFn_mem_FP
  have h3 : (fun z => pair [] (stripFn (pair []
      (coinStr (pairFst z).length (pairSnd z).length)))) ∈ FP := by
    refine Cobham.pairFn_mem_FP (constFn_mem_FP []) ?_
    exact h2
  have := mem_FP_comp h3 encodeListFn_mem_FP
  exact this

/-- **It really is the number's encoding**, whenever the width holds the
value. -/
theorem natEncodeFn_eq {z : List Bool}
    (h : (pairSnd z).length < 2 ^ (pairFst z).length) :
    natEncodeFn z = DataEncode.bitstringEncode ((pairSnd z).length) := by
  rw [natEncodeFn, encodeListFn_eq, pairSnd_pair, stripFn_eq, pairSnd_pair,
    coinStr_eq h, stripTrailing_eq_bits, binValLE_bitsOfLenLE _ _ h]
  rfl

end Complexity
