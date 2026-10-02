/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.UnaryLength
public import Complexitylib.Classes.P.Unary
public import Complexitylib.Classes.PCP.Internal.PosScan
public import Complexitylib.Classes.PCP.Internal.UnaryDivMod
public import Complexitylib.Classes.PCP.Internal.NatEncode
import Complexitylib.Tactic.PolyTime

/-!
# Reading a table of unary numbers

An algorithm that materializes a graph writes a list of records and reads them
back. `PosScan` reads an entry of an encoded list, and `DataEncode` writes the
entries; what is missing is getting a *number* back out, in the unary form the
loops of the toolkit consume.

Storing the number in unary makes that a length computation: the encoding of a
unary string of `w` marks is `4 * w + 2` bits long — two brackets, and four bits
a mark — so dividing the length by four recovers the marks. No parsing of the
encoding is needed, and no binary arithmetic.

The same scan reads the two halves of an encoded pair, since a pair is encoded
as the two-element list of its halves.

## Main definitions

- `Complexity.unaryOf` — the marks an encoded unary string stands for
- `Complexity.fstEnc`, `Complexity.sndEnc` — the halves of an encoded pair

## Main results

- `Complexity.unaryOf_encode`, `Complexity.unaryOf_mem_FP`
- `Complexity.fstEnc_eq`, `Complexity.sndEnc_eq`, and their `FP` versions
- `Complexity.tableFst_eq`, `Complexity.tableSnd_eq` — an entry of a table of
  pairs of unary numbers, read back in unary
- `Complexity.recFst_eq`, `Complexity.recSnd_eq`, `Complexity.recThd_eq` — the
  same for records of three numbers
- `Complexity.encPair_eq` — and written out
-/

@[expose] public section

namespace Complexity

/-! ### Numbers -/

/-- The size of an encoded unary string: two brackets and four bits a mark. -/
theorem size_encode_replicate (w : ℕ) :
    (DataEncode.encode (List.replicate w true)).size = 4 * w + 2 := by
  have hone : (DataEncode.encode true).size = 4 := by
    show (Data.l [Data.l []]).size = 4
    rw [Data.cons_size]
    simp
  induction w with
  | zero => simp
  | succ w ih =>
      have h : DataEncode.encode (List.replicate (w + 1) true)
          = Data.l (DataEncode.encode true :: (List.replicate w true).map DataEncode.encode) := by
        show Data.l ((List.replicate (w + 1) true).map DataEncode.encode) = _
        rw [List.replicate_succ, List.map_cons]
      rw [h, Data.cons_size, hone,
        show (Data.l ((List.replicate w true).map DataEncode.encode)).size
          = (DataEncode.encode (List.replicate w true)).size from rfl, ih]
      omega

theorem length_bitstringEncode_replicate (w : ℕ) :
    (DataEncode.bitstringEncode (List.replicate w true)).length = 4 * w + 2 := by
  rw [DataEncode.bitstringEncode_def, Data.length_toBits, size_encode_replicate]

/-- The unary number an encoded unary string stands for: its length without the
two brackets, divided by four. -/
def unaryOf (e : List Bool) : List Bool := List.replicate ((e.length - 2) / 4) true

theorem unaryOf_encode (w : ℕ) :
    unaryOf (DataEncode.bitstringEncode (List.replicate w true)) = List.replicate w true := by
  rw [unaryOf, length_bitstringEncode_replicate]
  congr 1
  omega

@[polytime] theorem unaryOf_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => unaryOf (a z)) ∈ FP := by
  polytime [unaryOf]

/-! ### Pairs -/

/-- The first half of an encoded pair. -/
noncomputable def fstEnc (e : List Bool) : List Bool := posAt e 0

/-- The second half of an encoded pair. -/
noncomputable def sndEnc (e : List Bool) : List Bool := posAt e 1

theorem bitstringEncode_prod {α β : Type} [DataEncode α] [DataEncode β] (a : α) (b : β) :
    DataEncode.bitstringEncode (a, b)
      = DataEncode.bitstringEncode
          ([DataEncode.encode a, DataEncode.encode b] : List Data) := by
  rw [DataEncode.bitstringEncode_def, DataEncode.bitstringEncode_def, DataEncode_pair]
  show _ = (Data.l (([DataEncode.encode a, DataEncode.encode b] : List Data).map id)).toBits
  rw [List.map_id]

theorem fstEnc_eq {α β : Type} [DataEncode α] [DataEncode β] (a : α) (b : β) :
    fstEnc (DataEncode.bitstringEncode (a, b)) = DataEncode.bitstringEncode a := by
  rw [fstEnc, bitstringEncode_prod,
    posAt_eq_of_lt (l := ([DataEncode.encode a, DataEncode.encode b] : List Data))
      (by norm_num)]
  rfl

theorem sndEnc_eq {α β : Type} [DataEncode α] [DataEncode β] (a : α) (b : β) :
    sndEnc (DataEncode.bitstringEncode (a, b)) = DataEncode.bitstringEncode b := by
  rw [sndEnc, bitstringEncode_prod,
    posAt_eq_of_lt (l := ([DataEncode.encode a, DataEncode.encode b] : List Data))
      (by norm_num)]
  rfl

@[polytime] theorem fstEnc_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => fstEnc (a z)) ∈ FP := by
  polytime [fstEnc]

@[polytime] theorem sndEnc_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => sndEnc (a z)) ∈ FP := by
  polytime [sndEnc]

/-! ### Unary arithmetic with constants -/

/-- Any string, as that many marks: its length, written in unary. -/
def marks (s : List Bool) : List Bool := List.replicate s.length true

theorem marks_eq (s : List Bool) : marks s = List.replicate s.length true := rfl

@[polytime] theorem marks_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => marks (a z)) ∈ FP := by
  polytime [marks]

/-- Division by a constant, in unary; `divC 0 s` is empty. -/
def divC (c : ℕ) (s : List Bool) : List Bool := List.replicate (s.length / c) true

theorem divC_eq {c : ℕ} (s : List Bool) : divC c s = List.replicate (s.length / c) true := rfl

@[polytime] theorem divC_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) (c : ℕ) :
    (fun z => divC c (a z)) ∈ FP := by
  polytime [divC]

/-- Remainder by a constant, in unary; `modC 0 s` is `s` in marks. -/
def modC (c : ℕ) (s : List Bool) : List Bool := List.replicate (s.length % c) true

theorem modC_eq {c : ℕ} (s : List Bool) : modC c s = List.replicate (s.length % c) true := rfl

@[polytime] theorem modC_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) (c : ℕ) :
    (fun z => modC c (a z)) ∈ FP := by
  polytime [modC]

/-- The product of two lengths. -/
def mulLen (a b : List Bool) : List Bool := List.replicate (a.length * b.length) false

@[simp] theorem length_mulLen (a b : List Bool) :
    (mulLen a b).length = a.length * b.length := by
  rw [mulLen, List.length_replicate]

@[polytime] theorem mulLen_mem_FP {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun z => mulLen (f z) (g z)) ∈ FP := by
  polytime [mulLen]

/-- Multiplication by a constant, as a length. -/
def mulC (c : ℕ) (s : List Bool) : List Bool := List.replicate (s.length * c) false

@[simp] theorem length_mulC (c : ℕ) (s : List Bool) : (mulC c s).length = s.length * c := by
  rw [mulC, List.length_replicate]

@[polytime] theorem mulC_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) (c : ℕ) :
    (fun z => mulC c (a z)) ∈ FP := by
  polytime [mulC]

/-! ### Writing records -/

/-- The encoding of a unary string. -/
def encUnary (s : List Bool) : List Bool := false :: s.flatMap boolBits ++ [true]

theorem encUnary_eq (s : List Bool) : encUnary s = DataEncode.bitstringEncode s :=
  (bitstringEncode_list s).symm

@[polytime] theorem encUnary_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => encUnary (a z)) ∈ FP := by
  simp_rw [encUnary_eq]
  polytime

/-- The encoding of a pair of unary strings. -/
def encPair (a b : List Bool) : List Bool := false :: (encUnary a ++ encUnary b) ++ [true]

theorem bitstringEncode_prod_eq {α β : Type} [DataEncode α] [DataEncode β] (a : α) (b : β) :
    DataEncode.bitstringEncode ((a, b) : α × β)
      = false :: (DataEncode.bitstringEncode a ++ DataEncode.bitstringEncode b) ++ [true] := by
  rw [DataEncode.bitstringEncode_def, DataEncode_pair, Data.toBits_l]
  simp [DataEncode.bitstringEncode_def]

theorem encPair_eq (a b : List Bool) :
    encPair a b = DataEncode.bitstringEncode ((a, b) : List Bool × List Bool) := by
  rw [bitstringEncode_prod_eq, encPair, encUnary_eq, encUnary_eq]

@[polytime] theorem encPair_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => encPair (a z) (b z)) ∈ FP := by
  polytime [encPair]

theorem unaryOf_fstEnc_encPair (w c : ℕ) :
    unaryOf (fstEnc (encPair (List.replicate w true) (List.replicate c true)))
      = List.replicate w true := by
  rw [encPair_eq, fstEnc_eq, unaryOf_encode]

theorem unaryOf_sndEnc_encPair (w c : ℕ) :
    unaryOf (sndEnc (encPair (List.replicate w true) (List.replicate c true)))
      = List.replicate c true := by
  rw [encPair_eq, sndEnc_eq, unaryOf_encode]

@[simp] theorem marks_append_mulC (w m c : ℕ) :
    marks (List.replicate w true ++ mulC c (List.replicate m true))
      = List.replicate (w + m * c) true := by
  rw [marks_eq, List.length_append, List.length_replicate, length_mulC,
    List.length_replicate]

theorem length_mulC_append (m c w : ℕ) :
    (mulC c (List.replicate m true) ++ List.replicate w true).length = m * c + w := by
  rw [List.length_append, length_mulC, List.length_replicate, List.length_replicate]

/-- The encoding of a list is two brackets and its entries' encodings. -/
theorem length_bitstringEncode_list {α : Type} [DataEncode α] (l : List α) :
    (DataEncode.bitstringEncode l).length
      = 2 + (l.map fun a => (DataEncode.bitstringEncode a).length).sum := by
  rw [DataEncode.bitstringEncode_list, List.length_cons, List.length_append,
    List.length_flatten, List.map_map]
  simp only [List.length_singleton, Function.comp_def]
  omega

@[simp] theorem length_encPair (w c : ℕ) :
    (encPair (List.replicate w true) (List.replicate c true)).length = 4 * w + 4 * c + 6 := by
  rw [encPair_eq, ← encPair_eq, encPair, encUnary_eq, encUnary_eq]
  simp only [List.length_append, List.length_cons, List.length_nil,
    length_bitstringEncode_replicate]
  omega

/-! ### Tables of pairs of numbers -/

/-- The first number of the `j`-th record of a table, in unary. -/
noncomputable def tableFst (T : List Bool) (j : ℕ) : List Bool := unaryOf (fstEnc (posAt T j))

/-- The second number of the `j`-th record of a table, in unary. -/
noncomputable def tableSnd (T : List Bool) (j : ℕ) : List Bool := unaryOf (sndEnc (posAt T j))

variable {l : List (List Bool × List Bool)} {j w c : ℕ}

theorem tableFst_def (T : List Bool) (j : ℕ) :
    tableFst T j = unaryOf (fstEnc (posAt T j)) := rfl

theorem tableSnd_def (T : List Bool) (j : ℕ) :
    tableSnd T j = unaryOf (sndEnc (posAt T j)) := rfl

theorem tableFst_eq (hj : j < l.length)
    (h : l[j]'hj = (List.replicate w true, List.replicate c true)) :
    tableFst (DataEncode.bitstringEncode l) j = List.replicate w true := by
  rw [tableFst, posAt_eq_of_lt hj, h, fstEnc_eq, unaryOf_encode]

theorem tableSnd_eq (hj : j < l.length)
    (h : l[j]'hj = (List.replicate w true, List.replicate c true)) :
    tableSnd (DataEncode.bitstringEncode l) j = List.replicate c true := by
  rw [tableSnd, posAt_eq_of_lt hj, h, sndEnc_eq, unaryOf_encode]

@[polytime] theorem tableFst_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => tableFst (b z) (a z).length) ∈ FP := by
  polytime [tableFst]

/-- Read the first table field at any index computable in unary. -/
@[polytime] theorem tableFst_mem_FP_of_unary {i : List Bool → ℕ}
    {table : List Bool → List Bool} (hi : UnaryFn i) (ht : table ∈ FP) :
    (fun z => tableFst (table z) (i z)) ∈ FP := by
  polytime [tableFst]

@[polytime] theorem tableSnd_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => tableSnd (b z) (a z).length) ∈ FP := by
  polytime [tableSnd]

/-- Read the second table field at any index computable in unary. -/
@[polytime] theorem tableSnd_mem_FP_of_unary {i : List Bool → ℕ}
    {table : List Bool → List Bool} (hi : UnaryFn i) (ht : table ∈ FP) :
    (fun z => tableSnd (table z) (i z)) ∈ FP := by
  polytime [tableSnd]

/-! ### Records of three numbers -/

/-- The encoding of three unary strings. -/
def encTriple (a b c : List Bool) : List Bool := false :: (encUnary a ++ encPair b c) ++ [true]

theorem encTriple_eq (a b c : List Bool) :
    encTriple a b c
      = DataEncode.bitstringEncode ((a, (b, c)) : List Bool × List Bool × List Bool) := by
  rw [bitstringEncode_prod_eq, encTriple, encUnary_eq, ← encPair_eq]

@[simp] theorem length_encTriple (a b c : ℕ) :
    (encTriple (List.replicate a true) (List.replicate b true)
        (List.replicate c true)).length = 4 * a + 4 * b + 4 * c + 10 := by
  rw [encTriple, encUnary_eq]
  simp only [List.length_append, List.length_cons, List.length_nil,
    length_bitstringEncode_replicate, length_encPair]
  omega

@[polytime] theorem encTriple_mem_FP {a b c : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hc : c ∈ FP) : (fun z => encTriple (a z) (b z) (c z)) ∈ FP := by
  polytime [encTriple]

/-- The first number of the `j`-th record of a table of triples. -/
noncomputable def recFst (T : List Bool) (j : ℕ) : List Bool := unaryOf (fstEnc (posAt T j))

/-- The second. -/
noncomputable def recSnd (T : List Bool) (j : ℕ) : List Bool :=
  unaryOf (fstEnc (sndEnc (posAt T j)))

/-- The third. -/
noncomputable def recThd (T : List Bool) (j : ℕ) : List Bool :=
  unaryOf (sndEnc (sndEnc (posAt T j)))

variable {l3 : List (List Bool × List Bool × List Bool)} {a b c : ℕ}

theorem recFst_eq (hj : j < l3.length)
    (h : l3[j]'hj = (List.replicate a true, List.replicate b true, List.replicate c true)) :
    recFst (DataEncode.bitstringEncode l3) j = List.replicate a true := by
  rw [recFst, posAt_eq_of_lt hj, h, fstEnc_eq, unaryOf_encode]

theorem recSnd_eq (hj : j < l3.length)
    (h : l3[j]'hj = (List.replicate a true, List.replicate b true, List.replicate c true)) :
    recSnd (DataEncode.bitstringEncode l3) j = List.replicate b true := by
  rw [recSnd, posAt_eq_of_lt hj, h, sndEnc_eq, fstEnc_eq, unaryOf_encode]

theorem recThd_eq (hj : j < l3.length)
    (h : l3[j]'hj = (List.replicate a true, List.replicate b true, List.replicate c true)) :
    recThd (DataEncode.bitstringEncode l3) j = List.replicate c true := by
  rw [recThd, posAt_eq_of_lt hj, h, sndEnc_eq, sndEnc_eq, unaryOf_encode]

@[polytime] theorem recFst_mem_FP {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun z => recFst (g z) (f z).length) ∈ FP := by
  polytime [recFst]

/-- Read the first record field at any index computable in unary. -/
@[polytime] theorem recFst_mem_FP_of_unary {i : List Bool → ℕ}
    {table : List Bool → List Bool} (hi : UnaryFn i) (ht : table ∈ FP) :
    (fun z => recFst (table z) (i z)) ∈ FP := by
  polytime [recFst]

@[polytime] theorem recSnd_mem_FP {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun z => recSnd (g z) (f z).length) ∈ FP := by
  polytime [recSnd]

/-- Read the second record field at any index computable in unary. -/
@[polytime] theorem recSnd_mem_FP_of_unary {i : List Bool → ℕ}
    {table : List Bool → List Bool} (hi : UnaryFn i) (ht : table ∈ FP) :
    (fun z => recSnd (table z) (i z)) ∈ FP := by
  polytime [recSnd]

@[polytime] theorem recThd_mem_FP {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun z => recThd (g z) (f z).length) ∈ FP := by
  polytime [recThd]

/-- Read the third record field at any index computable in unary. -/
@[polytime] theorem recThd_mem_FP_of_unary {i : List Bool → ℕ}
    {table : List Bool → List Bool} (hi : UnaryFn i) (ht : table ∈ FP) :
    (fun z => recThd (table z) (i z)) ∈ FP := by
  polytime [recThd]

/-! ### Digit sums -/

/-- A number from its digits: `∑ j < n, digit j · radix ^ j`, written in marks.
The digits are read from the input, so this is how an algorithm assembles a
mixed-radix number out of constantly many pieces. -/
noncomputable def digitSum (radix : ℕ) (digit : ℕ → List Bool → List Bool) :
    ℕ → List Bool → List Bool
  | 0, _ => []
  | n + 1, w => digitSum radix digit n w ++ mulC (radix ^ n) (digit n w)

@[polytime] theorem digitSum_mem_FP {radix : ℕ} {digit : ℕ → List Bool → List Bool}
    (hd : ∀ i, digit i ∈ FP) : ∀ n, digitSum radix digit n ∈ FP := by
  intro n
  induction n with
  | zero => exact mem_FP_of_eq (constFn_mem_FP []) fun w => by rw [digitSum]
  | succ n ih =>
      refine mem_FP_of_eq (Cobham.appendFn_mem_FP ih
        (mulC_mem_FP (hd n) (radix ^ n))) fun w => ?_
      rw [digitSum]

@[simp] theorem length_digitSum (radix : ℕ) (digit : ℕ → List Bool → List Bool)
    (w : List Bool) : ∀ n, (digitSum radix digit n w).length
      = ∑ j ∈ Finset.range n, (digit j w).length * radix ^ j := by
  intro n
  induction n with
  | zero => rw [digitSum, Finset.range_zero, Finset.sum_empty, List.length_nil]
  | succ n ih =>
      rw [digitSum, List.length_append, ih, Finset.sum_range_succ, length_mulC]

theorem length_digitSum_le {radix : ℕ} (hr : 0 < radix)
    {digit : ℕ → List Bool → List Bool} {d : ℕ} (hd : ∀ j w, (digit j w).length ≤ d)
    (n : ℕ) (w : List Bool) :
    (digitSum radix digit n w).length ≤ n * (d * radix ^ n) := by
  rw [length_digitSum]
  calc ∑ j ∈ Finset.range n, (digit j w).length * radix ^ j
      ≤ ∑ _j ∈ Finset.range n, d * radix ^ n := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_range] at hj
        exact Nat.mul_le_mul (hd j w) (Nat.pow_le_pow_right hr (le_of_lt hj))
    _ = n * (d * radix ^ n) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end Complexity
