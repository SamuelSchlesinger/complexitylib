/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Encoding.DataEncode
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.P.Iterate

/-!
# Writing encodings in polynomial time — proof internals

The fold behind `Complexitylib.Classes.P.DataEncode`. `DataEncode` writes a list
of bits as its entries' encodings between a leading `false` and a trailing
`true`, and a bit's encoding is `01` for `false` and `0011` for `true`. The part
between the brackets, `encodeBody`, is built by a fold that puts one bit's
encoding in front of the encoding of the rest, so its state is at most four times
as long as the list.

## Contents

- `bitstringEncode_false`, `bitstringEncode_true` — the encodings of a bit
- `encodeBody` — the entries' encodings, run together
- `bitstringEncode_eq_encodeBody` — a list's encoding is its body in brackets
- `encodeBody_mem_FP` — writing the body is polynomial-time
-/

@[expose] public section

namespace Complexity

/-- The encoding of `false` is `01`. -/
theorem bitstringEncode_false : DataEncode.bitstringEncode false = [false, true] := by
  simp [DataEncode.bitstringEncode_def, DataEncode.encode, Data.toBits_l]

/-- The encoding of `true` is `0011`. -/
theorem bitstringEncode_true :
    DataEncode.bitstringEncode true = [false, false, true, true] := by
  simp [DataEncode.bitstringEncode_def, DataEncode.encode, Data.toBits_l]

/-- The encodings of a list's bits, run together: the encoding of the list
without its two brackets. -/
def encodeBody (l : List Bool) : List Bool :=
  (l.map DataEncode.bitstringEncode).flatten

/-- A list's encoding is its body between a leading `false` and a trailing
`true`. -/
theorem bitstringEncode_eq_encodeBody (l : List Bool) :
    DataEncode.bitstringEncode l = false :: (encodeBody l ++ [true]) :=
  DataEncode.bitstringEncode_list l

/-- The body is at most four bits per entry. -/
theorem length_encodeBody_le (l : List Bool) : (encodeBody l).length ≤ 4 * l.length := by
  induction l with
  | nil => simp [encodeBody]
  | cons b t ih =>
    cases b <;>
      simp only [encodeBody, List.map_cons, List.flatten_cons, List.length_append,
        bitstringEncode_false, bitstringEncode_true, List.length_cons,
        List.length_nil] at ih ⊢ <;>
      omega

/-- **Writing the body is polynomial-time.** It is a fold over the list that
puts `01` or `0011` in front of the body of the rest. -/
theorem encodeBody_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => encodeBody (a z)) ∈ FP := by
  -- The fold's step reads the body so far off `pair (pair [] body) t`.
  have hacc : (fun v : List Bool => pairSnd (pairFst v)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP ha
  refine recFold_mem_FP_of_bound (g := fun _ t => encodeBody t)
    (Cobham.appendFn_mem_FP (constFn_mem_FP [false, true]) hacc)
    (Cobham.appendFn_mem_FP (constFn_mem_FP [false, false, true, true]) hacc)
    (constFn_mem_FP []) (constFn_mem_FP []) ha (fun _ => rfl) (fun _ _ => ?_)
    (fun _ _ => ?_) ((PolyBound.const 4).mul (PolyBound.eval p)) fun z t ht => ?_
  · simp only [pairFst_pair, pairSnd_pair, encodeBody, List.map_cons, List.flatten_cons,
      bitstringEncode_false]
  · simp only [pairFst_pair, pairSnd_pair, encodeBody, List.map_cons, List.flatten_cons,
      bitstringEncode_true]
  · have hbody := length_encodeBody_le t
    have hsuffix := ht.length_le
    have hlen := hp z
    show _ ≤ 4 * p.eval z.length
    omega

end Complexity
