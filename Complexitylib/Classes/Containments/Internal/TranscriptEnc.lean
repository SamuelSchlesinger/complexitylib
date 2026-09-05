/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.BinArith
public import Complexitylib.Classes.Containments.Internal.FPBridge
public import Complexitylib.Encoding.DataEncode

/-!
# The transcript encoding inside the polynomial-time algebra

⚠️ Unreviewed by Bolton

An interactive verifier reads `Complexity.Protocol.view`, which carries the transcript through
`DataEncode.bitstringEncode`. A machine walking the game tree therefore has to *build* that
encoding as it extends the transcript, one message at a time.

The encoding is a parenthesized serialization, so it is a plain concatenation once the outer
brackets are stripped: `Complexity.encBody` is the concatenation of the per-message encodings, and
extending the transcript appends to it (`Complexity.encBody_append`). That is what makes the walk
possible — nothing has to be re-encoded when a message is added or removed.

## Main definitions

- `Complexity.encBit`, `Complexity.encMsg`, `Complexity.encBody` — the three layers
- `Complexity.encStep` — the scan computing a message's encoding

## Main results

- `Complexity.bitstringEncode_transcript` — the encoding, spelled out
- `Complexity.encBody_append` — a new message is appended
- `Complexity.encMsgFn_mem_FP` — a message can be encoded in polynomial time
-/

@[expose] public section

namespace Complexity

open Cobham

/-! ## The three layers -/

/-- The encoding of a single bit. -/
def encBit (b : Bool) : List Bool := if b then [false, false, true, true] else [false, true]

/-- The encoding of one message. -/
def encMsg (v : List Bool) : List Bool := false :: ((v.map encBit).flatten ++ [true])

/-- The concatenation of the messages' encodings — the body of a transcript's encoding. -/
def encBody (τ : List (List Bool)) : List Bool := (τ.map encMsg).flatten

theorem encBit_eq (b : Bool) : (DataEncode.encode b).toBits = encBit b := by
  cases b <;> simp [DataEncode.encode, Data.toBits_l, encBit]

theorem encMsg_eq (v : List Bool) :
    (DataEncode.encode v).toBits = encMsg v := by
  show (Data.l (v.map DataEncode.encode)).toBits = _
  rw [Data.toBits_l, encMsg, List.map_map]
  have hmap : List.map (Data.toBits ∘ DataEncode.encode) v = v.map encBit :=
    List.map_congr_left fun b _ => encBit_eq b
  rw [hmap]

/-- **The transcript's encoding, spelled out.** -/
theorem bitstringEncode_transcript (τ : List (List Bool)) :
    DataEncode.bitstringEncode τ = false :: (encBody τ ++ [true]) := by
  show (Data.l (τ.map DataEncode.encode)).toBits = _
  rw [Data.toBits_l, encBody, List.map_map]
  have hmap : List.map (Data.toBits ∘ DataEncode.encode) τ = τ.map encMsg :=
    List.map_congr_left fun v _ => encMsg_eq v
  rw [hmap]

@[simp] theorem encBody_nil : encBody [] = [] := rfl

/-- **A new message is appended.** Nothing already written has to change. -/
@[simp] theorem encBody_append (τ : List (List Bool)) (v : List Bool) :
    encBody (τ ++ [v]) = encBody τ ++ encMsg v := by
  rw [encBody, encBody, List.map_append]
  simp

theorem encBody_append_two (τ : List (List Bool)) (v a : List Bool) :
    encBody (τ ++ [v, a]) = encBody τ ++ encMsg v ++ encMsg a := by
  have h : τ ++ [v, a] = (τ ++ [v]) ++ [a] := by simp
  rw [h, encBody_append, encBody_append]

theorem encBit_length_le (b : Bool) : (encBit b).length ≤ 4 := by
  cases b <;> simp [encBit]

theorem encMsg_length_le (v : List Bool) : (encMsg v).length ≤ 4 * v.length + 2 := by
  rw [encMsg, List.length_cons, List.length_append, List.length_flatten, List.length_cons]
  have h : ∀ l ∈ (v.map encBit).map List.length, l ≤ 4 := by
    intro l hl
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hl
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
    exact encBit_length_le b
  have := List.sum_le_length_nsmul _ 4 h
  rw [List.length_map, List.length_map] at this
  simp only [smul_eq_mul] at this
  simp only [List.length_nil]
  omega

/-! ## Encoding a message is polynomial-time -/

/-- One step of the encoding scan: the bits emitted so far, and the message still to read. -/
def encStep : List Bool × List Bool → List Bool × List Bool
  | (acc, []) => (acc, [])
  | (acc, b :: t) => (acc ++ encBit b, t)

@[simp] theorem encStep_nil (acc : List Bool) : encStep (acc, []) = (acc, []) := rfl

theorem encStep_cons (acc : List Bool) (b : Bool) (t : List Bool) :
    encStep (acc, b :: t) = (acc ++ encBit b, t) := rfl

/-- **The scan flattens the per-bit encodings.** -/
theorem encStep_iterate_run (acc v : List Bool) :
    encStep^[v.length] (acc, v) = (acc ++ (v.map encBit).flatten, []) := by
  induction v generalizing acc with
  | nil => simp
  | cons b t ih =>
      rw [List.length_cons, Function.iterate_succ_apply, encStep_cons, ih]
      simp

theorem encStep_iterate_length (acc v : List Bool) (n : ℕ) :
    (encStep^[n] (acc, v)).1.length + (encStep^[n] (acc, v)).2.length
      ≤ acc.length + 4 * v.length := by
  induction n generalizing acc v with
  | zero => simp; omega
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases v with
      | nil => simpa using ih acc []
      | cons b t =>
          rw [encStep_cons]
          have hb : (encBit b).length ≤ 4 := by cases b <;> simp [encBit]
          have := ih (acc ++ encBit b) t
          simp only [List.length_append, List.length_cons] at this ⊢
          omega

/-! ## The packed scan -/

/-- The packed scan state. -/
def encPack (acc rest : List Bool) : List Bool := pair acc rest

@[simp] theorem encPack_length (acc rest : List Bool) :
    (encPack acc rest).length = 2 * acc.length + rest.length + 2 := by
  rw [encPack, pair_length]
  omega

/-- One step of the packed scan. -/
def encStepP (z : List Bool) : List Bool :=
  selectHead (lenLeFlag (pairSnd z) [false])
    (encPack (pairFst z ++
        selectHead (bit1 (pairSnd z)) [false, false, true, true] [false, true])
      ((pairSnd z).drop 1))
    z

theorem encStepP_pack (acc rest : List Bool) :
    encStepP (encPack acc rest)
      = encPack (encStep (acc, rest)).1 (encStep (acc, rest)).2 := by
  rw [encStepP, encPack]
  simp only [pairFst_pair, pairSnd_pair]
  cases rest with
  | nil =>
      have hflag : lenLeFlag ([] : List Bool) [false] = [false] := rfl
      rw [selectHead, hflag]
      simp [encPack]
  | cons b t =>
      have hflag : lenLeFlag (b :: t) [false] = [true] :=
        (lenLeFlag_eq_true_iff (b :: t) [false]).mpr (by simp)
      rw [selectHead, hflag]
      simp only [List.head?_cons, reduceIte]
      rw [encStep_cons, encPack, bit1_cons]
      cases b <;> simp [encBit, selectHead, encPack]

theorem encStepP_iterate (s : List Bool × List Bool) (n : ℕ) :
    encStepP^[n] (encPack s.1 s.2) = encPack (encStep^[n] s).1 (encStep^[n] s).2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, encStepP_pack, ih (encStep s),
        Function.iterate_succ_apply]

theorem encStepP_iterate_args (acc rest : List Bool) (n : ℕ) :
    encStepP^[n] (encPack acc rest)
      = encPack (encStep^[n] (acc, rest)).1 (encStep^[n] (acc, rest)).2 :=
  encStepP_iterate (acc, rest) n

/-- The flattened per-bit encodings, computed by the scan. -/
def encFlat (v : List Bool) : List Bool := pairFst (encStepP^[v.length] (encPack [] v))

theorem encFlat_eq (v : List Bool) : encFlat v = (v.map encBit).flatten := by
  rw [encFlat, encStepP_iterate_args, encStep_iterate_run, encPack]
  simp

theorem encMsg_eq_encFlat (v : List Bool) : encMsg v = false :: (encFlat v ++ [true]) := by
  rw [encMsg, encFlat_eq]

theorem encStepP_mem_FP : encStepP ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hfst : (fun z : List Bool => pairFst z) ∈ FP := Cobham.fstBlock_mem_FP
  have hsnd : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
  have hone : (fun _ : List Bool => ([false] : List Bool)) ∈ FP := constFn_mem_FP [false]
  have hbit : (fun z => bit1 (pairSnd z)) ∈ FP := by
    have := Cobham.takeLenFn_mem_FP hone (Cobham.appendFn_mem_FP hsnd hone)
    simpa [bit1] using this
  have hdrop : (fun z => (pairSnd z).drop 1) ∈ FP := by
    have := dropLenFn_mem_FP hone hsnd
    simpa using this
  exact Cobham.selectHeadFn_mem_FP (lenLeFlagFn_mem_FP hsnd hone)
    (Cobham.pairFn_mem_FP
      (Cobham.appendFn_mem_FP hfst
        (Cobham.selectHeadFn_mem_FP hbit (constFn_mem_FP [false, false, true, true])
          (constFn_mem_FP [false, true])))
      hdrop) hid

theorem encFlatFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => encFlat (a z)) ∈ FP := by
  have hinit : (fun z => encPack [] (a z)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP []) ha
  have hwidth : (fun z => encPack (a z ++ a z ++ a z ++ a z) (a z)) ∈ FP :=
    Cobham.pairFn_mem_FP
      (Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP ha ha) ha) ha) ha
  have hbound : ∀ z, ∀ n ≤ (a z).length,
      (encStepP^[n] (encPack [] (a z))).length
        ≤ (encPack (a z ++ a z ++ a z ++ a z) (a z)).length := by
    intro z n _
    rw [encStepP_iterate_args, encPack_length, encPack_length]
    have := encStep_iterate_length [] (a z) n
    simp only [List.length_nil, List.length_append] at this ⊢
    omega
  have h := Cobham.iterate_mem_FP encStepP_mem_FP hinit ha hwidth hbound
  have h1 := mem_FP_comp h Cobham.fstBlock_mem_FP
  simp [encFlat]
  exact h1

theorem encMsgFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => encMsg (a z)) ∈ FP := by
  have h : (fun z => false :: (encFlat (a z) ++ [true])) ∈ FP := by
    have hcat := Cobham.appendFn_mem_FP (encFlatFn_mem_FP ha) (constFn_mem_FP [true])
    have := mem_FP_comp hcat (Cobham.cons_mem_FP false)
    exact this
  exact mem_FP_of_eq h fun z => (encMsg_eq_encFlat (a z)).symm

/-! ## Transcripts given as rounds -/

/-- A transcript, read off a list of rounds. This is the shape a stack holds: one frame per
round, carrying the verifier's message and the prover's reply. -/
def flatRounds : List (List Bool × List Bool) → List (List Bool)
  | [] => []
  | p :: ps => p.1 :: p.2 :: flatRounds ps

@[simp] theorem flatRounds_nil : flatRounds [] = [] := rfl

@[simp] theorem flatRounds_cons (p : List Bool × List Bool)
    (ps : List (List Bool × List Bool)) :
    flatRounds (p :: ps) = p.1 :: p.2 :: flatRounds ps := rfl

@[simp] theorem flatRounds_length (ps : List (List Bool × List Bool)) :
    (flatRounds ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rw [flatRounds_cons, List.length_cons, List.length_cons, ih, List.length_cons]
      omega

@[simp] theorem flatRounds_append (ps : List (List Bool × List Bool)) (v a : List Bool) :
    flatRounds (ps ++ [(v, a)]) = flatRounds ps ++ [v, a] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [List.cons_append, flatRounds_cons, ih, flatRounds_cons]; simp

/-- The body of the encoding of a transcript given as rounds. -/
def encBodyR (ps : List (List Bool × List Bool)) : List Bool := encBody (flatRounds ps)

@[simp] theorem encBodyR_nil : encBodyR [] = [] := rfl

@[simp] theorem encBodyR_append (ps : List (List Bool × List Bool)) (v a : List Bool) :
    encBodyR (ps ++ [(v, a)]) = encBodyR ps ++ encMsg v ++ encMsg a := by
  rw [encBodyR, encBodyR, flatRounds_append, encBody_append_two]

end Complexity
