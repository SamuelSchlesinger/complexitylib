/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Encoding
public import Complexitylib.Mathlib.NatBits
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Machine descriptions for the universal Turing machine

A `TMDesc` describes a single-work-tape deterministic Turing machine as
finite data: a state bit-width `w` (states are numbers below `2^w`), start
and halt states, and a transition table (`List DescEntry`, first match wins).

## Encoding

A description is laid out as a string over the writable alphabet
`Γw = {0, 1, □}`, with `□` acting as a field/entry separator:

```
qstart(w bits) □ qhalt(w bits) □ entry₀ □ entry₁ □ ⋯ □ entryₘ □ □
```

Each entry is `2w + 16` bit-symbols with no internal separators (field widths
are determined by `w`): key `q(w) si(2) sw(2) so(2)`, action
`q'(w) ww(2) wo(2) di(2) dw(2) dOut(2)`. The state width `w` is *defined* by
the length of the leading `qstart` field. The table ends at the first empty
segment (`□□`), so trailing junk is ignored — every description has
infinitely many encodings (`decodeDesc_encodeDesc_append`), which the
hierarchy-theorem diagonalization relies on.

The binary encoding `encodeDesc : TMDesc → List Bool` maps each `Γw` symbol
to 2 bits via `Γw.encode`; `decodeDesc : List Bool → TMDesc` is *total*
(unparseable segments are skipped, missing fields default), so every binary
string denotes some machine.

## Main definitions

- `DescAct`, `DescEntry`, `TMDesc` — machine descriptions
- `TMDesc.lookup` — first-match transition lookup with default action
- `TMDesc.syms` / `encodeDesc` — canonical encoding
- `parseSyms` / `decodeDesc` — total decoding
- `TMDesc.WF` — well-formedness (all state fields below `2^w`)

## Main results

- `decodeDesc_encodeDesc` — roundtrip on well-formed descriptions
- `decodeDesc_encodeDesc_append` — roundtrip ignores trailing junk
-/


@[expose] public section

namespace Complexity

-- ════════════════════════════════════════════════════════════════════════
-- Descriptions
-- ════════════════════════════════════════════════════════════════════════

/-- The action part of a transition-table entry: next state, writes for the
    work and output tapes, and directions for the input, work, and output
    heads (matching the component order of `TM.δ`). -/
structure DescAct where
  /-- The next state (as a number below `2^w`). -/
  q'   : ℕ
  /-- The symbol written to the work tape. -/
  ww   : Γw
  /-- The symbol written to the output tape. -/
  wo   : Γw
  /-- The input-head direction. -/
  di   : Dir3
  /-- The work-head direction. -/
  dw   : Dir3
  /-- The output-head direction. -/
  dOut : Dir3
  deriving DecidableEq

/-- One transition-table row for a single-work-tape machine: the key
    (state and the three symbols under the input/work/output heads) together
    with the action to take. -/
structure DescEntry where
  /-- The state this row fires in. -/
  q   : ℕ
  /-- The symbol under the input head. -/
  si  : Γ
  /-- The symbol under the work head. -/
  sw  : Γ
  /-- The symbol under the output head. -/
  so  : Γ
  /-- The action to take when the key matches. -/
  act : DescAct
  deriving DecidableEq

/-- A description of a single-work-tape deterministic TM: state bit-width
    `w` (states are numbers below `2^w`), start and halt states, and a
    transition table with first-match-wins semantics (`TMDesc.lookup`). -/
structure TMDesc where
  /-- The state bit-width: states are numbers below `2^w`. -/
  w       : ℕ
  /-- The start state. -/
  qstart  : ℕ
  /-- The halt state. -/
  qhalt   : ℕ
  /-- The transition table, first match wins. -/
  entries : List DescEntry
  deriving DecidableEq

namespace TMDesc

/-- Identity write-back: the `Γw` symbol that leaves a read symbol unchanged
    when written. `▷` maps to `□`, which is harmless: `▷` occurs only at
    cell 0, where writes are structural no-ops. -/
def readback : Γ → Γw
  | .zero  => .zero
  | .one   => .one
  | .blank => .blank
  | .start => .blank

/-- The default action taken when no table entry matches: go to the halt
    state, write back what was read, and keep all heads in place. -/
def defaultAct (d : TMDesc) (sw so : Γ) : DescAct :=
  { q' := d.qhalt, ww := readback sw, wo := readback so,
    di := .stay, dw := .stay, dOut := .stay }

/-- First-match transition lookup; missing keys take the default action. -/
def lookup (d : TMDesc) (q : ℕ) (si sw so : Γ) : DescAct :=
  match d.entries.find? fun e => e.q == q && e.si == si && e.sw == sw && e.so == so with
  | some e => e.act
  | none => d.defaultAct sw so

/-- A description is well-formed when every state field is below `2^w`, so
    the fixed-width binary encoding is faithful. -/
structure WF (d : TMDesc) : Prop where
  qstart_lt : d.qstart < 2 ^ d.w
  qhalt_lt  : d.qhalt < 2 ^ d.w
  entries_q_lt  : ∀ e ∈ d.entries, e.q < 2 ^ d.w
  entries_q'_lt : ∀ e ∈ d.entries, e.act.q' < 2 ^ d.w

end TMDesc

-- ════════════════════════════════════════════════════════════════════════
-- Encoding: description → Γw symbols → bits
-- ════════════════════════════════════════════════════════════════════════

/-- A bit as a desc-tape symbol. -/
def bitSym (b : Bool) : Γw := if b then .one else .zero

/-- A bit string as desc-tape symbols. -/
def bitsToSyms (l : List Bool) : List Γw := l.map bitSym

@[simp] theorem bitsToSyms_length (l : List Bool) : (bitsToSyms l).length = l.length :=
  List.length_map ..

@[simp] theorem bitsToSyms_append (a b : List Bool) :
    bitsToSyms (a ++ b) = bitsToSyms a ++ bitsToSyms b :=
  List.map_append ..

theorem bitSym_ne_blank (b : Bool) : bitSym b ≠ Γw.blank := by
  cases b <;> simp [bitSym]

theorem bitsToSyms_ne_blank {l : List Bool} {s : Γw} (h : s ∈ bitsToSyms l) :
    s ≠ Γw.blank := by
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp h
  exact bitSym_ne_blank b

namespace DescEntry

/-- The desc-tape symbols of one table entry (given state width `w`):
    `q(w) si(2) sw(2) so(2) q'(w) ww(2) wo(2) di(2) dw(2) dOut(2)`,
    `2w + 16` symbols with no separators. -/
def syms (w : ℕ) (e : DescEntry) : List Γw :=
  bitsToSyms (Nat.toBits w e.q) ++ bitsToSyms e.si.encode ++
  bitsToSyms e.sw.encode ++ bitsToSyms e.so.encode ++
  bitsToSyms (Nat.toBits w e.act.q') ++ bitsToSyms e.act.ww.encode ++
  bitsToSyms e.act.wo.encode ++ bitsToSyms e.act.di.encode ++
  bitsToSyms e.act.dw.encode ++ bitsToSyms e.act.dOut.encode

theorem syms_length (w : ℕ) (e : DescEntry) : (e.syms w).length = 2 * w + 16 := by
  simp [syms, Nat.length_toBits, Γ.length_encode, Γw.length_encode, Dir3.length_encode]
  omega

theorem syms_ne_blank {w : ℕ} {e : DescEntry} {s : Γw} (h : s ∈ e.syms w) :
    s ≠ Γw.blank := by
  simp only [syms, List.mem_append] at h
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h <;>
    exact bitsToSyms_ne_blank h

end DescEntry

namespace TMDesc

/-- The desc-tape symbols of a description:
    `qstart(w) □ qhalt(w) □ entry₀ □ ⋯ □ entryₘ □ □`. -/
def syms (d : TMDesc) : List Γw :=
  bitsToSyms (Nat.toBits d.w d.qstart) ++ [Γw.blank] ++
  bitsToSyms (Nat.toBits d.w d.qhalt) ++ [Γw.blank] ++
  (d.entries.flatMap fun e => e.syms d.w ++ [Γw.blank]) ++ [Γw.blank]

end TMDesc

/-- The canonical binary encoding of a description: each desc-tape symbol
    becomes 2 bits via `Γw.encode`. -/
def encodeDesc (d : TMDesc) : List Bool := d.syms.flatMap Γw.encode

-- ════════════════════════════════════════════════════════════════════════
-- Decoding: bits → Γw symbols
-- ════════════════════════════════════════════════════════════════════════

/-- Total 2-bit-group decoding: `00 → 0`, `01 → 1`, and both remaining
    patterns (`10`, `11`) map to the separator `□`. Left inverse of
    `Γw.encode` on the three encodable patterns. -/
def symOfPair : Bool → Bool → Γw
  | false, false => .zero
  | false, true  => .one
  | _,     _     => .blank

/-- Group a bit string into consecutive pairs and decode each; a trailing
    odd bit is dropped. -/
def groupPairs : List Bool → List Γw
  | b₀ :: b₁ :: rest => symOfPair b₀ b₁ :: groupPairs rest
  | _ => []

/-- Decoding pairs is a left inverse of symbol-wise binary encoding. -/
theorem groupPairs_flatMap_encode : ∀ l : List Γw, groupPairs (l.flatMap Γw.encode) = l
  | [] => rfl
  | s :: rest => by
    cases s <;>
      simpa [List.flatMap_cons, Γw.encode, groupPairs, symOfPair]
        using groupPairs_flatMap_encode rest

/-- `groupPairs` distributes over appending at an even boundary. -/
theorem groupPairs_append_of_even : ∀ {a : List Bool}, a.length % 2 = 0 →
    ∀ b : List Bool, groupPairs (a ++ b) = groupPairs a ++ groupPairs b
  | [], _, b => rfl
  | [_], h, _ => by simp at h
  | b₀ :: b₁ :: rest, h, b => by
    have hr : rest.length % 2 = 0 := by
      simp only [List.length_cons] at h; omega
    simp only [List.cons_append, groupPairs, groupPairs_append_of_even hr b]

/-- Every symbol-wise binary encoding has even length. -/
theorem flatMap_encode_length_even (l : List Γw) : (l.flatMap Γw.encode).length % 2 = 0 := by
  induction l with
  | nil => rfl
  | cons s rest ih => simp [Γw.length_encode]

-- ════════════════════════════════════════════════════════════════════════
-- Decoding: Γw symbols → description
-- ════════════════════════════════════════════════════════════════════════

/-- The bit denoted by a desc-tape symbol, if any. -/
def symBit? : Γw → Option Bool
  | .zero  => some false
  | .one   => some true
  | .blank => none

@[simp] theorem symBit?_bitSym (b : Bool) : symBit? (bitSym b) = some b := by
  cases b <;> rfl

/-- Split off the first field: the symbols before the first `□`, and the
    rest after it. An empty first field means the input started with a
    separator (or was empty). -/
def takeField : List Γw → List Γw × List Γw
  | [] => ([], [])
  | .blank :: rest => ([], rest)
  | s :: rest => (s :: (takeField rest).1, (takeField rest).2)

theorem takeField_rest_length : ∀ l : List Γw, (takeField l).2.length ≤ l.length
  | [] => Nat.le_refl _
  | .blank :: _ => Nat.le_succ_of_le (Nat.le_refl _)
  | .zero :: rest => Nat.le_succ_of_le (takeField_rest_length rest)
  | .one :: rest => Nat.le_succ_of_le (takeField_rest_length rest)

/-- On a nonempty input the remainder after the first field is strictly
    shorter — the parse loop terminates. -/
theorem takeField_cons_rest_length (s : Γw) (rest : List Γw) :
    (takeField (s :: rest)).2.length ≤ rest.length := by
  cases s with
  | blank => exact Nat.le_refl _
  | zero => exact takeField_rest_length rest
  | one => exact takeField_rest_length rest

/-- `takeField` recovers a blank-free field followed by a separator. -/
theorem takeField_append {f : List Γw} (hf : ∀ s ∈ f, s ≠ Γw.blank) (r : List Γw) :
    takeField (f ++ Γw.blank :: r) = (f, r) := by
  induction f with
  | nil => rfl
  | cons s rest ih =>
    have hs : s ≠ Γw.blank := hf s (List.mem_cons_self ..)
    have := ih fun t ht => hf t (List.mem_cons_of_mem _ ht)
    cases s with
    | blank => exact absurd rfl hs
    | zero => simp [takeField, this]
    | one => simp [takeField, this]

/-- The number denoted by a field (its bit symbols, read big-endian). -/
def fieldNat (f : List Γw) : ℕ := Nat.fromBits (f.filterMap symBit?)

@[simp] theorem filterMap_symBit?_bitsToSyms (l : List Bool) :
    (bitsToSyms l).filterMap symBit? = l := by
  induction l with
  | nil => rfl
  | cons b rest ih => simp [bitsToSyms]

theorem fieldNat_bitsToSyms_toBits {w v : ℕ} (hv : v < 2 ^ w) :
    fieldNat (bitsToSyms (Nat.toBits w v)) = v := by
  rw [fieldNat, filterMap_symBit?_bitsToSyms, Nat.fromBits_toBits hv]

-- Total 2-bit decoders for the three symbol kinds; the junk pattern `11`
-- takes a fixed harmless value in each case.

/-- Total read-symbol decoder (left inverse of `Γ.encode`). -/
def decΓ (l : List Bool) : Γ :=
  match l with
  | [false, false] => .zero
  | [false, true]  => .one
  | [true, false]  => .blank
  | [true, true]   => .start
  | _ => .blank

/-- Total write-symbol decoder; `11` decodes to `□`. -/
def decΓw (l : List Bool) : Γw :=
  match l with
  | [false, false] => .zero
  | [false, true]  => .one
  | _ => .blank

/-- Total direction decoder; `11` decodes to `stay`. -/
def decDir (l : List Bool) : Dir3 :=
  match l with
  | [false, false] => .left
  | [false, true]  => .right
  | _ => .stay

@[simp] theorem decΓ_encode (s : Γ) : decΓ s.encode = s := by cases s <;> rfl
@[simp] theorem decΓw_encode (s : Γw) : decΓw s.encode = s := by cases s <;> rfl
@[simp] theorem decDir_encode (d : Dir3) : decDir d.encode = d := by cases d <;> rfl

/-- Parse one table entry from a (blank-free) segment: reject if shorter
    than `2w + 16`, otherwise decode the fixed-width fields sequentially
    from the prefix and ignore any excess. -/
def parseEntry (w : ℕ) (seg : List Γw) : Option DescEntry :=
  let bits := seg.filterMap symBit?
  if bits.length < 2 * w + 16 then none
  else
    let qF := bits.take w;    let r₁ := bits.drop w
    let siF := r₁.take 2;     let r₂ := r₁.drop 2
    let swF := r₂.take 2;     let r₃ := r₂.drop 2
    let soF := r₃.take 2;     let r₄ := r₃.drop 2
    let q'F := r₄.take w;     let r₅ := r₄.drop w
    let wwF := r₅.take 2;     let r₆ := r₅.drop 2
    let woF := r₆.take 2;     let r₇ := r₆.drop 2
    let diF := r₇.take 2;     let r₈ := r₇.drop 2
    let dwF := r₈.take 2;     let r₉ := r₈.drop 2
    let dOutF := r₉.take 2
    some
      { q := Nat.fromBits qF, si := decΓ siF, sw := decΓ swF, so := decΓ soF
        act :=
        { q' := Nat.fromBits q'F, ww := decΓw wwF, wo := decΓw woF,
          di := decDir diF, dw := decDir dwF, dOut := decDir dOutF } }

/-- Parse the table: segments are separated by `□`; parseable segments
    become entries, unparseable (too short) segments are skipped, and the
    first *empty* segment (a `□□` or end of input) terminates the table. -/
def parseEntries (w : ℕ) : List Γw → List DescEntry
  | [] => []
  | .blank :: _ => []
  | s :: rest =>
    match parseEntry w (takeField (s :: rest)).1 with
    | some e => e :: parseEntries w (takeField (s :: rest)).2
    | none => parseEntries w (takeField (s :: rest)).2
  termination_by l => l.length
  decreasing_by
    all_goals exact Nat.lt_succ_of_le (takeField_cons_rest_length s rest)

/-- Decode a desc-tape symbol string into a description. The state width is
    the length of the leading `qstart` field; a `qhalt` field of any other
    length denotes the out-of-range sentinel `2^w`. The interpreter can reach
    that halt state through its default action, matching the universal
    machine's symbol-wise comparison with the malformed field. -/
def parseSyms (l : List Γw) : TMDesc :=
  let (qsF, r₁) := takeField l
  let (qhF, r₂) := takeField r₁
  let w := qsF.length
  { w := w
    qstart := fieldNat qsF
    qhalt := if qhF.length = w then fieldNat qhF else 2 ^ w
    entries := parseEntries w r₂ }

/-- Total decoding of a binary string into a machine description. -/
def decodeDesc (α : List Bool) : TMDesc := parseSyms (groupPairs α)

-- ════════════════════════════════════════════════════════════════════════
-- Roundtrip
-- ════════════════════════════════════════════════════════════════════════

/-- Parsing one encoded entry recovers it (when its state fields fit in
    width `w`). -/
theorem parseEntry_syms {w : ℕ} {e : DescEntry}
    (hq : e.q < 2 ^ w) (hq' : e.act.q' < 2 ^ w) :
    parseEntry w (e.syms w) = some e := by
  have hbits : (e.syms w).filterMap symBit?
      = Nat.toBits w e.q ++ (e.si.encode ++ (e.sw.encode ++ (e.so.encode ++
        (Nat.toBits w e.act.q' ++ (e.act.ww.encode ++ (e.act.wo.encode ++
        (e.act.di.encode ++ (e.act.dw.encode ++ e.act.dOut.encode)))))))) := by
    simp [DescEntry.syms, List.filterMap_append, List.append_assoc]
  have hq_len : (Nat.toBits w e.q).length = w := Nat.length_toBits ..
  have hq'_len : (Nat.toBits w e.act.q').length = w := Nat.length_toBits ..
  simp only [parseEntry, hbits]
  rw [ite_eq_right (by
    simp [Nat.length_toBits, Γ.length_encode, Γw.length_encode, Dir3.length_encode]
    omega)]
  rw [List.take_left' hq_len, List.drop_left' hq_len,
      List.take_left' (Γ.length_encode e.si), List.drop_left' (Γ.length_encode e.si),
      List.take_left' (Γ.length_encode e.sw), List.drop_left' (Γ.length_encode e.sw),
      List.take_left' (Γ.length_encode e.so), List.drop_left' (Γ.length_encode e.so),
      List.take_left' hq'_len, List.drop_left' hq'_len,
      List.take_left' (Γw.length_encode e.act.ww), List.drop_left' (Γw.length_encode e.act.ww),
      List.take_left' (Γw.length_encode e.act.wo), List.drop_left' (Γw.length_encode e.act.wo),
      List.take_left' (Dir3.length_encode e.act.di), List.drop_left' (Dir3.length_encode e.act.di),
      List.take_left' (Dir3.length_encode e.act.dw), List.drop_left' (Dir3.length_encode e.act.dw),
      List.take_of_length_le (Nat.le_of_eq (Dir3.length_encode e.act.dOut))]
  simp [Nat.fromBits_toBits hq, Nat.fromBits_toBits hq']

/-- A leading separator (empty segment) terminates the table parse. -/
theorem parseEntries_blank (w : ℕ) (rest : List Γw) :
    parseEntries w (Γw.blank :: rest) = [] := by
  rw [parseEntries]

/-- One-step unfolding of the table parse on a segment-headed input. -/
theorem parseEntries_cons_of_ne_blank {s : Γw} (hs : s ≠ Γw.blank)
    (w : ℕ) (rest : List Γw) :
    parseEntries w (s :: rest) =
      match parseEntry w (takeField (s :: rest)).1 with
      | some e => e :: parseEntries w (takeField (s :: rest)).2
      | none => parseEntries w (takeField (s :: rest)).2 := by
  cases s with
  | blank => exact absurd rfl hs
  | zero => rw [parseEntries]; simp
  | one => rw [parseEntries]; simp

/-- Parsing the encoded table recovers it, ignoring anything after the
    terminating empty segment. -/
theorem parseEntries_syms {w : ℕ} {es : List DescEntry}
    (hq : ∀ e ∈ es, e.q < 2 ^ w) (hq' : ∀ e ∈ es, e.act.q' < 2 ^ w)
    (junk : List Γw) :
    parseEntries w ((es.flatMap fun e => e.syms w ++ [Γw.blank]) ++ Γw.blank :: junk)
      = es := by
  induction es with
  | nil => simpa using parseEntries_blank w junk
  | cons e es' ih =>
    have hassoc : ((e :: es').flatMap fun e => e.syms w ++ [Γw.blank]) ++ Γw.blank :: junk
        = e.syms w ++ Γw.blank ::
            ((es'.flatMap fun e => e.syms w ++ [Γw.blank]) ++ Γw.blank :: junk) := by
      simp [List.append_assoc]
    obtain ⟨s, tail, hsyms⟩ : ∃ s tail, e.syms w = s :: tail := by
      cases h : e.syms w with
      | nil =>
        have := e.syms_length w
        rw [h] at this
        simp at this
      | cons s t => exact ⟨s, t, rfl⟩
    have hs : s ≠ Γw.blank := DescEntry.syms_ne_blank (hsyms ▸ List.mem_cons_self ..)
    rw [hassoc, hsyms, List.cons_append, parseEntries_cons_of_ne_blank hs,
        ← List.cons_append, ← hsyms,
        takeField_append (fun t ht => DescEntry.syms_ne_blank ht),
        parseEntry_syms (hq e (List.mem_cons_self ..)) (hq' e (List.mem_cons_self ..))]
    exact congrArg (e :: ·)
      (ih (fun e' he' => hq e' (List.mem_cons_of_mem _ he'))
          (fun e' he' => hq' e' (List.mem_cons_of_mem _ he')))

/-- **Roundtrip with padding**: decoding an encoded well-formed description
    recovers it exactly, no matter what junk follows the encoding. This
    gives every description infinitely many encodings — the padding fact
    the hierarchy-theorem diagonalization relies on. -/
theorem decodeDesc_encodeDesc_append {d : TMDesc} (hd : d.WF) (junk : List Bool) :
    decodeDesc (encodeDesc d ++ junk) = d := by
  have hgroup : groupPairs (encodeDesc d ++ junk) = d.syms ++ groupPairs junk := by
    rw [encodeDesc, groupPairs_append_of_even (flatMap_encode_length_even _),
        groupPairs_flatMap_encode]
  have hassoc : d.syms ++ groupPairs junk
      = bitsToSyms (Nat.toBits d.w d.qstart) ++ Γw.blank ::
          (bitsToSyms (Nat.toBits d.w d.qhalt) ++ Γw.blank ::
            ((d.entries.flatMap fun e => e.syms d.w ++ [Γw.blank]) ++
              Γw.blank :: groupPairs junk)) := by
    simp [TMDesc.syms, List.append_assoc]
  have hlen_s : (bitsToSyms (Nat.toBits d.w d.qstart)).length = d.w := by
    simp [Nat.length_toBits]
  have hlen_h : (bitsToSyms (Nat.toBits d.w d.qhalt)).length = d.w := by
    simp [Nat.length_toBits]
  rw [decodeDesc, hgroup, hassoc, parseSyms,
      takeField_append (fun s hs => bitsToSyms_ne_blank hs)]
  dsimp only
  rw [takeField_append (fun s hs => bitsToSyms_ne_blank hs)]
  simp only [hlen_s, hlen_h, ite_true,
      fieldNat_bitsToSyms_toBits hd.qstart_lt,
      fieldNat_bitsToSyms_toBits hd.qhalt_lt,
      parseEntries_syms hd.entries_q_lt hd.entries_q'_lt]

/-- **Roundtrip**: decoding an encoded well-formed description recovers it. -/
theorem decodeDesc_encodeDesc {d : TMDesc} (hd : d.WF) :
    decodeDesc (encodeDesc d) = d := by
  simpa using decodeDesc_encodeDesc_append hd []

end Complexity
