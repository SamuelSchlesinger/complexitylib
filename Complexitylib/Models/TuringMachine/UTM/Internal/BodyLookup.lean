/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.Verdict
public import Complexitylib.Models.TuringMachine.UTM.Internal.BodyApply
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Match-loop ↔ lookup correspondence (pure list level)

The body machine's key scan accepts a desc-tape segment exactly when the
abstract table lookup (`TMDesc.lookup`) would select the entry parsed from
that segment. This file proves the correspondence at the pure list level —
no machine steps (design appendix 2):

- `keyCells` / `keyCells_get` — the six expected key-symbol cells of
  `Body.keyCell`, as a `Γw` list;
- `MachMatch` — the machine's segment-acceptance predicate (state-field
  prefix, six key cells, and full value length);
- `machMatch_iff_parse` — on a `□`-free segment, `MachMatch` holds iff the
  segment parses (`parseEntry`) with exactly the sought key;
- `machFind` + `machFind_some_find?` / `machFind_none_find?` /
  `firstMatch_lookup` / `noMatch_lookup` — the machine's first matching
  segment in the `takeField` split is the `find?` hit of
  `parseEntries`, so its action is exactly `TMDesc.lookup`'s result (and
  no match ⟺ the default action);
- `value_slices` — the matched segment's value cells decode (via
  `cellBit`/`grpΓw`/`grpDir`, the machine's decoders) to the parsed
  entry's action fields.
-/


@[expose] public section

namespace Complexity

namespace TM.UTMBody

-- ════════════════════════════════════════════════════════════════════════
-- Bit-symbol translation helpers
-- ════════════════════════════════════════════════════════════════════════

/-- `bitSym` and `bitCell` denote the same cell content. -/
theorem bitSym_toΓ (b : Bool) : (bitSym b).toΓ = bitCell b := by
  cases b <;> rfl

/-- `bitSym` is injective. -/
theorem bitSym_injective : Function.Injective bitSym := by
  intro a b h
  cases a <;> cases b <;> simp [bitSym] at h ⊢

/-- `bitsToSyms` is injective. -/
theorem bitsToSyms_injective : Function.Injective bitsToSyms :=
  fun _ _ h => List.map_injective_iff.mpr bitSym_injective h

/-- `bitsToSyms` commutes with `take`. -/
theorem bitsToSyms_take (l : List Bool) (n : ℕ) :
    bitsToSyms (l.take n) = (bitsToSyms l).take n :=
  List.map_take ..

/-- `bitsToSyms` commutes with `drop`. -/
theorem bitsToSyms_drop (l : List Bool) (n : ℕ) :
    bitsToSyms (l.drop n) = (bitsToSyms l).drop n :=
  List.map_drop ..

/-- On a `□`-free list the (total) bit translation is the machine's
    `cellBit` read of each cell. -/
theorem filterMap_symBit?_eq_map_cellBit :
    ∀ {l : List Γw}, (∀ s ∈ l, s ≠ Γw.blank) →
      l.filterMap symBit? = l.map fun s => cellBit s.toΓ
  | [], _ => rfl
  | s :: rest, h => by
    have ih := filterMap_symBit?_eq_map_cellBit
      (fun t ht => h t (List.mem_cons_of_mem _ ht))
    cases s with
    | blank => exact absurd rfl (h _ (List.mem_cons_self ..))
    | zero => simpa [symBit?, cellBit] using ih
    | one => simpa [symBit?, cellBit] using ih

/-- A length-2 bit list is the encoding of the symbol it `decΓ`-decodes to
    (`decΓ` is a bijection on 2-bit patterns). -/
theorem eq_encode_of_decΓ_eq {l : List Bool} (hl : l.length = 2) {s : Γ}
    (h : decΓ l = s) : l = s.encode := by
  match l, hl with
  | [a, b], _ => cases a <;> cases b <;> cases s <;> simp_all [decΓ, Γ.encode]

/-- Composed `drop`s collapse to a single `drop` (index-arithmetic form). -/
private theorem drop_add {α : Type _} (l : List α) {m n k : ℕ} (h : m + n = k) :
    (l.drop m).drop n = l.drop k := by
  rw [List.drop_drop, h]

/-- A 6-element prefix as its three 2-element groups. -/
private theorem take_six_decomp {α : Type _} (l : List α) :
    l.take 6 = l.take 2 ++ ((l.drop 2).take 2 ++ ((l.drop 2).drop 2).take 2) := by
  rw [show (6 : ℕ) = 2 + 4 from rfl, List.take_add,
      show (4 : ℕ) = 2 + 2 from rfl, List.take_add]

/-- A 2-element `take`-of-`drop` slice as its two cells. -/
private theorem drop_take_two {α : Type _} {l : List α} {i : ℕ}
    (h : i + 1 < l.length) :
    (l.drop i).take 2 = [l[i]'(by omega), l[i + 1]'h] := by
  rw [List.drop_eq_getElem_cons (by omega : i < l.length),
      List.drop_eq_getElem_cons h]
  rfl

-- ════════════════════════════════════════════════════════════════════════
-- 1. The six expected key-symbol cells
-- ════════════════════════════════════════════════════════════════════════

/-- The six expected key-symbol cells of the scan (`Body.keyCell`), as a
    list: the bit symbols of the three simulated reads' encodings. -/
def keyCells (f : VFlags) (v0 v1 v2 : Γ) : List Γw :=
  bitsToSyms ((simRead f.1 v0).encode ++ (simRead f.2.1 v1).encode ++
    (simRead f.2.2 v2).encode)

@[simp] theorem keyCells_length (f : VFlags) (v0 v1 v2 : Γ) :
    (keyCells f v0 v1 v2).length = 6 := by
  simp [keyCells, Γ.length_encode]

/-- `keyCells` read as `Γ` cells is exactly `keyCell 0 .. keyCell 5`. -/
theorem keyCells_map_toΓ (f : VFlags) (v0 v1 v2 : Γ) :
    (keyCells f v0 v1 v2).map Γw.toΓ =
      [keyCell f v0 v1 v2 0, keyCell f v0 v1 v2 1, keyCell f v0 v1 v2 2,
       keyCell f v0 v1 v2 3, keyCell f v0 v1 v2 4, keyCell f v0 v1 v2 5] := by
  simp only [keyCells, keyCell]
  generalize simRead f.1 v0 = s0
  generalize simRead f.2.1 v1 = s1
  generalize simRead f.2.2 v2 = s2
  cases s0 <;> cases s1 <;> cases s2 <;> rfl

/-- Pointwise form: cell `idx` of `keyCells`, read as `Γ`, is
    `keyCell idx`. -/
theorem keyCells_get (f : VFlags) (v0 v1 v2 : Γ) (idx : Fin 6) :
    ((keyCells f v0 v1 v2)[idx.val]'
        (by rw [keyCells_length]; exact idx.isLt)).toΓ
      = keyCell f v0 v1 v2 idx := by
  have hlt : idx.val < ((keyCells f v0 v1 v2).map Γw.toΓ).length := by
    rw [List.length_map, keyCells_length]; exact idx.isLt
  have h := List.getElem_of_eq (keyCells_map_toΓ f v0 v1 v2) hlt
  rw [List.getElem_map] at h
  rw [h]
  fin_cases idx <;> rfl

-- ════════════════════════════════════════════════════════════════════════
-- 2. The machine's segment-acceptance predicate
-- ════════════════════════════════════════════════════════════════════════

/-- **The machine's segment-acceptance predicate**: the segment starts with
    the state-tape symbols (`cmpQ`'s lockstep compare), followed by the six
    expected key cells (`cmpS`), and is long enough for the full value copy
    (`copyQ'`/`copyAct` find no early `□` — on the `□`-free segments
    `takeField` produces, length is exactly that condition). -/
def MachMatch (w : ℕ) (stSyms keyCs seg : List Γw) : Prop :=
  seg.take w = stSyms ∧ (seg.drop w).take 6 = keyCs ∧ 2 * w + 16 ≤ seg.length

instance (w : ℕ) (stSyms keyCs seg : List Γw) :
    Decidable (MachMatch w stSyms keyCs seg) := by
  unfold MachMatch; infer_instance

-- ════════════════════════════════════════════════════════════════════════
-- parseEntry inversion
-- ════════════════════════════════════════════════════════════════════════

/-- `parseEntry` in closed form, with normalized field offsets:
    key `q si sw so` at bit offsets `0, w, w+2, w+4`; action
    `q' ww wo di dw dOut` at `w+6, 2w+6, 2w+8, 2w+10, 2w+12, 2w+14`. -/
private theorem parseEntry_eq (w : ℕ) (seg : List Γw) :
    parseEntry w seg =
      if 2 * w + 16 ≤ (seg.filterMap symBit?).length then
        some
          { q := Nat.fromBits ((seg.filterMap symBit?).take w)
            si := decΓ (((seg.filterMap symBit?).drop w).take 2)
            sw := decΓ (((seg.filterMap symBit?).drop (w + 2)).take 2)
            so := decΓ (((seg.filterMap symBit?).drop (w + 4)).take 2)
            act :=
            { q' := Nat.fromBits (((seg.filterMap symBit?).drop (w + 6)).take w)
              ww := decΓw (((seg.filterMap symBit?).drop (2 * w + 6)).take 2)
              wo := decΓw (((seg.filterMap symBit?).drop (2 * w + 8)).take 2)
              di := decDir (((seg.filterMap symBit?).drop (2 * w + 10)).take 2)
              dw := decDir (((seg.filterMap symBit?).drop (2 * w + 12)).take 2)
              dOut := decDir (((seg.filterMap symBit?).drop (2 * w + 14)).take 2) } }
      else none := by
  rw [parseEntry]
  by_cases hlen : (seg.filterMap symBit?).length < 2 * w + 16
  · rw [ite_eq_left hlen, ite_eq_right (by omega)]
  · rw [ite_eq_right hlen, ite_eq_left (by omega)]
    dsimp only
    rw [drop_add _ (rfl : w + 2 = w + 2),
        drop_add _ (by omega : w + 2 + 2 = w + 4),
        drop_add _ (by omega : w + 4 + 2 = w + 6),
        drop_add _ (by omega : w + 6 + w = 2 * w + 6),
        drop_add _ (by omega : 2 * w + 6 + 2 = 2 * w + 8),
        drop_add _ (by omega : 2 * w + 8 + 2 = 2 * w + 10),
        drop_add _ (by omega : 2 * w + 10 + 2 = 2 * w + 12),
        drop_add _ (by omega : 2 * w + 12 + 2 = 2 * w + 14)]

-- ════════════════════════════════════════════════════════════════════════
-- 3. The parse bridge
-- ════════════════════════════════════════════════════════════════════════

/-- **The parse bridge**: on a `□`-free segment, the machine's acceptance
    predicate (state field = the `w`-bit encoding of `q`, six key cells =
    `keyCells` of the simulated reads, full value length) holds iff the
    segment parses to an entry whose key is exactly `(q, simRead …)`. -/
theorem machMatch_iff_parse {w q : ℕ} (hq : q < 2 ^ w) (f : VFlags)
    (v0 v1 v2 : Γ) {seg : List Γw} (hnb : ∀ s ∈ seg, s ≠ Γw.blank) :
    MachMatch w (bitsToSyms (Nat.toBits w q)) (keyCells f v0 v1 v2) seg ↔
      ∃ e, parseEntry w seg = some e ∧ e.q = q ∧ e.si = simRead f.1 v0 ∧
        e.sw = simRead f.2.1 v1 ∧ e.so = simRead f.2.2 v2 := by
  have hseg : bitsToSyms (seg.filterMap symBit?) = seg :=
    bitsToSyms_filterMap_of_ne_blank hnb
  have hlen : (seg.filterMap symBit?).length = seg.length := by
    conv_rhs => rw [← hseg]
    rw [bitsToSyms_length]
  rw [MachMatch, parseEntry_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [ite_eq_left (by omega)]
    have hkey : ((seg.filterMap symBit?).drop w).take 6
        = (simRead f.1 v0).encode ++ (simRead f.2.1 v1).encode ++
          (simRead f.2.2 v2).encode := by
      apply bitsToSyms_injective
      rw [bitsToSyms_take, bitsToSyms_drop, hseg]
      exact h2
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · -- q field
      show Nat.fromBits ((seg.filterMap symBit?).take w) = q
      have h1' : bitsToSyms ((seg.filterMap symBit?).take w)
          = bitsToSyms (Nat.toBits w q) := by
        rw [bitsToSyms_take, hseg, h1]
      rw [bitsToSyms_injective h1', Nat.fromBits_toBits hq]
    · -- si field
      show decΓ (((seg.filterMap symBit?).drop w).take 2) = simRead f.1 v0
      have : ((seg.filterMap symBit?).drop w).take 2 = (simRead f.1 v0).encode := by
        have ht : (((seg.filterMap symBit?).drop w).take 6).take 2
            = ((seg.filterMap symBit?).drop w).take 2 := by
          simp [List.take_take]
        rw [← ht, hkey, List.append_assoc, List.take_left' (Γ.length_encode _)]
      rw [this, decΓ_encode]
    · -- sw field
      show decΓ (((seg.filterMap symBit?).drop (w + 2)).take 2) = simRead f.2.1 v1
      have : ((seg.filterMap symBit?).drop (w + 2)).take 2
          = (simRead f.2.1 v1).encode := by
        rw [← drop_add _ (rfl : w + 2 = w + 2), List.take_drop,
            show (2 + 2 : ℕ) = 4 from rfl]
        have ht : ((seg.filterMap symBit?).drop w).take 4
            = (((seg.filterMap symBit?).drop w).take 6).take 4 := by
          simp [List.take_take]
        rw [ht, hkey, List.take_left' (by simp [Γ.length_encode]),
            List.drop_left' (Γ.length_encode _)]
      rw [this, decΓ_encode]
    · -- so field
      show decΓ (((seg.filterMap symBit?).drop (w + 4)).take 2) = simRead f.2.2 v2
      have : ((seg.filterMap symBit?).drop (w + 4)).take 2
          = (simRead f.2.2 v2).encode := by
        rw [← drop_add _ (rfl : w + 4 = w + 4), List.take_drop,
            show (4 + 2 : ℕ) = 6 from rfl, hkey,
            List.drop_left' (by simp [Γ.length_encode])]
      rw [this, decΓ_encode]
  · rintro ⟨e, hpe, hq', hsi, hsw, hso⟩
    by_cases hc : 2 * w + 16 ≤ (seg.filterMap symBit?).length
    · rw [ite_eq_left hc] at hpe
      injection hpe with hpe
      subst hpe
      dsimp only at hq' hsi hsw hso
      refine ⟨?_, ?_, by omega⟩
      · -- state field
        have hwlen : ((seg.filterMap symBit?).take w).length = w := by
          rw [List.length_take]; omega
        have hbits := Nat.toBits_fromBits ((seg.filterMap symBit?).take w)
        rw [hwlen, hq'] at hbits
        rw [hbits, bitsToSyms_take, hseg]
      · -- key cells
        have hsi' : ((seg.filterMap symBit?).drop w).take 2
            = (simRead f.1 v0).encode :=
          eq_encode_of_decΓ_eq
            (by rw [List.length_take, List.length_drop]; omega) hsi
        have hsw' : ((seg.filterMap symBit?).drop (w + 2)).take 2
            = (simRead f.2.1 v1).encode :=
          eq_encode_of_decΓ_eq
            (by rw [List.length_take, List.length_drop]; omega) hsw
        have hso' : ((seg.filterMap symBit?).drop (w + 4)).take 2
            = (simRead f.2.2 v2).encode :=
          eq_encode_of_decΓ_eq
            (by rw [List.length_take, List.length_drop]; omega) hso
        have hkey : ((seg.filterMap symBit?).drop w).take 6
            = (simRead f.1 v0).encode ++ ((simRead f.2.1 v1).encode ++
              (simRead f.2.2 v2).encode) := by
          rw [take_six_decomp, hsi',
              drop_add _ (rfl : w + 2 = w + 2), hsw',
              drop_add _ (by omega : w + 2 + 2 = w + 4), hso']
        rw [← hseg, ← bitsToSyms_drop, ← bitsToSyms_take, hkey, keyCells,
            List.append_assoc]
    · rw [ite_eq_right hc] at hpe
      exact absurd hpe (by simp)

-- ════════════════════════════════════════════════════════════════════════
-- 4. The first-match correspondence
-- ════════════════════════════════════════════════════════════════════════

/-- The machine's segment walk at the list level: the first segment of the
    `takeField` split that satisfies `MachMatch`, stopping (like
    `parseEntries`) at the first empty segment. -/
def machFind (w : ℕ) (stSyms keyCs : List Γw) : List Γw → Option (List Γw)
  | [] => none
  | .blank :: _ => none
  | s :: rest =>
    if MachMatch w stSyms keyCs (takeField (s :: rest)).1 then
      some (takeField (s :: rest)).1
    else machFind w stSyms keyCs (takeField (s :: rest)).2
  termination_by l => l.length
  decreasing_by
    all_goals exact Nat.lt_succ_of_le (takeField_cons_rest_length s rest)

/-- One-step unfolding of `machFind` on a segment-headed input. -/
theorem machFind_cons_of_ne_blank {s : Γw} (hs : s ≠ Γw.blank)
    (w : ℕ) (stSyms keyCs rest : List Γw) :
    machFind w stSyms keyCs (s :: rest) =
      if MachMatch w stSyms keyCs (takeField (s :: rest)).1 then
        some (takeField (s :: rest)).1
      else machFind w stSyms keyCs (takeField (s :: rest)).2 := by
  cases s with
  | blank => exact absurd rfl hs
  | zero => rw [machFind]; exact fun h => nomatch h
  | one => rw [machFind]; exact fun h => nomatch h

/-- What `machFind` returns is a `□`-free segment that `MachMatch`es. -/
theorem machFind_matches (w : ℕ) (stSyms keyCs : List Γw) :
    ∀ R seg : List Γw, machFind w stSyms keyCs R = some seg →
      MachMatch w stSyms keyCs seg ∧ ∀ s ∈ seg, s ≠ Γw.blank
  | [] => by simp [machFind]
  | .blank :: rest => by simp [machFind]
  | s :: rest => by
    intro seg h
    by_cases hs : s = Γw.blank
    · subst hs
      simp [machFind] at h
    · rw [machFind_cons_of_ne_blank hs] at h
      by_cases hm : MachMatch w stSyms keyCs (takeField (s :: rest)).1
      · rw [ite_eq_left hm] at h
        injection h with h
        subst h
        exact ⟨hm, takeField_fst_ne_blank _⟩
      · rw [ite_eq_right hm] at h
        exact machFind_matches w stSyms keyCs (takeField (s :: rest)).2 seg h
  termination_by R => R.length
  decreasing_by
    all_goals exact Nat.lt_succ_of_le (takeField_cons_rest_length s rest)

/-- The key predicate of `TMDesc.lookup`'s `find?`. -/
def keyMatch (q : ℕ) (si sw so : Γ) (e : DescEntry) : Bool :=
  e.q == q && e.si == si && e.sw == sw && e.so == so

/-- `TMDesc.lookup` in terms of `keyMatch`. -/
theorem lookup_eq_find? (d : TMDesc) (q : ℕ) (si sw so : Γ) :
    d.lookup q si sw so =
      match d.entries.find? (keyMatch q si sw so) with
      | some e => e.act
      | none => d.defaultAct sw so := rfl

/-- **The first-match correspondence**, combined form: the `find?` hit of
    the parsed table is exactly the parse of the machine's first
    `MachMatch`-ing segment. -/
theorem find?_parseEntries_eq_machFind (w q : ℕ) (hq : q < 2 ^ w)
    (f : VFlags) (v0 v1 v2 : Γ) :
    ∀ R : List Γw,
      (parseEntries w R).find?
          (keyMatch q (simRead f.1 v0) (simRead f.2.1 v1) (simRead f.2.2 v2))
        = (machFind w (bitsToSyms (Nat.toBits w q))
            (keyCells f v0 v1 v2) R).bind (parseEntry w)
  | [] => by simp [machFind, parseEntries]
  | .blank :: rest => by simp [machFind, parseEntries_blank]
  | s :: rest => by
    by_cases hs : s = Γw.blank
    · subst hs
      simp [machFind, parseEntries_blank]
    · rw [parseEntries_cons_of_ne_blank hs, machFind_cons_of_ne_blank hs]
      have hnb : ∀ x ∈ (takeField (s :: rest)).1, x ≠ Γw.blank :=
        takeField_fst_ne_blank _
      by_cases hm : MachMatch w (bitsToSyms (Nat.toBits w q))
        (keyCells f v0 v1 v2) (takeField (s :: rest)).1
      · rw [ite_eq_left hm]
        obtain ⟨e, hpe, hq', hsi, hsw, hso⟩ :=
          (machMatch_iff_parse hq f v0 v1 v2 hnb).mp hm
        simp only [hpe, Option.bind_some]
        exact List.find?_cons_of_pos
          (by simp [keyMatch, hq', hsi, hsw, hso])
      · rw [ite_eq_right hm]
        cases hpe : parseEntry w (takeField (s :: rest)).1 with
        | none =>
          exact find?_parseEntries_eq_machFind w q hq f v0 v1 v2
            (takeField (s :: rest)).2
        | some e =>
          rw [List.find?_cons_of_neg (by
            intro hkm
            simp only [keyMatch, Bool.and_eq_true, beq_iff_eq] at hkm
            obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hkm
            exact hm ((machMatch_iff_parse hq f v0 v1 v2 hnb).mpr
              ⟨e, hpe, h1, h2, h3, h4⟩))]
          exact find?_parseEntries_eq_machFind w q hq f v0 v1 v2
            (takeField (s :: rest)).2
  termination_by R => R.length
  decreasing_by
    all_goals exact Nat.lt_succ_of_le (takeField_cons_rest_length s rest)

/-- **(a) The machine's first hit is the lookup's first hit**: if the
    machine's segment walk accepts `seg`, then `seg` parses to an entry `e`,
    and `e` is exactly the table's `find?` hit for the sought key. -/
theorem machFind_some_find? {w q : ℕ} (hq : q < 2 ^ w) (f : VFlags)
    (v0 v1 v2 : Γ) {R seg : List Γw}
    (h : machFind w (bitsToSyms (Nat.toBits w q)) (keyCells f v0 v1 v2) R
      = some seg) :
    ∃ e, parseEntry w seg = some e ∧
      (parseEntries w R).find?
          (keyMatch q (simRead f.1 v0) (simRead f.2.1 v1) (simRead f.2.2 v2))
        = some e ∧
      MachMatch w (bitsToSyms (Nat.toBits w q)) (keyCells f v0 v1 v2) seg := by
  obtain ⟨hm, hnb⟩ := machFind_matches _ _ _ R _ h
  obtain ⟨e, hpe, -⟩ := (machMatch_iff_parse hq f v0 v1 v2 hnb).mp hm
  refine ⟨e, hpe, ?_, hm⟩
  rw [find?_parseEntries_eq_machFind w q hq f v0 v1 v2 R, h]
  exact hpe

/-- **(b) No machine hit ⟺ no lookup hit**: if the machine's segment walk
    rejects every segment, the table's `find?` misses. -/
theorem machFind_none_find? {w q : ℕ} (hq : q < 2 ^ w) (f : VFlags)
    (v0 v1 v2 : Γ) {R : List Γw}
    (h : machFind w (bitsToSyms (Nat.toBits w q)) (keyCells f v0 v1 v2) R
      = none) :
    (parseEntries w R).find?
        (keyMatch q (simRead f.1 v0) (simRead f.2.1 v1) (simRead f.2.2 v2))
      = none := by
  rw [find?_parseEntries_eq_machFind w q hq f v0 v1 v2 R, h]
  rfl

/-- **First-match ⇒ lookup**: the action of the entry parsed from the
    machine's first `MachMatch`-ing segment is exactly what `TMDesc.lookup`
    returns on the table parsed from the same entry region. -/
theorem firstMatch_lookup {w q : ℕ} (hq : q < 2 ^ w) (f : VFlags)
    (v0 v1 v2 : Γ) (qs qh : ℕ) {R seg : List Γw}
    (h : machFind w (bitsToSyms (Nat.toBits w q)) (keyCells f v0 v1 v2) R
      = some seg) :
    ∃ e, parseEntry w seg = some e ∧
      MachMatch w (bitsToSyms (Nat.toBits w q)) (keyCells f v0 v1 v2) seg ∧
      (TMDesc.mk w qs qh (parseEntries w R)).lookup q (simRead f.1 v0)
          (simRead f.2.1 v1) (simRead f.2.2 v2) = e.act := by
  obtain ⟨e, hpe, hfind, hm⟩ := machFind_some_find? hq f v0 v1 v2 h
  exact ⟨e, hpe, hm, by rw [lookup_eq_find?, hfind]⟩

/-- **No match ⇒ default**: if the machine's segment walk rejects every
    segment, `TMDesc.lookup` on the parsed table falls to the default
    action. -/
theorem noMatch_lookup {w q : ℕ} (hq : q < 2 ^ w) (f : VFlags)
    (v0 v1 v2 : Γ) (qs qh : ℕ) {R : List Γw}
    (h : machFind w (bitsToSyms (Nat.toBits w q)) (keyCells f v0 v1 v2) R
      = none) :
    (TMDesc.mk w qs qh (parseEntries w R)).lookup q (simRead f.1 v0)
        (simRead f.2.1 v1) (simRead f.2.2 v2)
      = (TMDesc.mk w qs qh (parseEntries w R)).defaultAct
          (simRead f.2.1 v1) (simRead f.2.2 v2) := by
  rw [lookup_eq_find?, machFind_none_find? hq f v0 v1 v2 h]

-- ════════════════════════════════════════════════════════════════════════
-- 5. The value decode bridge
-- ════════════════════════════════════════════════════════════════════════

/-- The bit value the machine decodes from desc-segment cell `i`
    (out-of-range reads default to `□`, i.e. `false`; the machine reads the
    cell as `Γ` and applies `cellBit`). -/
def segBit (seg : List Γw) (i : ℕ) : Bool := cellBit ((seg.getD i Γw.blank).toΓ)

/-- In range, `segBit` is the `cellBit` read of the cell. -/
theorem segBit_eq {seg : List Γw} {i : ℕ} (h : i < seg.length) :
    segBit seg i = cellBit ((seg[i]'h).toΓ) := by
  rw [segBit, List.getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- On a `□`-free segment, bit `i` of the parse's bit string is `segBit i`. -/
private theorem filterMap_getElem_eq_segBit {seg : List Γw}
    (hnb : ∀ s ∈ seg, s ≠ Γw.blank) {i : ℕ}
    (h : i < (seg.filterMap symBit?).length) :
    (seg.filterMap symBit?)[i] = segBit seg i := by
  have hmap := filterMap_symBit?_eq_map_cellBit hnb
  have hi : i < seg.length := by
    rw [hmap, List.length_map] at h
    exact h
  rw [segBit_eq hi, List.getElem_of_eq hmap h, List.getElem_map]

/-- **The value decode bridge**: on a `□`-free segment that parses to `e`,
    the value cells decode to `e.act` exactly as the machine reads them —
    the `w`-cell state field at offset `w+6` is the bit-symbol encoding of
    `e.act.q'`, and the five 2-cell groups at offsets `2w+6 .. 2w+14`
    decode via `grpΓw`/`grpDir` of the `cellBit` cell reads to
    `ww`/`wo`/`di`/`dw`/`dOut`. -/
theorem value_slices {w : ℕ} {seg : List Γw} {e : DescEntry}
    (hnb : ∀ s ∈ seg, s ≠ Γw.blank) (hp : parseEntry w seg = some e) :
    (seg.drop (w + 6)).take w = bitsToSyms (Nat.toBits w e.act.q') ∧
    grpΓw (segBit seg (2 * w + 6)) (segBit seg (2 * w + 7)) = e.act.ww ∧
    grpΓw (segBit seg (2 * w + 8)) (segBit seg (2 * w + 9)) = e.act.wo ∧
    grpDir (segBit seg (2 * w + 10)) (segBit seg (2 * w + 11)) = e.act.di ∧
    grpDir (segBit seg (2 * w + 12)) (segBit seg (2 * w + 13)) = e.act.dw ∧
    grpDir (segBit seg (2 * w + 14)) (segBit seg (2 * w + 15)) = e.act.dOut := by
  have hseg : bitsToSyms (seg.filterMap symBit?) = seg :=
    bitsToSyms_filterMap_of_ne_blank hnb
  rw [parseEntry_eq] at hp
  by_cases hc : 2 * w + 16 ≤ (seg.filterMap symBit?).length
  swap
  · rw [ite_eq_right hc] at hp
    exact absurd hp (by simp)
  rw [ite_eq_left hc] at hp
  injection hp with hp
  subst hp
  have hgrp : ∀ i j : ℕ, i + 1 = j → j < (seg.filterMap symBit?).length →
      ((seg.filterMap symBit?).drop i).take 2
        = [segBit seg i, segBit seg j] := by
    intro i j hij hj
    subst hij
    rw [drop_take_two hj, filterMap_getElem_eq_segBit hnb,
        filterMap_getElem_eq_segBit hnb]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the q' field
    dsimp only
    have hq'len : (((seg.filterMap symBit?).drop (w + 6)).take w).length = w := by
      rw [List.length_take, List.length_drop]; omega
    have h1 := Nat.toBits_fromBits (((seg.filterMap symBit?).drop (w + 6)).take w)
    rw [hq'len] at h1
    rw [h1, bitsToSyms_take, bitsToSyms_drop, hseg]
  · dsimp only
    rw [hgrp (2 * w + 6) (2 * w + 7) (by omega) (by omega), ← grpΓw_eq_decΓw]
  · dsimp only
    rw [hgrp (2 * w + 8) (2 * w + 9) (by omega) (by omega), ← grpΓw_eq_decΓw]
  · dsimp only
    rw [hgrp (2 * w + 10) (2 * w + 11) (by omega) (by omega), ← grpDir_eq_decDir]
  · dsimp only
    rw [hgrp (2 * w + 12) (2 * w + 13) (by omega) (by omega), ← grpDir_eq_decDir]
  · dsimp only
    rw [hgrp (2 * w + 14) (2 * w + 15) (by omega) (by omega), ← grpDir_eq_decDir]

end TM.UTMBody

end Complexity
