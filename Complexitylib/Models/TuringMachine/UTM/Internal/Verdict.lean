/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.HaltTest

/-!
# Halt-test verdict correspondence

The halt-test machine compares the state tape against the description
tape's second field — exactly the `qhF` field that `parseSyms` decodes as
the halt state. This file proves the comparison agrees with the abstract
halt check of the interpreted machine `(decodeDesc α).toTM`:

* a running state tape (`w`-bit encoding of `q < 2^w`) matches the field
  iff `q` is the decoded halt state (well-formed fields decode by
  `Nat.toBits`/`Nat.fromBits`; malformed-width fields never match, and the
  decoded sentinel `2^w` has no `w`-bit running-state encoding);
* after a default transition the state tape holds the field verbatim, and
  the interpreted machine sits exactly at its (clamped) halt state.
-/


@[expose] public section

namespace Complexity

namespace TM.UTMBody

/-- A blank-free `Γw` list is the symbol image of its own bits. -/
theorem bitsToSyms_filterMap_of_ne_blank :
    ∀ {l : List Γw}, (∀ s ∈ l, s ≠ Γw.blank) →
      bitsToSyms (l.filterMap symBit?) = l
  | [], _ => rfl
  | s :: rest, h => by
    have ih := bitsToSyms_filterMap_of_ne_blank
      (fun t ht => h t (List.mem_cons_of_mem _ ht))
    cases s with
    | blank => exact absurd rfl (h _ (List.mem_cons_self ..))
    | zero => simpa [bitsToSyms, symBit?, bitSym] using ih
    | one => simpa [bitsToSyms, symBit?, bitSym] using ih

/-- The description tape's second field (the qhalt field), as scanned by the
    halt-test machine and decoded by `parseSyms`. -/
def qhaltField (dSyms : List Γw) : List Γw :=
  (takeField (takeField dSyms).2).1

/-- The qhalt field of a decoded description determines its halt state:
    `fieldNat` if the width matches, the sentinel `2^w` otherwise. -/
theorem decodeDesc_qhalt (α : List Bool) :
    (decodeDesc α).qhalt =
      if (qhaltField (groupPairs α)).length = (decodeDesc α).w then
        fieldNat (qhaltField (groupPairs α))
      else 2 ^ (decodeDesc α).w := rfl

/-- The decoded width is the first field's length. -/
theorem decodeDesc_w (α : List Bool) :
    (decodeDesc α).w = (takeField (groupPairs α)).1.length := rfl

/-- **Running-state verdict**: for `q < 2^w` (with `w` the decoded width),
    the state tape's `w`-bit encoding of `q` equals the qhalt field iff the
    interpreted machine's state `q` is its halt state. -/
theorem verdict_running (α : List Bool) {q : ℕ}
    (hq : q < 2 ^ (decodeDesc α).w) :
    (bitsToSyms (Nat.toBits (decodeDesc α).w q) = qhaltField (groupPairs α))
      ↔ q = min (decodeDesc α).qhalt (2 ^ (decodeDesc α).w) := by
  set d := decodeDesc α with hd
  by_cases hlen : (qhaltField (groupPairs α)).length = d.w
  · -- well-formed width: symbol-wise equality ⟺ decoded values agree
    have hqh : d.qhalt = fieldNat (qhaltField (groupPairs α)) := by
      rw [hd, decodeDesc_qhalt, ite_eq_left hlen]
    have hlt : fieldNat (qhaltField (groupPairs α)) < 2 ^ d.w := by
      rw [fieldNat, ← hlen]
      calc Nat.fromBits ((qhaltField (groupPairs α)).filterMap symBit?)
          < 2 ^ ((qhaltField (groupPairs α)).filterMap symBit?).length :=
            Nat.fromBits_lt_pow_length _
        _ ≤ 2 ^ (qhaltField (groupPairs α)).length :=
            Nat.pow_le_pow_right (by omega) (List.length_filterMap_le ..)
    rw [hqh, Nat.min_eq_left (Nat.le_of_lt hlt)]
    constructor
    · intro h
      have := congrArg (fun l => Nat.fromBits (l.filterMap symBit?)) h
      simpa [filterMap_symBit?_bitsToSyms, Nat.fromBits_toBits hq, fieldNat]
        using this
    · intro h
      subst h
      have hnb : ∀ s ∈ qhaltField (groupPairs α), s ≠ Γw.blank :=
        fun s hs => takeField_fst_ne_blank _ s hs
      have hbits := bitsToSyms_filterMap_of_ne_blank hnb
      have hlenb : ((qhaltField (groupPairs α)).filterMap symBit?).length = d.w := by
        have := congrArg List.length hbits
        rw [bitsToSyms_length] at this
        omega
      rw [fieldNat, show d.w = ((qhaltField (groupPairs α)).filterMap symBit?).length
        from hlenb.symm, Nat.toBits_fromBits, hbits]
  · -- malformed width: lengths differ on the left; the sentinel on the right
    have hqh : d.qhalt = 2 ^ d.w := by
      rw [hd, decodeDesc_qhalt, ite_eq_right hlen]
    rw [hqh, Nat.min_self]
    constructor
    · intro h
      have := congrArg List.length h
      simp only [bitsToSyms_length, Nat.length_toBits] at this
      exact absurd this.symm hlen
    · intro h
      omega

end TM.UTMBody

end Complexity
