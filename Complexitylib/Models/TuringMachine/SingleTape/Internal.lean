/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine

/-!
# Single-tape simulation — encoding internals

Foundations for `NTM.singleTapeSim` (see `docs/A4-SingleTapeSimulation.md`):
the binary symbol codec and the block-index arithmetic for laying `k` work
tapes onto one. These are **path-independent**: any single-work-tape encoding
over the fixed alphabet `Γ = {0,1,□,▷}` needs a binary code (so that literal
`□` can serve as the end-of-used-region sentinel) and a per-position block
layout. Proof internals only — correctness of the full simulation is
established downstream.
-/


@[expose] public section

namespace Complexity

namespace NTM.SingleTape

/-! ## Binary symbol codec

A writable symbol `Γw = {0,1,□}` is stored in two cells over `{0,1}` (never
`□`), so that a literal `□` inside the used region is impossible and can mark
its end. Code: `□ ↦ 00`, `0 ↦ 01`, `1 ↦ 10`. -/

/-- Encode a writable symbol as a 2-cell binary code. -/
def encSym : Γw → Γ × Γ
  | .blank => (Γ.zero, Γ.zero)
  | .zero  => (Γ.zero, Γ.one)
  | .one   => (Γ.one, Γ.zero)

/-- Encode a writable symbol into a 2-cell **writable** code (for SCATTER's
    symbol writes; agrees with `encSym` under `Γw.toΓ`, see `encSymW_toΓ`). -/
def encSymW : Γw → Γw × Γw
  | .blank => (.zero, .zero)
  | .zero  => (.zero, .one)
  | .one   => (.one, .zero)

/-- Decode a 2-cell code back to a writable symbol (any non-code pair ↦ `□`). -/
def decSym : Γ → Γ → Γw
  | Γ.zero, Γ.one => .zero
  | Γ.one,  Γ.zero => .one
  | _,      _      => .blank

/-- The writable codec agrees with the `Γ`-valued one under `Γw.toΓ`. -/
theorem encSymW_toΓ (s : Γw) :
    ((encSymW s).1.toΓ, (encSymW s).2.toΓ) = encSym s := by
  cases s <;> rfl

/-- The codec round-trips. -/
@[simp] theorem decSym_encSym (s : Γw) :
    decSym (encSym s).1 (encSym s).2 = s := by
  cases s <;> rfl

/-- No active code cell is `□`: encoded symbols use only `{0,1}`. This is what
    lets a literal `□` mark the end of the used region. -/
theorem encSym_ne_blank (s : Γw) :
    (encSym s).1 ≠ Γ.blank ∧ (encSym s).2 ≠ Γ.blank := by
  cases s <;> exact ⟨by decide, by decide⟩

/-- An encoded code cell is never `▷` either, so the global `▷` at cell 0 stays
    unique within the work tape. -/
theorem encSym_ne_start (s : Γw) :
    (encSym s).1 ≠ Γ.start ∧ (encSym s).2 ≠ Γ.start := by
  cases s <;> exact ⟨by decide, by decide⟩

/-- Codec on the full read alphabet `Γ`, used by the invariant (which ranges
    over work-tape cells of type `Γ`). `▷ ↦ 00` is junk: `▷` never occurs at a
    work-tape position `≥ 1`, so the round-trip below excludes it. -/
def encSymΓ : Γ → Γ × Γ
  | .blank => (Γ.zero, Γ.zero)
  | .zero  => (Γ.zero, Γ.one)
  | .one   => (Γ.one, Γ.zero)
  | .start => (Γ.zero, Γ.zero)

/-- Decode a 2-cell code over `Γ` (any non-code pair ↦ `□`). -/
def decSymΓ : Γ → Γ → Γ
  | Γ.zero, Γ.one => Γ.zero
  | Γ.one,  Γ.zero => Γ.one
  | _,      _      => Γ.blank

/-- The full-alphabet codec round-trips on every non-`▷` symbol. -/
theorem decSymΓ_encSymΓ {s : Γ} (hs : s ≠ Γ.start) :
    decSymΓ (encSymΓ s).1 (encSymΓ s).2 = s := by
  cases s <;> first | rfl | exact absurd rfl hs

/-- Bridge: encoding a writable symbol agrees with the full-alphabet codec on
    its image. Lets `δ'` write via `encSym` while the invariant reads `encSymΓ`. -/
theorem encSymΓ_toΓ (s : Γw) : encSymΓ (Γw.toΓ s) = encSym s := by
  cases s <;> rfl

/-- Both code cells are writable (`≠ ▷`), so encoding never introduces a second
    `▷` (holds even for the junk `▷ ↦ 00` case). -/
theorem encSymΓ_ne_start (s : Γ) :
    (encSymΓ s).1 ≠ Γ.start ∧ (encSymΓ s).2 ≠ Γ.start := by
  cases s <;> exact ⟨by decide, by decide⟩

/-- Neither code cell is `□`: codes use only `{0,1}`, so a literal `□` can mark
    the end of the used region. -/
theorem encSymΓ_ne_blank (s : Γ) :
    (encSymΓ s).1 ≠ Γ.blank ∧ (encSymΓ s).2 ≠ Γ.blank := by
  cases s <;> exact ⟨by decide, by decide⟩

/-! ## Block layout

Position-major: super-position `p ≥ 1` occupies a block of `blockWidth k = 3*k`
cells starting at `blockStart k p = 1 + (p-1)*3k`. Within a block, tape `j`
uses offsets `3j, 3j+1` (symbol code) and `3j+2` (head-present bit). Cell 0 is
the global `▷`. -/

/-- Cells per super-position block: 2 symbol cells + 1 head bit, per tape. -/
def blockWidth (k : ℕ) : ℕ := 3 * k

/-- First cell of the block for super-position `p ≥ 1`. -/
def blockStart (k p : ℕ) : ℕ := 1 + (p - 1) * blockWidth k

/-- The first super-position's block starts at cell 1, directly after the `▷`. -/
@[simp] theorem blockStart_one (k : ℕ) : blockStart k 1 = 1 := by
  simp [blockStart]

/-- Consecutive blocks are exactly `blockWidth k` apart. -/
theorem blockStart_succ (k p : ℕ) (hp : 1 ≤ p) :
    blockStart k (p + 1) = blockStart k p + blockWidth k := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  show 1 + ((1 + q + 1) - 1) * blockWidth k
      = 1 + ((1 + q) - 1) * blockWidth k + blockWidth k
  have e1 : (1 + q + 1) - 1 = q + 1 := by omega
  have e2 : (1 + q) - 1 = q := by omega
  rw [e1, e2, Nat.add_mul, one_mul]
  omega

/-- Blocks start at or after cell 1 (never the `▷` cell 0). -/
theorem one_le_blockStart (k p : ℕ) : 1 ≤ blockStart k p := by
  simp only [blockStart]; omega

/-- For positive width, block starts are strictly increasing in the position. -/
theorem blockStart_lt_blockStart {k : ℕ} (hk : 1 ≤ k) {p q : ℕ}
    (hp : 1 ≤ p) (hpq : p < q) : blockStart k p < blockStart k q := by
  simp only [blockStart]
  have hbw : 1 ≤ blockWidth k := by simp only [blockWidth]; omega
  have hlt : (p - 1) + 1 ≤ q - 1 := by omega
  have hmono : ((p - 1) + 1) * blockWidth k ≤ (q - 1) * blockWidth k :=
    Nat.mul_le_mul hlt (le_refl _)
  rw [Nat.add_mul, one_mul] at hmono
  omega

/-- The cell holding tape `j`'s head-present bit within block `p` (offset 0 of
    the triple: **head-bit-first**, so a sweep learns "head here" before passing
    the symbol cells). -/
def headBitCell (k p : ℕ) (j : Fin k) : ℕ := blockStart k p + 3 * j.val

/-- The first (high) symbol cell of tape `j` within block `p` (offset 1; the low
    symbol cell is `symCell + 1` at offset 2). -/
def symCell (k p : ℕ) (j : Fin k) : ℕ := blockStart k p + 3 * j.val + 1

/-- Within a block, tape `j`'s three cells stay inside `[blockStart, blockStart+3k)`. -/
theorem headBitCell_lt_blockStart_succ (k p : ℕ) (j : Fin k) (hp : 1 ≤ p) :
    headBitCell k p j < blockStart k (p + 1) := by
  rw [blockStart_succ k p hp]
  have hj : j.val < k := j.isLt
  simp only [headBitCell, blockWidth]
  omega

/-- Block starts are monotone (non-strict) in the position. -/
theorem blockStart_le (k : ℕ) {p q : ℕ} (hpq : p ≤ q) :
    blockStart k p ≤ blockStart k q := by
  simp only [blockStart]
  exact Nat.add_le_add_left (Nat.mul_le_mul (by omega) (le_refl _)) 1

/-- Tape `j`'s whole triple fits strictly before the next block:
    `headBitCell + 3 ≤ blockStart (p+1)` (the `+2` cell is the last of the triple). -/
theorem headBitCell_add_three_le_blockStart_succ (k p : ℕ) (j : Fin k) (hp : 1 ≤ p) :
    headBitCell k p j + 3 ≤ blockStart k (p + 1) := by
  rw [blockStart_succ k p hp]
  have hj : j.val < k := j.isLt
  simp only [headBitCell, blockWidth]
  omega

/-! ## The simulation invariant

`SimInvAt k t w M` asserts that the single work tape `t` encodes the `k`
work tapes `w`, with the used region materialized up to super-position `M`
(the maximum position any head has reached). This is the relation preserved by
one simulated macro-step; the two behavioural lemmas of `singleTapeSim` follow
from base case + preservation + iteration. See `docs/A4-SingleTapeSimulation.md`. -/

/-- The single tape `t` encodes the `k` work tapes `w`, materialized up to `M`. -/
structure SimInvAt (k : ℕ) (t : Tape) (w : Fin k → Tape) (M : ℕ) : Prop where
  /-- Cell 0 is the global start marker `▷`. -/
  cell0 : t.cells 0 = Γ.start
  /-- Each encoded work tape has `▷` at its own cell 0. -/
  wfStart : ∀ j : Fin k, (w j).cells 0 = Γ.start
  /-- No encoded work tape has `▷` at a position `≥ 1` (writes use `Γw`). -/
  noStart : ∀ (j : Fin k) (p : ℕ), 1 ≤ p → (w j).cells p ≠ Γ.start
  /-- Every head is within the materialized region. -/
  heads_le : ∀ j : Fin k, (w j).head ≤ M
  /-- Head-present bit at `(p, j)` is set iff tape `j`'s head is at position `p`. -/
  headBit : ∀ (p : ℕ), 1 ≤ p → p ≤ M → ∀ j : Fin k,
    t.cells (headBitCell k p j) = (if (w j).head = p then Γ.one else Γ.zero)
  /-- The two symbol cells at `(p, j)` hold the code of tape `j`'s symbol at `p`. -/
  sym : ∀ (p : ℕ), 1 ≤ p → p ≤ M → ∀ j : Fin k,
    t.cells (symCell k p j) = (encSymΓ ((w j).cells p)).1 ∧
    t.cells (symCell k p j + 1) = (encSymΓ ((w j).cells p)).2
  /-- Everything from block `M+1` onward is blank — the `□` sentinel region. -/
  sentinel : ∀ c : ℕ, blockStart k (M + 1) ≤ c → t.cells c = Γ.blank

/-- **Base case.** The initial single tape `Tape.init []` encodes the initial
    `k`-tape configuration (all heads at 0, all blank), materialized to `M = 0`
    (empty used region — the sentinel `□` starts right at cell 1). -/
theorem simInvAt_init (k : ℕ) :
    SimInvAt k (Tape.init []) (fun _ => Tape.init []) 0 where
  cell0 := by simp [Tape.init]
  wfStart := fun _ => by simp [Tape.init]
  noStart := fun _ p hp => by
    simp only [Tape.init]
    rw [ite_eq_right (by omega : ¬ p = 0)]
    simp
  heads_le := fun _ => by simp [Tape.init]
  headBit := fun p hp1 hp0 _ => by omega
  sym := fun p hp1 hp0 _ => by omega
  sentinel := fun c hc => by
    rw [blockStart_one] at hc
    simp only [Tape.init]
    rw [ite_eq_right (by omega : ¬ c = 0)]
    simp

/-- `SimInvAt` depends on the encoding tape only through its cells (never its
    head), so it transfers along any cell-preserving change (e.g. a head move). -/
theorem SimInvAt.cells_congr {k : ℕ} {t t' : Tape} {w : Fin k → Tape} {M : ℕ}
    (h : SimInvAt k t w M) (hc : t'.cells = t.cells) : SimInvAt k t' w M where
  cell0 := by rw [hc]; exact h.cell0
  wfStart := h.wfStart
  noStart := h.noStart
  heads_le := h.heads_le
  headBit := fun p hp1 hpM j => by rw [hc]; exact h.headBit p hp1 hpM j
  sym := fun p hp1 hpM j => by rw [hc]; exact h.sym p hp1 hpM j
  sentinel := fun c hc' => by rw [hc]; exact h.sentinel c hc'

/-- **GATHER decode kernel (head off cell 0).** When tape `j`'s head is in the
    materialized region, decoding its two symbol cells recovers exactly the
    symbol under that head — what the sweep accumulates. -/
theorem SimInvAt.decSymΓ_symCell_head {k : ℕ} {t : Tape} {w : Fin k → Tape} {M : ℕ}
    (h : SimInvAt k t w M) (j : Fin k)
    (hp1 : 1 ≤ (w j).head) (hpM : (w j).head ≤ M) :
    decSymΓ (t.cells (symCell k ((w j).head) j))
            (t.cells (symCell k ((w j).head) j + 1)) = (w j).read := by
  obtain ⟨c1, c2⟩ := h.sym ((w j).head) hp1 hpM j
  rw [c1, c2, decSymΓ_encSymΓ (h.noStart j ((w j).head) hp1)]
  rfl

/-- **GATHER decode kernel (head on cell 0).** A head at position 0 reads `▷`;
    the sweep finds no marker for it and records `▷`. -/
theorem SimInvAt.read_eq_start_of_head_eq_zero {k : ℕ} {t : Tape} {w : Fin k → Tape} {M : ℕ}
    (h : SimInvAt k t w M) (j : Fin k) (h0 : (w j).head = 0) :
    (w j).read = Γ.start := by
  rw [Tape.read, h0]; exact h.wfStart j

/-- **No `□` inside the materialized region.** Every cell strictly between the
    `▷` (cell 0) and the sentinel block is a code or head-bit cell, hence in
    `{0,1}` — so the first `□` a rightward sweep meets is exactly the sentinel
    at `blockStart k (M+1)`. (Holds vacuously for `k = 0`.) -/
theorem SimInvAt.materialized_ne_blank {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {M : ℕ} (h : SimInvAt k t w M) {c : ℕ}
    (hc1 : 1 ≤ c) (hc2 : c < blockStart k (M + 1)) : t.cells c ≠ Γ.blank := by
  have hbs : blockStart k (M + 1) = 1 + M * blockWidth k := by
    simp only [blockStart, Nat.add_sub_cancel]
  rw [hbs] at hc2
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp only [blockWidth] at hc2; omega
  have hW : 0 < blockWidth k := by simp only [blockWidth]; omega
  -- decompose c - 1 = blockWidth k * q + ib, with block index q+1 ∈ [1, M]
  have hr : c - 1 < blockWidth k * M := by rw [Nat.mul_comm]; omega
  -- introduce the block index `q+1` and in-block offset `ib` as opaque naturals
  -- (forgetting the non-literal division so `omega` can reason about them)
  obtain ⟨q, ib, hqM, hibW, hdm⟩ :
      ∃ q ib, q < M ∧ ib < blockWidth k ∧ blockWidth k * q + ib = c - 1 :=
    ⟨(c - 1) / blockWidth k, (c - 1) % blockWidth k,
      Nat.div_lt_of_lt_mul hr, Nat.mod_lt _ hW, Nat.div_add_mod _ _⟩
  have hp1 : 1 ≤ q + 1 := by omega
  have hpM : q + 1 ≤ M := by omega
  have hbq : blockStart k (q + 1) = 1 + q * blockWidth k := by
    show 1 + (q + 1 - 1) * blockWidth k = 1 + q * blockWidth k
    rw [Nat.add_sub_cancel]
  have hdm' : q * blockWidth k + ib = c - 1 := by rw [Nat.mul_comm] at hdm; exact hdm
  have hceq : c = blockStart k (q + 1) + ib := by rw [hbq]; omega
  -- decompose ib = 3*j + off within the block, j ∈ [0, k), off ∈ [0,3)
  have hib3 : ib < 3 * k := by have h' := hibW; simp only [blockWidth] at h'; exact h'
  have hjk : ib / 3 < k := Nat.div_lt_of_lt_mul hib3
  have hibdm : 3 * (ib / 3) + ib % 3 = ib := Nat.div_add_mod _ _
  have hc_full : c = blockStart k (q + 1) + (3 * (ib / 3) + ib % 3) := by rw [hceq, hibdm]
  have hcases : ib % 3 = 0 ∨ ib % 3 = 1 ∨ ib % 3 = 2 := by omega
  rcases hcases with h3 | h3 | h3 <;> rw [h3] at hc_full
  · -- offset 0 : head-bit cell
    have hcs : c = headBitCell k (q + 1) ⟨ib / 3, hjk⟩ := by simp only [headBitCell]; omega
    rw [hcs, h.headBit (q + 1) hp1 hpM ⟨ib / 3, hjk⟩]; split <;> decide
  · -- offset 1 : high symbol cell
    have hcs : c = symCell k (q + 1) ⟨ib / 3, hjk⟩ := by simp only [symCell]; omega
    rw [hcs, (h.sym (q + 1) hp1 hpM ⟨ib / 3, hjk⟩).1]; exact (encSymΓ_ne_blank _).1
  · -- offset 2 : low symbol cell
    have hcs : c = symCell k (q + 1) ⟨ib / 3, hjk⟩ + 1 := by simp only [symCell]; omega
    rw [hcs, (h.sym (q + 1) hp1 hpM ⟨ib / 3, hjk⟩).2]; exact (encSymΓ_ne_blank _).2

/-- **No `▷` inside the materialized region.** Every cell strictly between the
    `▷` (cell 0) and the sentinel block is a code or head-bit cell (in `{0,1}`),
    hence never `▷` — so `▷` uniquely marks cell `0`. The REWIND sweep's precondition. -/
theorem SimInvAt.materialized_ne_start {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {M : ℕ} (h : SimInvAt k t w M) {c : ℕ}
    (hc1 : 1 ≤ c) (hc2 : c < blockStart k (M + 1)) : t.cells c ≠ Γ.start := by
  have hbs : blockStart k (M + 1) = 1 + M * blockWidth k := by
    simp only [blockStart, Nat.add_sub_cancel]
  rw [hbs] at hc2
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp only [blockWidth] at hc2; omega
  have hW : 0 < blockWidth k := by simp only [blockWidth]; omega
  have hr : c - 1 < blockWidth k * M := by rw [Nat.mul_comm]; omega
  obtain ⟨q, ib, hqM, hibW, hdm⟩ :
      ∃ q ib, q < M ∧ ib < blockWidth k ∧ blockWidth k * q + ib = c - 1 :=
    ⟨(c - 1) / blockWidth k, (c - 1) % blockWidth k,
      Nat.div_lt_of_lt_mul hr, Nat.mod_lt _ hW, Nat.div_add_mod _ _⟩
  have hp1 : 1 ≤ q + 1 := by omega
  have hpM : q + 1 ≤ M := by omega
  have hbq : blockStart k (q + 1) = 1 + q * blockWidth k := by
    show 1 + (q + 1 - 1) * blockWidth k = 1 + q * blockWidth k
    rw [Nat.add_sub_cancel]
  have hdm' : q * blockWidth k + ib = c - 1 := by rw [Nat.mul_comm] at hdm; exact hdm
  have hceq : c = blockStart k (q + 1) + ib := by rw [hbq]; omega
  have hib3 : ib < 3 * k := by have h' := hibW; simp only [blockWidth] at h'; exact h'
  have hjk : ib / 3 < k := Nat.div_lt_of_lt_mul hib3
  have hibdm : 3 * (ib / 3) + ib % 3 = ib := Nat.div_add_mod _ _
  have hc_full : c = blockStart k (q + 1) + (3 * (ib / 3) + ib % 3) := by rw [hceq, hibdm]
  have hcases : ib % 3 = 0 ∨ ib % 3 = 1 ∨ ib % 3 = 2 := by omega
  rcases hcases with h3 | h3 | h3 <;> rw [h3] at hc_full
  · have hcs : c = headBitCell k (q + 1) ⟨ib / 3, hjk⟩ := by simp only [headBitCell]; omega
    rw [hcs, h.headBit (q + 1) hp1 hpM ⟨ib / 3, hjk⟩]; split <;> decide
  · have hcs : c = symCell k (q + 1) ⟨ib / 3, hjk⟩ := by simp only [symCell]; omega
    rw [hcs, (h.sym (q + 1) hp1 hpM ⟨ib / 3, hjk⟩).1]; exact (encSymΓ_ne_start _).1
  · have hcs : c = symCell k (q + 1) ⟨ib / 3, hjk⟩ + 1 := by simp only [symCell]; omega
    rw [hcs, (h.sym (q + 1) hp1 hpM ⟨ib / 3, hjk⟩).2]; exact (encSymΓ_ne_start _).2

end NTM.SingleTape

end Complexity
