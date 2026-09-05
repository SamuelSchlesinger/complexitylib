/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# TM State Normalization and Binary Encoding

This file provides two pieces of general infrastructure for working with
Turing machines:

1. **State normalization**: Convert any `TM n` with finite state type `Q` to
   an equivalent machine using states `Fin (Fintype.card Q)`. This is needed
   whenever states must be represented as binary numbers (e.g., for encoding
   a TM description).

2. **Binary encoding primitives**: Fixed-width encodings for tape symbols,
   write symbols, directions, and natural numbers, with roundtrip correctness
   proofs.

## Main definitions

### State normalization
- `TM.stateEquiv` — canonical equivalence `Q ≃ Fin (Fintype.card Q)`
- `TM.normalize` — normalize state type to `Fin (Fintype.card Q)`
- `TM.normalizeCfg` — embed a config into the normalized state space
- `TM.normalize_decidesInTime` — behavioral equivalence

### Binary encoding
- `Γ.encode` / `Γ.decode` — tape symbol ↔ 2 bits
- `Γw.encode` — write symbol → 2 bits
- `Dir3.encode` — direction → 2 bits
- `Nat.toBits` / `Nat.fromBits` — fixed-width big-endian binary

### Enumeration
- `allΓ` — all 4 tape symbols in canonical order
- `allΓFuncs` — enumerate all `Fin n → Γ` functions
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- State normalization
-- ════════════════════════════════════════════════════════════════════════

/-- The canonical equivalence between a TM's states and `Fin (Fintype.card Q)`. -/
noncomputable def stateEquiv (tm : TM n) : tm.Q ≃ Fin (Fintype.card tm.Q) :=
  @Fintype.equivFin tm.Q tm.finQ

/-- The canonical equivalence cast to `Fin k` given `k = Fintype.card Q`. -/
noncomputable def stateEquivOfCardEq (tm : TM n) (hk : k = @Fintype.card tm.Q tm.finQ) :
    tm.Q ≃ Fin k :=
  hk ▸ tm.stateEquiv

/-- `stateEquivOfCardEq` agrees with `stateEquiv` on values. -/
theorem stateEquivOfCardEq_val (tm : TM n) (hk : k = @Fintype.card tm.Q tm.finQ)
    (q : tm.Q) : (tm.stateEquivOfCardEq hk q).val = (tm.stateEquiv q).val := by
  subst hk; rfl

/-- Normalize a TM's state type to `Fin (Fintype.card Q)` via the canonical
    equivalence. This preserves all computational behavior.
    Noncomputable because `Fintype.equivFin` uses choice. -/
noncomputable def normalize (tm : TM n) : TM n where
  Q := Fin (@Fintype.card tm.Q tm.finQ)
  qstart := tm.stateEquiv tm.qstart
  qhalt := tm.stateEquiv tm.qhalt
  δ := fun q iHead wHeads oHead =>
    let (q', wW, oW, iD, wD, oD) := tm.δ (tm.stateEquiv.symm q) iHead wHeads oHead
    (tm.stateEquiv q', wW, oW, iD, wD, oD)
  δ_right_of_start := fun q iHead wHeads oHead =>
    tm.δ_right_of_start (tm.stateEquiv.symm q) iHead wHeads oHead

/-- Configuration embedding: map a config with original states to normalized states. -/
noncomputable def normalizeCfg (tm : TM n) (c : Cfg n tm.Q) : Cfg n (tm.normalize.Q) where
  state := tm.stateEquiv c.state
  input := c.input
  work := c.work
  output := c.output

/-- Stepping the normalized TM commutes with the state equivalence. -/
theorem normalize_step_comm (tm : TM n) (c : Cfg n tm.Q) :
    tm.normalize.step (tm.normalizeCfg c) =
      (tm.step c).map tm.normalizeCfg := by
  simp only [step, normalize, normalizeCfg]
  by_cases h : c.state = tm.qhalt
  · simp [h, stateEquiv]; rfl
  · have hne : tm.stateEquiv c.state ≠ tm.stateEquiv tm.qhalt := by
      intro heq; exact h (tm.stateEquiv.injective heq)
    simp only [h, hne, ↓reduceIte, Option.map, Equiv.symm_apply_apply, normalizeCfg]
    rfl

/-- Multi-step simulation: normalized TM mirrors original TM. -/
theorem normalize_reachesIn (tm : TM n) {t : ℕ} {c c' : Cfg n tm.Q}
    (h : tm.reachesIn t c c') :
    tm.normalize.reachesIn t (tm.normalizeCfg c) (tm.normalizeCfg c') := by
  induction h with
  | zero => exact .zero
  | step hstep _ ih =>
    exact .step (by rw [normalize_step_comm, hstep]; rfl) ih

/-- Halting is preserved by normalization. -/
theorem normalize_halted (tm : TM n) (c : Cfg n tm.Q) :
    tm.normalize.halted (tm.normalizeCfg c) ↔ tm.halted c := by
  simp only [halted, Cfg.isHalted, normalizeCfg, normalize, stateEquiv]
  constructor
  · intro h; exact tm.stateEquiv.injective h
  · intro h; rw [h]

/-- Output is preserved by normalization. -/
theorem normalize_output (tm : TM n) (c : Cfg n tm.Q) :
    (tm.normalizeCfg c).output = c.output := rfl

/-- The initial config normalizes correctly. -/
theorem normalize_initCfg (tm : TM n) (x : List Bool) :
    tm.normalizeCfg (tm.initCfg x) = tm.normalize.initCfg x := by
  simp [normalizeCfg, initCfg, Cfg.init, normalize]

/-- Normalized TM decides the same language in the same time. -/
theorem normalize_decidesInTime (tm : TM n) {L : Language} {T : ℕ → ℕ}
    (h : tm.DecidesInTime L T) :
    tm.normalize.DecidesInTime L T := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hmem, hnmem⟩ := h x
  refine ⟨tm.normalizeCfg c', t, ht, ?_, ?_, ?_, ?_⟩
  · rw [← normalize_initCfg]; exact normalize_reachesIn tm hreach
  · rwa [normalize_halted]
  · intro hx; rw [normalize_output]; exact hmem hx
  · intro hx; rw [normalize_output]; exact hnmem hx

end TM

-- ════════════════════════════════════════════════════════════════════════
-- Binary encoding primitives
-- ════════════════════════════════════════════════════════════════════════

/-- Encode a tape symbol as 2 bits: 0→00, 1→01, □→10, ▷→11. -/
def Γ.encode : Γ → List Bool
  | .zero  => [false, false]
  | .one   => [false, true]
  | .blank => [true, false]
  | .start => [true, true]

/-- Decode 2 bits back to a tape symbol. -/
def Γ.decode : List Bool → Option Γ
  | [false, false] => some .zero
  | [false, true]  => some .one
  | [true, false]  => some .blank
  | [true, true]   => some .start
  | _              => none

/-- Encode a write symbol as 2 bits: 0→00, 1→01, □→10. -/
def Γw.encode : Γw → List Bool
  | .zero  => [false, false]
  | .one   => [false, true]
  | .blank => [true, false]

/-- Encode a direction as 2 bits: L→00, R→01, S→10. -/
def Dir3.encode : Dir3 → List Bool
  | .left  => [false, false]
  | .right => [false, true]
  | .stay  => [true, false]

theorem Γ.length_encode (g : Γ) : g.encode.length = 2 := by cases g <;> rfl
theorem Γw.length_encode (g : Γw) : g.encode.length = 2 := by cases g <;> rfl
theorem Dir3.length_encode (d : Dir3) : d.encode.length = 2 := by cases d <;> rfl

/-- Roundtrip: decode ∘ encode = some. -/
theorem Γ.decode_encode (g : Γ) : Γ.decode (Γ.encode g) = some g := by
  cases g <;> rfl

/-- Γ encoding is injective. -/
theorem Γ.encode_injective : Function.Injective Γ.encode := by
  intro a b h; cases a <;> cases b <;> simp_all [Γ.encode]

/-- Decode 2 bits back to a write symbol; reject the unused `[true, true]`
    pattern and every non-two-bit input. -/
def Γw.decode : List Bool → Option Γw
  | [false, false] => some .zero
  | [false, true]  => some .one
  | [true, false]  => some .blank
  | _              => none

/-- Decode 2 bits back to a direction; reject the unused `[true, true]` pattern
    and every non-two-bit input. -/
def Dir3.decode : List Bool → Option Dir3
  | [false, false] => some .left
  | [false, true]  => some .right
  | [true, false]  => some .stay
  | _              => none

/-- Roundtrip for write symbols: `decode ∘ encode = some`. -/
theorem Γw.decode_encode (g : Γw) : Γw.decode (Γw.encode g) = some g := by
  cases g <;> rfl

/-- Roundtrip for directions: `decode ∘ encode = some`. -/
theorem Dir3.decode_encode (d : Dir3) : Dir3.decode (Dir3.encode d) = some d := by
  cases d <;> rfl

/-- Γw encoding is injective. -/
theorem Γw.encode_injective : Function.Injective Γw.encode := by
  intro a b h; cases a <;> cases b <;> simp_all [Γw.encode]

/-- Dir3 encoding is injective. -/
theorem Dir3.encode_injective : Function.Injective Dir3.encode := by
  intro a b h; cases a <;> cases b <;> simp_all [Dir3.encode]

/-- The unused two-bit pattern is rejected as malformed (write symbols). -/
theorem Γw.decode_true_true : Γw.decode [true, true] = none := rfl

/-- The unused two-bit pattern is rejected as malformed (directions). -/
theorem Dir3.decode_true_true : Dir3.decode [true, true] = none := rfl

/-- All 4 tape symbols in canonical order. -/
def allΓ : List Γ := [.zero, .one, .blank, .start]

/-- Every tape symbol appears in `allΓ`. -/
theorem mem_allΓ (g : Γ) : g ∈ allΓ := by
  cases g <;> simp [allΓ]

/-- `allΓ` contains no duplicates. -/
theorem nodup_allΓ : allΓ.Nodup := by
  simp [allΓ, List.Nodup]

/-- `allΓ` has exactly 4 elements (one per `Γ` constructor). -/
theorem length_allΓ : allΓ.length = 4 := rfl

/-- Enumerate all functions `Fin n → Γ` in canonical (lexicographic) order. -/
def allΓFuncs : (n : ℕ) → List (Fin n → Γ)
  | 0 => [Fin.elim0]
  | n + 1 => (allΓFuncs n).flatMap fun f =>
      allΓ.map fun g =>
        fun i : Fin (n + 1) =>
          if h : i.val < n then f ⟨i.val, h⟩ else g

/-- Every function `Fin n → Γ` appears in `allΓFuncs n`. -/
theorem mem_allΓFuncs : ∀ (n : ℕ) (f : Fin n → Γ), f ∈ allΓFuncs n
  | 0, f => by
    simp only [allΓFuncs, List.mem_singleton]
    funext i; exact i.elim0
  | n + 1, f => by
    simp only [allΓFuncs, List.mem_flatMap, List.mem_map]
    refine ⟨fun i => f ⟨i.val, by omega⟩, mem_allΓFuncs n _,
            f ⟨n, Nat.lt_succ_self _⟩, mem_allΓ _, ?_⟩
    funext i
    by_cases hi : i.val < n
    · simp [hi]
    · have : i.val = n := by omega
      simp [hi]; congr 1; exact Fin.ext this.symm

end Complexity
