/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.Desc

/-!
# Interpreting machine descriptions

`TMDesc.toTM` turns a description into an actual single-work-tape machine:
states are `Fin (2^w + 1)` (the extra state `2^w` represents a malformed
out-of-range halt field), transitions look up the table, and head directions
are sanitized to satisfy the `▷ ⇒ move right` discipline. Transition targets
are clamped at `2^w`; in particular, a missing table entry takes the default
action to the represented halt state, including the malformed sentinel.

`descOfTM` extracts a well-formed description from any single-work-tape
machine: states are numbered by the canonical `Fintype` equivalence and the
table lists every `(state, symbols)` combination densely.

## Main results

- `TMDesc.toTM` — interpreter; the *specification* of the universal machine
- `descOfTM` / `descOfTM_wf` — every `TM 1` has a well-formed description
- `descOfTM_step_comm` — step-exact correspondence between `M` and
  `(descOfTM M).toTM`
- `descOfTM_decidesInTime` — language and running time carry over exactly
-/


@[expose] public section

namespace Complexity

namespace TMDesc

/-- Interpret a description as a single-work-tape machine. States are
    `Fin (2^w + 1)`; state `2^w` represents an out-of-range `qhalt`. Transition
    targets are clamped at that state, so the default action still reaches the
    represented halt state. Directions are sanitized to satisfy the
    `▷ ⇒ right` discipline. -/
def toTM (d : TMDesc) : TM 1 where
  Q := Fin (2 ^ d.w + 1)
  qstart := ⟨d.qstart % 2 ^ d.w, Nat.lt_succ_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))⟩
  qhalt := ⟨min d.qhalt (2 ^ d.w), Nat.lt_succ_of_le (Nat.min_le_right ..)⟩
  δ := fun q si sw so =>
    let a := d.lookup q.val si (sw 0) so
    -- targets are clamped (not reduced mod 2^w) so that the default
    -- action's target `d.qhalt` lands exactly on `qhalt` even when the
    -- decoded halt state is the out-of-range sentinel `2^w`
    (⟨min a.q' (2 ^ d.w), Nat.lt_succ_of_le (Nat.min_le_right ..)⟩,
     fun _ => a.ww,
     a.wo,
     if si = Γ.start then .right else a.di,
     fun i => if sw i = Γ.start then .right else a.dw,
     if so = Γ.start then .right else a.dOut)
  δ_right_of_start := fun q si sw so =>
    ⟨fun h => by simp [h], fun i h => by simp [h], fun h => by simp [h]⟩

end TMDesc

-- ════════════════════════════════════════════════════════════════════════
-- Extraction: every TM 1 has a description
-- ════════════════════════════════════════════════════════════════════════

namespace TM

variable (M : TM 1)

/-- The table action of `M` (with states numbered by `stateEquiv`) on the
    key `(q, si, sw, so)`. -/
noncomputable def descAct (q : Fin (Fintype.card M.Q)) (si sw so : Γ) : DescAct :=
  let r := M.δ (M.stateEquiv.symm q) si (fun _ => sw) so
  { q' := (M.stateEquiv r.1).val
    ww := r.2.1 0
    wo := r.2.2.1
    di := r.2.2.2.1
    dw := r.2.2.2.2.1 0
    dOut := r.2.2.2.2.2 }

/-- The dense table row for key `(q, si, sw, so)`. -/
noncomputable def descEntry (q : Fin (Fintype.card M.Q)) (si sw so : Γ) : DescEntry :=
  { q := q.val, si := si, sw := sw, so := so, act := M.descAct q si sw so }

/-- Extract a description from a single-work-tape machine: states are
    numbered by the canonical equivalence, the state field width is the
    state count itself (`k < 2^k`), and the table densely lists every
    `(state, symbols)` combination. -/
noncomputable def descOfTM : TMDesc :=
  let k := Fintype.card M.Q
  { w := k
    qstart := (M.stateEquiv M.qstart).val
    qhalt := (M.stateEquiv M.qhalt).val
    entries :=
      (List.finRange k).flatMap fun q =>
        allΓ.flatMap fun si =>
          allΓ.flatMap fun sw =>
            allΓ.map fun so => M.descEntry q si sw so }

theorem descOfTM_wf : (M.descOfTM).WF := by
  constructor
  · exact lt_of_lt_of_le (M.stateEquiv M.qstart).isLt (Nat.le_of_lt Nat.lt_two_pow_self)
  · exact lt_of_lt_of_le (M.stateEquiv M.qhalt).isLt (Nat.le_of_lt Nat.lt_two_pow_self)
  · intro e he
    simp only [descOfTM, List.mem_flatMap, List.mem_map] at he
    obtain ⟨q, -, si, -, sw, -, so, -, rfl⟩ := he
    exact lt_of_lt_of_le q.isLt (Nat.le_of_lt Nat.lt_two_pow_self)
  · intro e he
    simp only [descOfTM, List.mem_flatMap, List.mem_map] at he
    obtain ⟨q, -, si, -, sw, -, so, -, rfl⟩ := he
    exact lt_of_lt_of_le (M.stateEquiv _).isLt (Nat.le_of_lt Nat.lt_two_pow_self)

-- ── Table lookup computes the extracted action ──────────────────────────

private theorem find?_eq_some_of_unique {α : Type _} {p : α → Bool} {a : α} :
    ∀ {l : List α}, a ∈ l → p a = true → (∀ b ∈ l, p b = true → b = a) →
      l.find? p = some a
  | b :: l, ha, hpa, huniq => by
    by_cases hpb : p b = true
    · rw [List.find?_cons_of_pos hpb, huniq b (List.mem_cons_self ..) hpb]
    · rw [List.find?_cons_of_neg hpb]
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact absurd hpa hpb
      · exact find?_eq_some_of_unique ha' hpa
          fun c hc hpc => huniq c (List.mem_cons_of_mem _ hc) hpc

/-- Every entry of the extracted table is a `descEntry`, determined by its
    key. -/
private theorem descOfTM_mem_entries {e : DescEntry}
    (he : e ∈ (M.descOfTM).entries) :
    ∃ (q : Fin (Fintype.card M.Q)) (si sw so : Γ), e = M.descEntry q si sw so := by
  simp only [descOfTM, List.mem_flatMap, List.mem_map] at he
  obtain ⟨q, -, si, -, sw, -, so, -, rfl⟩ := he
  exact ⟨q, si, sw, so, rfl⟩

/-- Looking up an in-range key in the extracted table returns the extracted
    action. -/
theorem descOfTM_lookup (q : Fin (Fintype.card M.Q)) (si sw so : Γ) :
    (M.descOfTM).lookup q.val si sw so = M.descAct q si sw so := by
  have hmem : M.descEntry q si sw so ∈ (M.descOfTM).entries := by
    simp only [descOfTM, List.mem_flatMap, List.mem_map]
    exact ⟨q, List.mem_finRange q, si, mem_allΓ si, sw, mem_allΓ sw,
      ⟨so, mem_allΓ so, rfl⟩⟩
  have hkey : (fun e : DescEntry =>
      e.q == q.val && e.si == si && e.sw == sw && e.so == so)
        (M.descEntry q si sw so) = true := by
    simp [descEntry]
  have huniq : ∀ e ∈ (M.descOfTM).entries,
      (fun e : DescEntry => e.q == q.val && e.si == si && e.sw == sw && e.so == so) e
        = true → e = M.descEntry q si sw so := by
    intro e he hp
    obtain ⟨q', si', sw', so', rfl⟩ := M.descOfTM_mem_entries he
    simp only [descEntry, Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨hq, hsi⟩, hsw⟩, hso⟩ := hp
    have : q' = q := Fin.val_injective hq
    subst this hsi hsw hso
    rfl
  rw [TMDesc.lookup, find?_eq_some_of_unique hmem hkey huniq]
  rfl

-- ── Step-exact correspondence ────────────────────────────────────────────

/-- Configuration embedding into the interpreted description's state space:
    states are renumbered by `stateEquiv` (values below `card Q < 2^card Q`),
    tapes are unchanged. -/
noncomputable def descCfg (c : Cfg 1 M.Q) : Cfg 1 (M.descOfTM.toTM.Q) where
  state := ⟨(M.stateEquiv c.state).val,
    Nat.lt_succ_of_lt (lt_of_lt_of_le (M.stateEquiv c.state).isLt
      (Nat.le_of_lt Nat.lt_two_pow_self))⟩
  input := c.input
  work := c.work
  output := c.output

/-- Halting is preserved by the embedding. -/
theorem descOfTM_halted (c : Cfg 1 M.Q) :
    M.descOfTM.toTM.halted (M.descCfg c) ↔ M.halted c := by
  have hlt : (M.stateEquiv M.qhalt).val ≤ 2 ^ Fintype.card M.Q :=
    Nat.le_of_lt (lt_of_lt_of_le (M.stateEquiv M.qhalt).isLt
      (Nat.le_of_lt Nat.lt_two_pow_self))
  simp only [halted, Cfg.isHalted, descCfg, TMDesc.toTM, descOfTM,
    Nat.min_eq_left hlt]
  constructor
  · intro h; exact M.stateEquiv.injective (Fin.val_injective (Fin.mk.injEq .. ▸ h))
  · intro h; simp [h]

/-- The initial configuration embeds correctly. -/
theorem descOfTM_initCfg (x : List Bool) :
    M.descCfg (M.initCfg x) = M.descOfTM.toTM.initCfg x := by
  have hlt : (M.stateEquiv M.qstart).val < 2 ^ Fintype.card M.Q :=
    lt_of_lt_of_le (M.stateEquiv M.qstart).isLt (Nat.le_of_lt Nat.lt_two_pow_self)
  simp only [initCfg, Cfg.init, descCfg, TMDesc.toTM, descOfTM,
    Nat.mod_eq_of_lt hlt]

/-- Stepping the interpreted description commutes with the configuration
    embedding. -/
theorem descOfTM_step_comm (c : Cfg 1 M.Q) :
    M.descOfTM.toTM.step (M.descCfg c) = (M.step c).map M.descCfg := by
  by_cases h : c.state = M.qhalt
  · have hh : (M.descCfg c).state = M.descOfTM.toTM.qhalt := (M.descOfTM_halted c).mpr h
    simp [step, h, hh]
  · have hne : (M.descCfg c).state ≠ M.descOfTM.toTM.qhalt :=
      fun hh => h ((M.descOfTM_halted c).mp hh)
    simp only [step, ite_eq_right h, ite_eq_right hne, Option.map_some]
    have hro := M.δ_right_of_start c.state c.input.read
      (fun i => (c.work i).read) c.output.read
    have hwork : (fun _ : Fin 1 => (c.work 0).read) = (fun i => (c.work i).read) :=
      funext fun i => by rw [Subsingleton.elim i 0]
    simp only [descCfg, TMDesc.toTM, M.descOfTM_lookup, descAct,
      Equiv.symm_apply_apply, hwork]
    have hwidth : M.descOfTM.w = Fintype.card M.Q := rfl
    simp only [Option.some.injEq, Cfg.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Fin.mk.injEq]
      exact Nat.min_eq_left (by
        rw [hwidth]
        exact Nat.le_of_lt (lt_of_lt_of_le (M.stateEquiv _).isLt
          (Nat.le_of_lt Nat.lt_two_pow_self)))
    · by_cases hi : c.input.read = Γ.start
      · rw [ite_eq_left hi, hro.1 hi]
      · rw [ite_eq_right hi]
    · funext i
      obtain rfl : i = 0 := Subsingleton.elim i 0
      by_cases hw : (c.work 0).read = Γ.start
      · rw [ite_eq_left hw, hro.2.1 0 hw]
      · rw [ite_eq_right hw]
    · by_cases ho : c.output.read = Γ.start
      · rw [ite_eq_left ho, hro.2.2 ho]
      · rw [ite_eq_right ho]

/-- Multi-step correspondence. -/
theorem descOfTM_reachesIn {t : ℕ} {c c' : Cfg 1 M.Q}
    (h : M.reachesIn t c c') :
    M.descOfTM.toTM.reachesIn t (M.descCfg c) (M.descCfg c') := by
  induction h with
  | zero => exact .zero
  | step hstep _ ih =>
    exact .step (by rw [descOfTM_step_comm, hstep]; rfl) ih

/-- **Extraction fidelity**: the interpreted description of a machine
    decides the same language in exactly the same time. -/
theorem descOfTM_decidesInTime {L : Language} {T : ℕ → ℕ}
    (h : M.DecidesInTime L T) :
    M.descOfTM.toTM.DecidesInTime L T := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hmem, hnmem⟩ := h x
  refine ⟨M.descCfg c', t, ht, ?_, ?_, ?_, ?_⟩
  · rw [← descOfTM_initCfg]; exact M.descOfTM_reachesIn hreach
  · rwa [descOfTM_halted]
  · exact hmem
  · exact hnmem

/-- Every language decidable by a single-work-tape machine is decidable by
    an interpreted *well-formed description* in the same time bound. -/
theorem exists_wf_desc_decidesInTime {L : Language} {T : ℕ → ℕ} (M : TM 1)
    (h : M.DecidesInTime L T) :
    ∃ d : TMDesc, d.WF ∧ d.toTM.DecidesInTime L T :=
  ⟨M.descOfTM, M.descOfTM_wf, M.descOfTM_decidesInTime h⟩

end TM

end Complexity
