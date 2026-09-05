/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.BodyAssembly
public import Complexitylib.Encoding.Pairing

/-!
# Universal machine: simulation bridges

Bridges between the phase machines' Hoare specifications and the body's
standing invariant `SimInv`:

* the initialization machine's postcondition realizes `SimInv` at the
  interpreted machine's initial configuration (for **every** binary `α` —
  the decoded start state's fixed-width encoding is exactly the first
  description field, by the `toBits`/`fromBits` roundtrip at the field's
  own width);
* verdict and output-growth facts used by the loop and extraction proofs.

The completed loop simulation and headline universal-machine theorems are in
`UTM/SimLoop.lean` and `UTM/Universal.lean`.
-/


public section

namespace Complexity

namespace TM.UTMBody

/-- The first description field *is* the fixed-width encoding of the
    decoded start state — for arbitrary `α`. -/
theorem qstartField_eq_encoding (α : List Bool) :
    (takeField (groupPairs α)).1
      = bitsToSyms (Nat.toBits (decodeDesc α).w
          ((decodeDesc α).toTM.qstart.val)) := by
  have hval : (decodeDesc α).toTM.qstart.val
      = (decodeDesc α).qstart % 2 ^ (decodeDesc α).w := rfl
  have hlt : (decodeDesc α).qstart < 2 ^ (decodeDesc α).w := by
    show fieldNat (takeField (groupPairs α)).1 < _
    calc fieldNat (takeField (groupPairs α)).1
        < 2 ^ ((takeField (groupPairs α)).1.filterMap symBit?).length :=
          Nat.fromBits_lt_pow_length _
      _ ≤ 2 ^ (takeField (groupPairs α)).1.length :=
          Nat.pow_le_pow_right (by omega) (List.length_filterMap_le ..)
  rw [hval, Nat.mod_eq_of_lt hlt]
  have hnb : ∀ s ∈ (takeField (groupPairs α)).1, s ≠ Γw.blank :=
    fun s hs => takeField_fst_ne_blank _ s hs
  have hbits := bitsToSyms_filterMap_of_ne_blank hnb
  have hlen : ((takeField (groupPairs α)).1.filterMap symBit?).length
      = (decodeDesc α).w := by
    have := congrArg List.length hbits
    rw [bitsToSyms_length] at this
    exact this
  conv_lhs => rw [← hbits]
  congr 1
  show List.filterMap symBit? (takeField (groupPairs α)).1
      = Nat.toBits (decodeDesc α).w
          (Nat.fromBits ((takeField (groupPairs α)).1.filterMap symBit?))
  rw [← hlen, Nat.toBits_fromBits]

/-- A cleared, started tape shadows the empty simulated tape. -/
theorem vshift_initTape_nil {t : Tape} (h : t.HoldsExact []) (hh : t.head = 1) :
    VShift (Tape.init []) t := by
  refine ⟨?_, by rw [hh]; rfl⟩
  funext k
  by_cases hk0 : k = 0
  · subst hk0
    exact h.1
  · by_cases hk1 : k = 1
    · subst hk1
      have := (Tape.HoldsExact.nil_iff.mp h).2 0
      simpa using this
    · have := (Tape.HoldsExact.nil_iff.mp h).2 (k - 1)
      rw [show k - 1 + 1 = k by omega] at this
      rw [this]
      simp only [hk0, hk1, ite_false]
      show Γ.blank = (Tape.init []).cells (k - 1)
      simp [Tape.init, show k - 1 ≠ 0 by omega]

/-- The shifted copy of `x` (cells `▷ □ x ⋯`, head 1) shadows the
    interpreted machine's initial input tape. -/
theorem vshift_initTape_x {t : Tape} (x : List Bool)
    (hc : t.cells = fun k => if k = 0 then Γ.start else if k = 1 then Γ.blank
      else (((x.map Γ.ofBool))[k - 2]?).getD Γ.blank)
    (hh : t.head = 1) :
    VShift (Tape.init (x.map Γ.ofBool)) t := by
  refine ⟨?_, by rw [hh]; rfl⟩
  rw [hc]
  funext k
  by_cases hk0 : k = 0
  · simp [hk0]
  · by_cases hk1 : k = 1
    · simp [hk1]
    · simp only [hk0, hk1, ite_false]
      show _ = (Tape.init (x.map Γ.ofBool)).cells (k - 1)
      simp only [Tape.init, show k - 1 ≠ 0 by omega, ite_false,
        show k - 1 - 1 = k - 2 by omega]

/-- **Initialization realizes the invariant**: the tape shape guaranteed by
    `initTM`'s postcondition is `SimInv` at the interpreted machine's
    initial configuration. -/
theorem initPost_simInv (α x : List Bool)
    (inp : Tape) (work : Fin 6 → Tape) (out : Tape)
    (hpost :
      inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧
      (work 0).cells = (fun k => if k = 0 then Γ.start else if k = 1 then Γ.blank
        else (((x.map Γ.ofBool))[k - 2]?).getD Γ.blank) ∧ (work 0).head = 1 ∧
      (work 1).HoldsExact [] ∧ (work 1).head = 1 ∧
      (work 2).HoldsExact [] ∧ (work 2).head = 1 ∧
      (work 3).HoldsExact (takeField (groupPairs α)).1 ∧ (work 3).head = 1 ∧
      (work 4).HoldsExact (groupPairs α) ∧ (work 4).head = 1 ∧
      (work 5).HoldsExact [] ∧ (work 5).head = 1 ∧
      out.cells = (Tape.init []).cells ∧ out.head = 1)
    (hinp_head : 1 ≤ inp.head) :
    SimInv α ((decodeDesc α).toTM.initCfg x) inp work out := by
  obtain ⟨hinp, hw0c, hw0h, hw1, hw1h, hw2, hw2h, hw3, hw3h, hw4, hw4h,
    hw5, hw5h, houtc, houth⟩ := hpost
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact vshift_initTape_x x hw0c hw0h
  · exact vshift_initTape_nil hw1 hw1h
  · exact vshift_initTape_nil hw2 hw2h
  · exact Tape.StartInvariant.init_ofBool x
  · show (Tape.init ([] : List Γ)).StartInvariant
    simpa using Tape.StartInvariant.init_ofBool []
  · show (Tape.init ([] : List Γ)).StartInvariant
    simpa using Tape.StartInvariant.init_ofBool []
  · left
    have hstate : ((decodeDesc α).toTM.initCfg x).state
        = (decodeDesc α).toTM.qstart := rfl
    constructor
    · rw [hstate]
      show (decodeDesc α).qstart % 2 ^ (decodeDesc α).w < 2 ^ (decodeDesc α).w
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · rw [hstate, ← qstartField_eq_encoding]
      exact hw3
  · exact hw3h
  · exact hw4
  · exact hw4h
  · exact hw5
  · exact hw5h
  · rw [Tape.read, hinp]
    exact (Tape.StartInvariant.init_ofBool (pair α x)).2 inp.head hinp_head
  · rw [Tape.read, houtc, houth]
    simp [Tape.init]

/-- The halt test's comparison decides exactly the interpreted machine's
    halt condition, under the invariant. -/
theorem simInv_verdict (α : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (hinv : SimInv α mc inp work out) :
    ∃ stSyms, (work stT).HoldsExact stSyms ∧ (∀ s ∈ stSyms, s ≠ Γw.blank) ∧
      ((stSyms = qhaltField (groupPairs α))
        ↔ mc.state = (decodeDesc α).toTM.qhalt) := by
  obtain ⟨S, hhold, hnb, hwhich⟩ := hinv.state_syms_ne_blank
  refine ⟨S, hhold, hnb, ?_⟩
  rcases hwhich with ⟨hlt, rfl⟩ | ⟨hq, rfl⟩
  · rw [verdict_running α hlt]
    constructor
    · intro hv
      exact Fin.val_injective (by
        show mc.state.val = min (decodeDesc α).qhalt (2 ^ (decodeDesc α).w)
        exact hv)
    · intro hs
      show mc.state.val = min (decodeDesc α).qhalt (2 ^ (decodeDesc α).w)
      rw [hs]
      rfl
  · exact iff_of_true rfl hq

-- ════════════════════════════════════════════════════════════════════════
-- Tape support is bounded by time
-- ════════════════════════════════════════════════════════════════════════

/-- One tape action moves the head at most one cell. -/
theorem writeAndMove_head_le (t : Tape) (s : Γ) (d : Dir3) :
    (t.writeAndMove s d).head ≤ t.head + 1 := by
  show ((t.write s).move d).head ≤ t.head + 1
  cases d <;> (simp [Tape.move, Tape.write_head]; try omega)

/-- One tape action leaves cells other than the head untouched. -/
theorem writeAndMove_cells_ne (t : Tape) (s : Γ) (d : Dir3) {j : ℕ}
    (hj : j ≠ t.head) : (t.writeAndMove s d).cells j = t.cells j := by
  show ((t.write s).move d).cells j = t.cells j
  have hw : ((t.write s)).cells j = t.cells j := by
    unfold Tape.write
    split
    · rfl
    · exact Function.update_of_ne hj ..
  cases d <;> simpa [Tape.move] using hw

/-- After `t` steps the output head has advanced at most `t` cells. -/
theorem reachesIn_output_head_le {n : ℕ} {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      c'.output.head ≤ c.output.head + t := by
  intro t
  induction t with
  | zero =>
    intro c c' h
    cases h
    omega
  | succ t ih =>
    intro c c' h
    cases h with
    | step hstep hrest =>
      next c'' =>
      have h1 : c''.output.head ≤ c.output.head + 1 := by
        unfold TM.step at hstep
        split at hstep
        · exact absurd hstep (by simp)
        · simp only [Option.some.injEq] at hstep
          subst hstep
          exact writeAndMove_head_le ..
      have := ih hrest
      omega

/-- Cells beyond the output head's reach are never written. -/
theorem reachesIn_output_cells_far {n : ℕ} {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      ∀ j, c.output.head + t < j → c'.output.cells j = c.output.cells j := by
  intro t
  induction t with
  | zero =>
    intro c c' h j hj
    cases h
    rfl
  | succ t ih =>
    intro c c' h j hj
    cases h with
    | step hstep hrest =>
      next c'' =>
      have hhead : c''.output.head ≤ c.output.head + 1 := by
        unfold TM.step at hstep
        split at hstep
        · exact absurd hstep (by simp)
        · simp only [Option.some.injEq] at hstep
          subst hstep
          exact writeAndMove_head_le ..
      have hcell : c''.output.cells j = c.output.cells j := by
        unfold TM.step at hstep
        split at hstep
        · exact absurd hstep (by simp)
        · simp only [Option.some.injEq] at hstep
          subst hstep
          exact writeAndMove_cells_ne _ _ _ (by omega)
      rw [ih hrest j (by omega), hcell]

/-- From the initial configuration, the output tape has a first blank within
    `t + 1` cells after `t` steps. -/
theorem reachesIn_output_first_blank {n : ℕ} {tm : TM n} {t : ℕ}
    {x : List Bool} {c' : Cfg n tm.Q}
    (h : tm.reachesIn t (tm.initCfg x) c') :
    ∃ m, m ≤ t ∧ c'.output.cells (m + 2) = Γ.blank ∧
      ∀ j, j < m → c'.output.cells (j + 2) ≠ Γ.blank := by
  classical
  have hblank : c'.output.cells (t + 2) = Γ.blank := by
    rw [reachesIn_output_cells_far h (t + 2)
      (by simp [Tape.init])]
    simp [Tape.init]
  by_cases hall : ∃ m, m ≤ t ∧ c'.output.cells (m + 2) = Γ.blank
  · obtain ⟨m₀, -, -⟩ := hall
    have hP : ∃ m, c'.output.cells (m + 2) = Γ.blank := ⟨t, hblank⟩
    refine ⟨Nat.find hP, ?_, Nat.find_spec hP, fun j hj => Nat.find_min hP hj⟩
    exact Nat.le_of_not_lt fun hcon => (Nat.find_min hP hcon) hblank
  · exact absurd ⟨t, Nat.le_refl t, hblank⟩ hall

end TM.UTMBody

end Complexity
