/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import Complexitylib.Models.TuringMachine.Hoare.Defs
public import Complexitylib.Models.TuringMachine.Subroutines
public import Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# Right-scanner correctness

Exact simulation proof for `TM.scanRightTM`. A target work tape containing a
completed binary string is scanned from cell one to its first append blank in
`|bits| + 1` steps. The input tape, output tape, and every unrelated work tape
are preserved exactly when their heads read a non-`▷` symbol.

The public compositional theorem is stated in
`Complexitylib.Models.TuringMachine.Subroutines.ScanRight`.
-/


public section

namespace Complexity

namespace TM

/-! ## Exact scanner steps -/

/-- Scanning a bit advances only the target work-tape head. -/
private theorem scanRightTM_step_bit {n : ℕ} (idx : Fin n)
    (c : Cfg n (scanRightTM idx).Q) (bit : Bool)
    (hst : c.state = ScanPhase.scanning)
    (hread : (c.work idx).read = Γ.ofBool bit)
    (hinp : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    (scanRightTM idx).step c = some
      { state := ScanPhase.scanning
        input := c.input
        work := Function.update c.work idx ((c.work idx).move Dir3.right)
        output := c.output } := by
  have hstate : c.state ≠ (scanRightTM idx).qhalt := by
    simp [scanRightTM, hst]
  have hnotBlank : (c.work idx).read ≠ Γ.blank := by
    rw [hread]
    cases bit <;> decide
  rw [TM.step, ite_eq_right hstate]
  simp only [scanRightTM, hst, hnotBlank, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hi : i = idx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      apply writeAndMove_readBack
      rw [hread]
      cases bit <;> decide
    · rw [ite_eq_right hi, Function.update_of_ne hi]
      exact transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self hout

/-- Reading the append blank halts without changing any tape. -/
private theorem scanRightTM_step_blank {n : ℕ} (idx : Fin n)
    (c : Cfg n (scanRightTM idx).Q)
    (hst : c.state = ScanPhase.scanning)
    (hread : (c.work idx).read = Γ.blank)
    (hinp : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    (scanRightTM idx).step c = some
      { state := ScanPhase.done
        input := c.input
        work := c.work
        output := c.output } := by
  have hstate : c.state ≠ (scanRightTM idx).qhalt := by
    simp [scanRightTM, hst]
  rw [TM.step, ite_eq_right hstate]
  simp only [scanRightTM, hst, hread, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hi : i = idx
    · subst i
      exact transitionTape_eq_self (by rw [hread]; decide)
    · exact transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self hout

/-! ## Exact scan loop -/

/-- Scan the `rem` unvisited bits starting at cell `k + 1`, followed by the
terminating blank step. All frame equalities are stated against fixed ghost
tapes so they compose without reconstructing transition-level invariants. -/
private theorem scanRightTM_run {n : ℕ} (idx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hstring : (work₀ idx).HasBinaryString bits)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∀ rem k (c : Cfg n (scanRightTM idx).Q),
      bits.length = k + rem →
      c.state = ScanPhase.scanning →
      c.input = inp₀ →
      (∀ i, i ≠ idx → c.work i = work₀ i) →
      (c.work idx).cells = (work₀ idx).cells →
      (c.work idx).head = k + 1 →
      c.output = out₀ →
      ∃ c',
        (scanRightTM idx).reachesIn (rem + 1) c c' ∧
        (scanRightTM idx).halted c' ∧
        c'.input = inp₀ ∧
        (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
        (c'.work idx).cells = (work₀ idx).cells ∧
        (c'.work idx).HasBinaryPrefix bits ∧
        c'.output = out₀ := by
  intro rem
  induction rem with
  | zero =>
      intro k c hlen hst hinput hwork hcells hhead houtput
      have hk : k = bits.length := by omega
      subst k
      have hblank : (c.work idx).read = Γ.blank := by
        rw [Tape.read, hhead, hcells]
        exact hstring.2.2 bits.length le_rfl
      have hstep := scanRightTM_step_blank idx c hst hblank
        (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      have hprefix : (c.work idx).HasBinaryPrefix bits :=
        Tape.hasBinaryPrefix_of_hasBinaryString hstring hhead hcells
      exact ⟨_, .step hstep .zero, rfl, hinput, hwork, hcells, hprefix, houtput⟩
  | succ rem ih =>
      intro k c hlen hst hinput hwork hcells hhead houtput
      have hk : k < bits.length := by omega
      have hread : (c.work idx).read = Γ.ofBool (bits[k]'hk) := by
        rw [Tape.read, hhead, hcells]
        exact hstring.2.1 k hk
      have hstep := scanRightTM_step_bit idx c (bits[k]'hk) hst hread
        (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let c₁ : Cfg n (scanRightTM idx).Q :=
        { state := ScanPhase.scanning
          input := c.input
          work := Function.update c.work idx ((c.work idx).move Dir3.right)
          output := c.output }
      have hc₁Input : c₁.input = inp₀ := hinput
      have hc₁Other : ∀ i, i ≠ idx → c₁.work i = work₀ i := by
        intro i hi
        show Function.update c.work idx ((c.work idx).move Dir3.right) i = work₀ i
        rw [Function.update_of_ne hi]
        exact hwork i hi
      have hc₁Cells : (c₁.work idx).cells = (work₀ idx).cells := by
        show (Function.update c.work idx ((c.work idx).move Dir3.right) idx).cells = _
        rw [Function.update_self, Tape.move_cells]
        exact hcells
      have hc₁Head : (c₁.work idx).head = (k + 1) + 1 := by
        show (Function.update c.work idx ((c.work idx).move Dir3.right) idx).head = _
        rw [Function.update_self]
        simp [Tape.move, hhead]
      have hc₁Output : c₁.output = out₀ := houtput
      obtain ⟨c', hreach, hhalt, hinput', hwork', hcells', hprefix', houtput'⟩ :=
        ih (k + 1) c₁ (by omega) rfl hc₁Input hc₁Other hc₁Cells hc₁Head hc₁Output
      exact ⟨c', .step hstep hreach, hhalt, hinput', hwork', hcells', hprefix', houtput'⟩

/-- Internal proof of the public exact frame-preserving scanner endpoint. The
run uses one transition per bit and one transition on the append blank. -/
theorem scanRightTM_reachesIn_frame_internal {n : ℕ}
    (idx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hstring : (work₀ idx).HasBinaryString bits)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∃ c',
      (scanRightTM idx).reachesIn (bits.length + 1)
        { state := (scanRightTM idx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (scanRightTM idx).halted c' ∧
      c'.input = inp₀ ∧
      (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
      (c'.work idx).cells = (work₀ idx).cells ∧
      (c'.work idx).HasBinaryPrefix bits ∧
      c'.output = out₀ := by
  obtain ⟨c', hreach, hhalt, hinput, hwork, hcells, hprefix, houtput⟩ :=
    scanRightTM_run idx bits inp₀ work₀ out₀ hstring hinp hother hout
      bits.length 0
      { state := ScanPhase.scanning
        input := inp₀
        work := work₀
        output := out₀ }
      (by omega) rfl rfl (fun _ _ => rfl) rfl hstring.1 rfl
  exact ⟨c', hreach, hhalt, hinput, hwork, hcells, hprefix, houtput⟩

/-- Internal proof of the public frame-preserving bounded scanner contract. -/
theorem scanRightTM_hoareTime_frame_internal {n : ℕ}
    (idx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hstring : (work₀ idx).HasBinaryString bits)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    (scanRightTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).cells = (work₀ idx).cells ∧
        (work idx).HasBinaryPrefix bits ∧
        out = out₀)
      (bits.length + 1) := by
  rintro inp work out ⟨hinputEq, hworkEq, houtputEq⟩
  subst inp
  subst work
  subst out
  obtain ⟨c', hreach, hhalt, hinput, hwork, hcells, hprefix, houtput⟩ :=
    scanRightTM_reachesIn_frame_internal
      idx bits inp₀ work₀ out₀ hstring hinp hother hout
  exact ⟨c', bits.length + 1, le_rfl, hreach, hhalt,
    hinput, hwork, hcells, hprefix, houtput⟩

end TM

end Complexity
