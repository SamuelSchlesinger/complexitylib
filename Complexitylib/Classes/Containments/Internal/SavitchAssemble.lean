/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.SavitchReach
public import Complexitylib.Classes.Containments.Internal.SpaceIterate

/-!
# Savitch's machine

⚠️ Unreviewed by Bolton

Everything is in place: `Complexity.savG` is the polynomial-time function
`Complexity.SpaceIter.mem_PSPACE_of_iterate` wants, `Complexity.Sav.run_top` says
its orbit reaches an answer, `Complexity.Sav.runBound_le` bounds how long that
takes, and `Complexity.Sav.StkSize` bounds how much room it needs. This file puts
them together.

## Main results

- `Complexity.savitch_mem_PSPACE` — a language whose membership is reachability
  within `2 ^ poly` steps of a space-bounded machine is in `PSPACE`
-/

@[expose] public section

namespace Complexity

open Cobham

variable {k : ℕ}

/-! ## The run at a fixed input -/

/-- The abstract step `Complexity.savG` performs, at the ruler it builds. -/
noncomputable def savSemAt (tm : NTM k) (qp : Polynomial ℕ) (x : List Bool) :
    Sav.Sst → Sav.Sst := savSem tm (savR qp x)

/-- The answer the recursion returns at `x`. -/
noncomputable def savAns (tm : NTM k) (qp lp : Polynomial ℕ) (x : List Bool) : Bool :=
  Sav.frameVal (baseReachB tm (savR qp x))
    (fun u => baseAccB tm (savR qp x) (savRuler k (savR qp x)) u)
    (savZero k (savR qp x)) (savRoot tm qp lp x)

/-- What a run of `T` steps at `x` achieves: the flag stays down, then goes up,
then becomes the answer. -/
noncomputable def SavRunSpec (tm : NTM k) (qp lp : Polynomial ℕ) (x : List Bool)
    (T : ℕ) : Prop :=
  T ≤ Sav.runBound (savZero k (savR qp x)).length (lp.eval x.length) ∧
    (∀ j ≤ T, ((savSemAt tm qp x)^[j] (savInitSst tm qp lp x)).done = false) ∧
    (savSemAt tm qp x)^[T + 1] (savInitSst tm qp lp x)
      = ⟨true, savAns tm qp lp x, some (savAns tm qp lp x), []⟩ ∧
    (savSemAt tm qp x)^[T + 2] (savInitSst tm qp lp x)
      = ⟨savAns tm qp lp x, savAns tm qp lp x, some (savAns tm qp lp x), []⟩

theorem savRun_exists (tm : NTM k) (qp lp : Polynomial ℕ) (x : List Bool) :
    ∃ T, SavRunSpec tm qp lp x T := by
  have hlvl : (savRoot tm qp lp x).lvl.length = lp.eval x.length := by
    rw [savRoot, polyRuler_length]
  have hok : Sav.FrmOk (baseReachB tm (savR qp x)) (savZero k (savR qp x))
      (savRoot tm qp lp x) := ⟨rfl, by rw [savRoot]; simp⟩
  obtain ⟨T, hT, h⟩ := Sav.run_top (baseReachB tm (savR qp x))
    (fun u => baseAccB tm (savR qp x) (savRuler k (savR qp x)) u)
    (savZero k (savR qp x)) (binValLE_savZero k _) (savRoot tm qp lp x) hok
  rw [hlvl] at hT
  exact ⟨T, hT, h⟩

/-- The number of steps Savitch's recursion takes at `x`. -/
noncomputable def savT (tm : NTM k) (qp lp : Polynomial ℕ) (x : List Bool) : ℕ :=
  Classical.choose (savRun_exists tm qp lp x)

theorem savT_spec (tm : NTM k) (qp lp : Polynomial ℕ) (x : List Bool) :
    SavRunSpec tm qp lp x (savT tm qp lp x) :=
  Classical.choose_spec (savRun_exists tm qp lp x)

/-! ## The pieces of the space-bounded iteration -/

section

variable (tm : NTM k) {L : Language} {S : ℕ → ℕ} (hdec : tm.DecidesInSpace L S)
  (qp lp : Polynomial ℕ)
  (hqp : ∀ n, n + S n + 1 ≤ qp.eval n)
  (hcardq : ∀ n, Fintype.card tm.Q ≤ blockWidth (qp.eval n))

include hdec hqp hcardq in
/-- **The answer the recursion returns is membership.** -/
theorem frameVal_savRoot (x : List Bool)
    (hmem : x ∈ L ↔ ∃ c, tm.ReachesCfgLe (2 ^ lp.eval x.length) (tm.initCfg x) c ∧
      tm.halted c ∧ c.output.cells 1 = Γ.one) :
    savAns tm qp lp x = true ↔ x ∈ L := by
  have hW := hqp x.length
  have hxW : x.length ≤ qp.eval x.length := by omega
  have hR : savR qp x = blockRuler (qp.eval x.length) := savR_eq qp x
  have hfresh := Sav.frameVal_fresh (baseReachB tm (savR qp x))
    (fun u => baseAccB tm (savR qp x) (savRuler k (savR qp x)) u)
    (savZero k (savR qp x)) (binValLE_savZero k _)
    (f := savRoot tm qp lp x) (by rw [savRoot])
  rw [savAns, hfresh]
  have hkind : (savRoot tm qp lp x).kind = true := rfl
  have hu : (savRoot tm qp lp x).u = Cobham.cfgCode (qp.eval x.length) (tm.initCfg x) := by
    rw [savRoot, hR, initRecord_eq tm _ x hxW]
  have hl : (savRoot tm qp lp x).lvl.length = lp.eval x.length := by
    rw [savRoot, polyRuler_length]
  rw [hkind, ite_eq_left rfl, hu, hl, hR]
  rw [accB_cfgCode tm hdec x (qp.eval x.length) (hcardq x.length) hW _ _
    (NTM.reachesCfg_refl tm _), hmem]

end

/-! ## The whole containment -/

/-- **Savitch's machine.** A language whose membership is reachability within
`2 ^ lp(|x|)` steps of a machine bounded by `S` is in `PSPACE`. -/
theorem savitch_mem_PSPACE (tm : NTM k) {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (qp lp r w : Polynomial ℕ)
    (hqp : ∀ n, n + S n + 1 ≤ qp.eval n)
    (hcardq : ∀ n, Fintype.card tm.Q ≤ blockWidth (qp.eval n))
    (hmem : ∀ x : List Bool, x ∈ L ↔ ∃ c, tm.ReachesCfgLe (2 ^ lp.eval x.length)
      (tm.initCfg x) c ∧ tm.halted c ∧ c.output.cells 1 = Γ.one)
    (hr : ∀ n, 2 * (2 * (2 * qp.eval n + 2)
        + (lp.eval n + 1) * (2 * (2 * lp.eval n
            + 5 * (codeBlocks k * (2 * qp.eval n + 2)) + 14) + 2) + 14) + 2 + n ≤ r.eval n)
    (hw : ∀ n, (codeBlocks k * (2 * qp.eval n + 2) + 3) * lp.eval n + 2 ≤ w.eval n) :
    L ∈ PSPACE := by
  classical
  -- the standing abbreviations at a fixed input
  set G : List Bool → List Bool := savG tm qp lp with hG
  have hGfp : G ∈ FP := savG_mem_FP tm qp lp
  set Nof : List Bool → ℕ := fun x => savT tm qp lp x + 2 with hNof
  -- the ruler and the widths
  have hRlen : ∀ x : List Bool, (savR qp x).length = 2 * qp.eval x.length + 2 := by
    intro x
    rw [savR_eq, blockRuler_length, blockWidth]
    ring
  have hzlen : ∀ x : List Bool,
      (savZero k (savR qp x)).length = codeBlocks k * (2 * qp.eval x.length + 2) := by
    intro x
    rw [savZero_length, hRlen]
  -- the orbit
  have horb : ∀ (x : List Bool) (j : ℕ), G^[j + 1] (pair [] x)
      = pair (encSst (savR qp x) ((savSemAt tm qp x)^[j] (savInitSst tm qp lp x))) x := by
    intro x j
    rw [hG, savG_iterate]
    rfl
  -- the stack invariant along the orbit
  have hstk : ∀ (x : List Bool) (j : ℕ),
      Sav.StkSize (lp.eval x.length) (codeBlocks k * (2 * qp.eval x.length + 2))
        ((savSemAt tm qp x)^[j] (savInitSst tm qp lp x)).stk := by
    intro x j
    have hxW : x.length ≤ qp.eval x.length := by have := hqp x.length; omega
    have hu : (savRoot tm qp lp x).u.length
        = codeBlocks k * (2 * qp.eval x.length + 2) := by
      rw [savRoot, savR_eq, initRecord_eq tm _ x hxW, cfgCode_length, blockRuler_length,
        blockWidth]
      ring
    have h0 : Sav.StkSize (lp.eval x.length) (codeBlocks k * (2 * qp.eval x.length + 2))
        (savInitSst tm qp lp x).stk := by
      refine ⟨?_, ⟨by rw [hu], ?_, ?_⟩, trivial⟩
      · show ([] : List Sav.Frm).length + (savRoot tm qp lp x).lvl.length = lp.eval x.length
        rw [savRoot]
        simp
      · rw [savRoot]
        exact le_of_eq (hzlen x)
      · rw [savRoot]
        exact le_of_eq (hzlen x)
    exact Sav.iterate_stkSize _ _ _ (le_of_eq (hzlen x)) j _ h0
  -- the four contracts
  have hN : ∀ x : List Bool, Nof x = savT tm qp lp x + 2 := fun _ => rfl
  refine SpaceIter.mem_PSPACE_of_iterate hGfp r w Nof ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- lengths
    intro x i _
    have hbase := hr x.length
    cases i with
    | zero =>
        rw [Function.iterate_zero_apply, pair_length, List.length_nil]
        omega
    | succ j =>
        rw [horb x j, pair_length]
        have := encSst_length_le (Lmax := lp.eval x.length)
          (Wm := codeBlocks k * (2 * qp.eval x.length + 2)) (savR qp x) _ (hstk x j)
        rw [hRlen x] at this
        omega
  · intro x
    rw [hN x]
    omega
  · -- the step count
    intro x
    obtain ⟨hT, _, _, _⟩ := savT_spec tm qp lp x
    have hle := Sav.runBound_le (savZero k (savR qp x)).length (lp.eval x.length)
    have hmono : (2 : ℕ) ^ (((savZero k (savR qp x)).length + 3) * lp.eval x.length + 2)
        ≤ 2 ^ w.eval x.length := by
      refine Nat.pow_le_pow_right (by omega) ?_
      rw [hzlen x]
      exact hw x.length
    rw [hN x]
    omega
  · -- the flag stays down
    intro x i hi hlt
    obtain ⟨_, hdown, _, _⟩ := savT_spec tm qp lp x
    rw [hN x] at hlt
    cases i with
    | zero => omega
    | succ j =>
        rw [horb x j, headD_pair_encSst]
        exact hdown j (by omega)
  · -- the flag goes up
    intro x
    obtain ⟨_, _, hup, _⟩ := savT_spec tm qp lp x
    rw [hN x, show savT tm qp lp x + 2 = savT tm qp lp x + 1 + 1 from rfl,
      horb x (savT tm qp lp x + 1), headD_pair_encSst, hup]
  · intro x
    rw [hN x, show savT tm qp lp x + 2 + 1 = savT tm qp lp x + 2 + 1 from rfl,
      horb x (savT tm qp lp x + 2)]
    intro hc
    have := congrArg List.length hc
    rw [pair_length] at this
    simp at this
  · -- the answer
    intro x
    obtain ⟨_, _, _, hans⟩ := savT_spec tm qp lp x
    rw [hN x, horb x (savT tm qp lp x + 2), headD_pair_encSst, hans]
    exact (frameVal_savRoot tm hdec qp lp hqp hcardq x (hmem x)).symm

/-! ## The containment -/

/-- The polynomial bounding the width of the window Savitch's machine writes on. -/
noncomputable def savWidthPoly (cardQ : ℕ) (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X + p + Polynomial.C 1 + Polynomial.C cardQ

/-- The polynomial bounding the length of the state Savitch's machine carries. -/
noncomputable def savStatePoly (k : ℕ) (qp lp : Polynomial ℕ) : Polynomial ℕ :=
  2 * (2 * (2 * qp + 2)
      + (lp + 1) * (2 * (2 * lp + 5 * (Polynomial.C (codeBlocks k) * (2 * qp + 2)) + 14) + 2)
      + 14) + 2 + Polynomial.X

/-- The polynomial bounding the logarithm of the number of steps it takes. -/
noncomputable def savCountPoly (k : ℕ) (qp lp : Polynomial ℕ) : Polynomial ℕ :=
  (Polynomial.C (codeBlocks k) * (2 * qp + 2) + 3) * lp + 2

theorem savWidthPoly_eval (cardQ : ℕ) (p : Polynomial ℕ) (n : ℕ) :
    (savWidthPoly cardQ p).eval n = n + p.eval n + 1 + cardQ := by
  simp [savWidthPoly]

theorem savStatePoly_eval (k : ℕ) (qp lp : Polynomial ℕ) (n : ℕ) :
    (savStatePoly k qp lp).eval n
      = 2 * (2 * (2 * qp.eval n + 2)
          + (lp.eval n + 1) * (2 * (2 * lp.eval n
              + 5 * (codeBlocks k * (2 * qp.eval n + 2)) + 14) + 2) + 14) + 2 + n := by
  simp [savStatePoly]

theorem savCountPoly_eval (k : ℕ) (qp lp : Polynomial ℕ) (n : ℕ) :
    (savCountPoly k qp lp).eval n
      = (codeBlocks k * (2 * qp.eval n + 2) + 3) * lp.eval n + 2 := by
  simp [savCountPoly]

/-- **`NPSPACE ⊆ PSPACE`** (Savitch's theorem). -/
theorem NPSPACE_subset_PSPACE_internal : NPSPACE ⊆ PSPACE := by
  intro L hL
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hL
  obtain ⟨k, tm, S, hdec, hS⟩ := hm
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hS
  set lp : Polynomial ℕ := codeExpBound (Fintype.card tm.Q) k p with hlp
  set qp : Polynomial ℕ := savWidthPoly (Fintype.card tm.Q) p with hqpdef
  have hqe : ∀ n, qp.eval n = n + p.eval n + 1 + Fintype.card tm.Q := by
    intro n
    rw [hqpdef, savWidthPoly_eval]
  have hqp : ∀ n, n + S n + 1 ≤ qp.eval n := by
    intro n
    have := hp n
    rw [hqe]
    omega
  have hcardq : ∀ n, Fintype.card tm.Q ≤ blockWidth (qp.eval n) := by
    intro n
    rw [blockWidth, hqe]
    omega
  have hreach : ∀ x : List Bool, x ∈ L ↔
      ∃ c, tm.ReachesCfgLe (2 ^ lp.eval x.length) (tm.initCfg x) c ∧ tm.halted c ∧
        c.output.cells 1 = Γ.one := by
    intro x
    rw [mem_iff_exists_accepting_reachable hdec x]
    constructor
    · rintro ⟨c, hr, hh, ho⟩
      exact ⟨c, (NTM.reachesCfg_iff_reachesCfgLe tm _ (cfgCode x.length (S x.length))
        (fun ha hb => NTM.cfgCode_inj_of_reachesCfg hdec x ha hb)
        (card_Code_le_two_pow_poly tm.Q k S p hp x.length) c).mp hr, hh, ho⟩
    · rintro ⟨c, hle, hh, ho⟩
      exact ⟨c, (NTM.reachesCfg_iff_reachesCfgLe tm _ (cfgCode x.length (S x.length))
        (fun ha hb => NTM.cfgCode_inj_of_reachesCfg hdec x ha hb)
        (card_Code_le_two_pow_poly tm.Q k S p hp x.length) c).mpr hle, hh, ho⟩
  exact savitch_mem_PSPACE tm hdec qp lp (savStatePoly k qp lp) (savCountPoly k qp lp)
    hqp hcardq hreach (fun n => le_of_eq (savStatePoly_eval k qp lp n).symm)
    (fun n => le_of_eq (savCountPoly_eval k qp lp n).symm)

end Complexity
