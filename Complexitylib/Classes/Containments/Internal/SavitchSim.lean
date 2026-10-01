/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel’s dot
-/
module
public import Complexitylib.Classes.Containments.Internal.SavitchSem
public import Complexitylib.Classes.Containments.Internal.SavitchStep
public import Complexitylib.Classes.Containments.Internal.BinArith

/-!
# The encoded step simulates the abstract one

⚠️ Unreviewed by Bolton

`Complexity.savStep` is Savitch's recursion written on a bitstring, so that it
lands in `FP`; `Complexity.Sav.step` is the same recursion on an inductive state,
where it can be reasoned about. This file writes the encoding down and proves the
square commutes.

## Main definitions

- `Complexity.encFrm`, `Complexity.encSst` — the encoding of a frame and a state
- `Complexity.savSem` — the abstract step the encoded one simulates

## Main results

- `Complexity.savStep_encSst` — one encoded step is one abstract step
- `Complexity.savStep_iterate_encSst` — hence so is any number of them
-/

@[expose] public section

namespace Complexity

open Cobham

variable {k : ℕ}

/-! ## Flags as booleans -/

/-- The base reachability test, as a boolean. -/
noncomputable def baseReachB (tm : NTM k) (R u v : List Bool) : Bool :=
  (baseReach tm R u v).headD false

/-- The base acceptance test, as a boolean. -/
noncomputable def baseAccB (tm : NTM k) (R rl u : List Bool) : Bool :=
  (baseAcc tm R rl u).headD false

theorem baseReach_eq (tm : NTM k) (R u v : List Bool) :
    baseReach tm R u v = [baseReachB tm R u v] := by
  rcases baseReach_flag tm R u v with h | h <;> rw [baseReachB, h] <;> rfl

theorem baseAcc_eq (tm : NTM k) (R rl u : List Bool) :
    baseAcc tm R rl u = [baseAccB tm R rl u] := by
  rcases baseAcc_flag tm R rl u with h | h <;> rw [baseAccB, h] <;> rfl

/-! ## The encoding -/

/-- A returned value on the tape. -/
def encOpt : Option Bool → List Bool
  | none => []
  | some b => [b]

@[simp] theorem encOpt_none : encOpt none = [] := rfl

@[simp] theorem encOpt_some (b : Bool) : encOpt (some b) = [b] := rfl

/-- A frame on the tape. -/
def encFrm (f : Sav.Frm) : List Bool := mkFrame [f.kind] [f.ph] f.lvl f.u f.v f.m

/-- A state on the tape. -/
def encSst (R : List Bool) (s : Sav.Sst) : List Bool :=
  mkSt [s.done] [s.ans] R (encOpt s.ret) (encStack (s.stk.map encFrm))

/-- The abstract step the encoded one runs. -/
noncomputable def savSem (tm : NTM k) (R : List Bool) : Sav.Sst → Sav.Sst :=
  Sav.step (baseReachB tm R) (fun u => baseAccB tm R (savRuler k R) u) (savZero k R)

/-! ## The square commutes -/

@[simp] theorem stDone_encSst (R : List Bool) (s : Sav.Sst) :
    stDone (encSst R s) = [s.done] := by rw [encSst, stDone_mk]

@[simp] theorem stAns_encSst (R : List Bool) (s : Sav.Sst) :
    stAns (encSst R s) = [s.ans] := by rw [encSst, stAns_mk]

@[simp] theorem stR_encSst (R : List Bool) (s : Sav.Sst) :
    stR (encSst R s) = R := by rw [encSst, stR_mk]

@[simp] theorem stRet_encSst (R : List Bool) (s : Sav.Sst) :
    stRet (encSst R s) = encOpt s.ret := by rw [encSst, stRet_mk]

@[simp] theorem stStk_encSst (R : List Bool) (s : Sav.Sst) :
    stStk (encSst R s) = encStack (s.stk.map encFrm) := by rw [encSst, stStk_mk]

@[simp] theorem frKind_encFrm (f : Sav.Frm) : frKind (encFrm f) = [f.kind] := by
  rw [encFrm, frKind_mk]

@[simp] theorem frPh_encFrm (f : Sav.Frm) : frPh (encFrm f) = [f.ph] := by
  rw [encFrm, frPh_mk]

@[simp] theorem frLvl_encFrm (f : Sav.Frm) : frLvl (encFrm f) = f.lvl := by
  rw [encFrm, frLvl_mk]

@[simp] theorem frU_encFrm (f : Sav.Frm) : frU (encFrm f) = f.u := by
  rw [encFrm, frU_mk]

@[simp] theorem frV_encFrm (f : Sav.Frm) : frV (encFrm f) = f.v := by
  rw [encFrm, frV_mk]

@[simp] theorem frM_encFrm (f : Sav.Frm) : frM (encFrm f) = f.m := by
  rw [encFrm, frM_mk]

/-- **One encoded step is one abstract step.** The side condition rules out the
one shape the encoding cannot express: an empty stack with nothing returning. -/
theorem savStep_encSst (tm : NTM k) (R : List Bool) (s : Sav.Sst)
    (hne : s.stk = [] → s.ret ≠ none) :
    savStep tm (encSst R s) = encSst R (savSem tm R s) := by
  obtain ⟨d, a, r, stk⟩ := s
  rw [savSem]
  cases d
  · cases stk with
    | nil =>
        obtain ⟨b, rfl⟩ : ∃ b, r = some b := by
          cases r with
          | none => exact absurd rfl (hne rfl)
          | some b => exact ⟨b, rfl⟩
        rw [Sav.step_of_empty]
        simp [savStep, encSst, encOpt]
    | cons f fs =>
      cases r with
      | none =>
          by_cases hl : f.lvl = []
          · rw [Sav.step_base _ _ _ a f fs hl]
            cases hk : f.kind
            · simp [savStep, savDescend, savTop, savRest, stkTop, stkRest, encSst, encFrm, encOpt,
                emptyFlag_pair, hl, hk, Sav.baseVal, baseReach_eq]
            · simp [savStep, savDescend, savTop, savRest, stkTop, stkRest, encSst, encFrm, encOpt,
                emptyFlag_pair, hl, hk, Sav.baseVal, baseAcc_eq]
          · rw [Sav.step_push _ _ _ a f fs hl]
            obtain ⟨c, t, hct⟩ : ∃ c t, f.lvl = c :: t := by
              cases hlv : f.lvl with
              | nil => exact absurd hlv hl
              | cons c t => exact ⟨c, t, rfl⟩
            cases hp : f.ph
            · simp [savStep, savDescend, savChild, savTop, savRest, stkTop, stkRest,
                encSst, encFrm,
                encOpt, emptyFlag_pair, emptyFlag_cons, hct, hp, Sav.child, dropOne]
            · cases hk : f.kind
              · simp [savStep, savDescend, savChild, savTop, savRest, stkTop, stkRest,
                encSst, encFrm,
                  encOpt, emptyFlag_pair, emptyFlag_cons, hct, hp, hk, Sav.child, dropOne]
              · simp [savStep, savDescend, savChild, savTop, savRest, stkTop, stkRest,
                encSst, encFrm,
                  encOpt, emptyFlag_pair, emptyFlag_cons, hct, hp, hk, Sav.child, dropOne]
      | some b =>
          cases b
          · cases hov : bumpOver f.m
            · rw [Sav.step_ret_false_bump _ _ _ a f fs hov]
              simp [savStep, savReturn, savAdvance, savTop, savRest, stkTop, stkRest,
                encSst, encFrm,
                encOpt, emptyFlag_pair, emptyFlag_cons, hov]
            · rw [Sav.step_ret_false_over _ _ _ a f fs hov]
              simp [savStep, savReturn, savAdvance, savTop, savRest, stkTop, stkRest,
                encSst, encFrm,
                encOpt, emptyFlag_pair, emptyFlag_cons, hov]
          · cases hp : f.ph
            · rw [Sav.step_ret_true_of_ph_false _ _ _ a f fs hp]
              simp [savStep, savReturn, savTop, savRest, stkTop, stkRest, encSst, encFrm, encOpt,
                emptyFlag_pair, emptyFlag_cons, hp]
            · rw [Sav.step_ret_true_ph _ _ _ a f fs hp]
              simp [savStep, savReturn, savTop, savRest, stkTop, stkRest, encSst, encFrm, encOpt,
                emptyFlag_pair, emptyFlag_cons, hp]
  · rw [Sav.step_of_done]
    simp [savStep, encSst, encOpt]

/-! ## Iterating -/

theorem encSst_ne_nil (R : List Bool) (s : Sav.Sst) : encSst R s ≠ [] :=
  mkSt_ne_nil _ _ _ _ _

theorem savStep_iterate (tm : NTM k) (R : List Bool) :
    ∀ (j : ℕ) (s : Sav.Sst), Sav.StkOk s →
      (savStep tm)^[j] (encSst R s) = encSst R ((savSem tm R)^[j] s) := by
  intro j
  induction j with
  | zero => intro s _; rfl
  | succ j ih =>
      intro s h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        savStep_encSst tm R s h]
      exact ih _ (Sav.step_stkOk _ _ _ h)

/-- The root frame the recursion starts from. -/
noncomputable def savRoot (tm : NTM k) (qp lp : Polynomial ℕ) (x : List Bool) : Sav.Frm :=
  ⟨true, false, polyRuler lp x, initRecord tm (savR qp x) x, savZero k (savR qp x),
    savZero k (savR qp x)⟩

/-- The state `Complexity.savInit` builds, decoded. -/
noncomputable def savInitSst (tm : NTM k) (qp lp : Polynomial ℕ) (x : List Bool) : Sav.Sst :=
  ⟨false, false, none, [savRoot tm qp lp x]⟩

theorem savInit_eq (tm : NTM k) (qp lp : Polynomial ℕ) (x : List Bool) :
    savInit tm qp lp x = encSst (savR qp x) (savInitSst tm qp lp x) := rfl

theorem savSem_iterate_stkOk (tm : NTM k) (R : List Bool) :
    ∀ (j : ℕ) (s : Sav.Sst), Sav.StkOk s → Sav.StkOk ((savSem tm R)^[j] s) := by
  intro j
  induction j with
  | zero => intro s h; exact h
  | succ j ih =>
      intro s h
      rw [Function.iterate_succ_apply]
      exact ih _ (Sav.step_stkOk _ _ _ h)

theorem savInitSst_stkOk (tm : NTM k) (qp lp : Polynomial ℕ) (x : List Bool) :
    Sav.StkOk (savInitSst tm qp lp x) := by
  intro hc
  rw [savInitSst] at hc
  simp at hc

/-- **The packed orbit is the abstract one.** -/
theorem savG_iterate (tm : NTM k) (qp lp : Polynomial ℕ) (x : List Bool) :
    ∀ j : ℕ, (savG tm qp lp)^[j + 1] (pair [] x)
      = pair (encSst (savR qp x)
          ((savSem tm (savR qp x))^[j] (savInitSst tm qp lp x))) x := by
  have horbit (i : ℕ) : (savStep tm)^[i] (savInit tm qp lp x)
      = encSst (savR qp x)
          ((savSem tm (savR qp x))^[i] (savInitSst tm qp lp x)) := by
    rw [savInit_eq, savStep_iterate _ _ _ _ (savInitSst_stkOk tm qp lp x)]
  intro j
  change (initializedStep (savInit tm qp lp) (fun _ => savStep tm))^[j + 1] (pair [] x) = _
  rw [initializedStep_iterate _ _ _ j (fun i _ => by rw [horbit]; exact encSst_ne_nil _ _),
    horbit]

/-- The head of a packed state is its done flag. -/
theorem headD_pair_encSst (R : List Bool) (s : Sav.Sst) (x : List Bool) :
    (pair (encSst R s) x).headD false = s.done := by
  rw [encSst, mkSt, pair_cons_eq, pair_cons_eq]
  rfl

/-! ## How long an encoded state is -/

theorem encStack_length_le : ∀ (fs : List (List Bool)) (B : ℕ), (∀ f ∈ fs, f.length ≤ B) →
    (encStack fs).length ≤ fs.length * (2 * B + 2) :=
  StackEncoding.length_encode_le id

theorem encFrm_length_le {Lmax Wm : ℕ} {f : Sav.Frm} (hl : f.lvl.length ≤ Lmax)
    (hs : Sav.FrmSize Wm f) : (encFrm f).length ≤ 2 * Lmax + 5 * Wm + 14 := by
  obtain ⟨h1, h2, h3⟩ := hs
  rw [encFrm, mkFrame_length]
  simp only [List.length_cons, List.length_nil]
  omega

/-- **An encoded state is polynomially long.** -/
theorem encSst_length_le {Lmax Wm : ℕ} (R : List Bool) (s : Sav.Sst)
    (h : Sav.StkSize Lmax Wm s.stk) :
    (encSst R s).length
      ≤ 2 * R.length + (Lmax + 1) * (2 * (2 * Lmax + 5 * Wm + 14) + 2) + 14 := by
  have hall : ∀ g ∈ s.stk.map encFrm, g.length ≤ 2 * Lmax + 5 * Wm + 14 := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hl, hs⟩ := Sav.StkSize.mem_bound h f hf
    exact encFrm_length_le hl hs
  have hstk := encStack_length_le (s.stk.map encFrm) _ hall
  have hlen : (s.stk.map encFrm).length ≤ Lmax + 1 := by
    rw [List.length_map]
    exact Sav.StkSize.length_le h
  have hmul : (s.stk.map encFrm).length * (2 * (2 * Lmax + 5 * Wm + 14) + 2)
      ≤ (Lmax + 1) * (2 * (2 * Lmax + 5 * Wm + 14) + 2) := Nat.mul_le_mul_right _ hlen
  have hret : (encOpt s.ret).length ≤ 1 := by
    cases s.ret <;> simp
  rw [encSst, mkSt_length]
  simp only [List.length_cons, List.length_nil]
  omega

end Complexity
