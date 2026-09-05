/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.IPLeaf
public import Complexitylib.Classes.Containments.Internal.SpaceIterate

/-!
# `IP ⊆ PSPACE`, assembled

⚠️ Unreviewed by Bolton

Everything is in place: `Complexity.IPM.ipStep` is the walk of the game tree written inside the
polynomial-time algebra, `Complexity.Protocol.walk_decides` says its orbit ends with the
membership bit, `Complexity.IPM.runBound_le` bounds how long that takes, and
`Complexity.IPM.encSst_length_le` bounds how much room it needs. This file hands them to
`Complexity.SpaceIter.mem_PSPACE_of_iterate`.

## Main definitions

- `Complexity.ipG` — the function the space-bounded iteration runs

## Main results

- `Complexity.ipG_iterate` — the packed orbit is the abstract one
- `Complexity.IP_subset_PSPACE_internal` — the containment
-/

@[expose] public section

namespace Complexity

open Cobham

/-! ## The iterated function -/

/-- The function the space-bounded iteration runs: the running state is the first component and
the input the second, so the very first call — on `pair [] x` — builds the initial state. -/
noncomputable def ipG (prot : Protocol) (vd : List Bool → List Bool)
    (rp cp mp : Polynomial ℕ) (z : List Bool) : List Bool :=
  pair
    (selectHead (emptyFlag (pairFst z))
      (IPM.ipInit (polyRuler cp (pairSnd z)) (polyRuler rp (pairSnd z)))
      (IPM.ipStep (polyRuler mp (pairSnd z)) (polyRuler cp (pairSnd z))
        (okFn prot.vmsg vd (polyRuler rp (pairSnd z)) (pairSnd z)) (pairFst z)))
    (pairSnd z)

theorem ipG_nil (prot : Protocol) (vd : List Bool → List Bool) (rp cp mp : Polynomial ℕ)
    (x : List Bool) :
    ipG prot vd rp cp mp (pair [] x)
      = pair (IPM.ipInit (polyRuler cp x) (polyRuler rp x)) x := by
  rw [ipG, pairFst_pair, pairSnd_pair, emptyFlag_nil, selectHead_cons_true]

theorem ipG_step (prot : Protocol) (vd : List Bool → List Bool) (rp cp mp : Polynomial ℕ)
    (st x : List Bool) (h : st ≠ []) :
    ipG prot vd rp cp mp (pair st x)
      = pair (IPM.ipStep (polyRuler mp x) (polyRuler cp x)
          (okFn prot.vmsg vd (polyRuler rp x) x) st) x := by
  obtain ⟨b, t, rfl⟩ : ∃ b t, st = b :: t := by
    cases st with
    | nil => exact absurd rfl h
    | cons b t => exact ⟨b, t, rfl⟩
  rw [ipG, pairFst_pair, pairSnd_pair, emptyFlag_cons, selectHead_cons_false]

/-! ## The orbit -/

section

open Classical

variable (prot : Protocol) (vd : List Bool → List Bool) (rp cp mp : Polynomial ℕ)
  (hcp : ∀ n, prot.coins n = cp.eval n) (hmp : ∀ n, prot.msgLen n = mp.eval n)
  (hvd : ∀ z, vd z = [decide (z ∈ prot.verdict)])

include hcp in
theorem cr_length (x : List Bool) : (polyRuler cp x).length = (prot.walkParams x).t := by
  rw [polyRuler_length]
  show cp.eval x.length = prot.coins x.length
  rw [hcp]

include hmp in
theorem mr_length (x : List Bool) : (polyRuler mp x).length = (prot.walkParams x).m := by
  rw [polyRuler_length]
  show mp.eval x.length = prot.msgLen x.length
  rw [hmp]

include hcp hmp hvd in
/-- **The packed orbit is the abstract one.** -/
theorem ipG_iterate (x : List Bool) :
    ∀ j : ℕ, (ipG prot vd rp cp mp)^[j + 1] (pair [] x)
      = pair (IPM.encSst ((IPM.step (prot.walkParams x))^[j]
          ⟨false, false, none,
            [IPM.freshFrm (prot.walkParams x) [] (polyRuler rp x)]⟩)) x := by
  have hokf := okFn_hokf prot vd hvd (polyRuler rp x) x ((polyRuler rp x).length + 1) le_rfl
  intro j
  induction j with
  | zero =>
      rw [Function.iterate_one, ipG_nil,
        IPM.ipInit_eq _ (prot.walkParams x) (cr_length prot cp hcp x),
        Function.iterate_zero_apply]
  | succ j ih =>
      rw [Function.iterate_succ_apply' (IPM.step (prot.walkParams x)) j,
        Function.iterate_succ_apply', ih, ipG_step _ _ _ _ _ _ _ (IPM.encSst_ne_nil _),
        IPM.ipStep_encSst (prot.walkParams x) _ _ (mr_length prot mp hmp x)
          (cr_length prot cp hcp x) _ ((polyRuler rp x).length + 1) hokf _
          (IPM.iterate_encOk (prot.walkParams x) _ j _
            (IPM.encOk_start (prot.walkParams x) (polyRuler rp x)))]

end

/-! ## The run at a fixed input -/

open Classical in
/-- What a run of `T` steps at `x` achieves. -/
noncomputable def IPRunSpec (prot : Protocol) (L : Language) (rp : Polynomial ℕ)
    (x : List Bool) (T : ℕ) : Prop :=
  T ≤ IPM.runBound (prot.walkParams x) (prot.rounds x.length) ∧
    (∀ j ≤ T, ((IPM.step (prot.walkParams x))^[j]
      ⟨false, false, none, [IPM.freshFrm (prot.walkParams x) [] (polyRuler rp x)]⟩).done
        = false) ∧
    ((IPM.step (prot.walkParams x))^[T + 1]
      ⟨false, false, none, [IPM.freshFrm (prot.walkParams x) [] (polyRuler rp x)]⟩).done
        = true ∧
    ((((IPM.step (prot.walkParams x))^[T + 2]
      ⟨false, false, none, [IPM.freshFrm (prot.walkParams x) [] (polyRuler rp x)]⟩).done = true)
      ↔ x ∈ L)

section

open Classical

variable (prot : Protocol) {L : Language} (rp : Polynomial ℕ)
  (hrp : ∀ n, prot.rounds n = rp.eval n)
  (hcomp : ∀ y ∈ L, ∃ S : ProverStrategy, S.Bounded (prot.msgLen y.length) ∧
    2 / 3 ≤ eventProb (prot.acceptEvent S y))
  (hsound : ∀ y ∉ L, ∀ S : ProverStrategy, S.Bounded (prot.msgLen y.length) →
    eventProb (prot.acceptEvent S y) ≤ 1 / 3)

include hrp hcomp hsound in
theorem ipRun_exists (x : List Bool) : ∃ T, IPRunSpec prot L rp x T := by
  have hlvl : (polyRuler rp x).length = prot.rounds x.length := by
    rw [polyRuler_length, hrp]
  obtain ⟨T, hT, h1, h2, h3⟩ :=
    Protocol.walk_decides prot hcomp hsound x (polyRuler rp x) hlvl
  exact ⟨T, hT, h1, h2, h3⟩

end

/-- The number of steps the walk takes at `x`. -/
noncomputable def ipT (prot : Protocol) (L : Language) (rp : Polynomial ℕ)
    (hex : ∀ x : List Bool, ∃ T, IPRunSpec prot L rp x T) (x : List Bool) : ℕ :=
  Classical.choose (hex x)

theorem ipT_spec (prot : Protocol) (L : Language) (rp : Polynomial ℕ)
    (hex : ∀ x : List Bool, ∃ T, IPRunSpec prot L rp x T) (x : List Bool) :
    IPRunSpec prot L rp x (ipT prot L rp hex x) :=
  Classical.choose_spec (hex x)

/-! ## The containment -/

open Classical in
/-- **`IP ⊆ PSPACE`, for one protocol.** -/
theorem ip_mem_PSPACE (prot : Protocol) {L : Language} (rp cp mp r w : Polynomial ℕ)
    (hrp : ∀ n, prot.rounds n = rp.eval n) (hcp : ∀ n, prot.coins n = cp.eval n)
    (hmp : ∀ n, prot.msgLen n = mp.eval n)
    (hcomp : ∀ y ∈ L, ∃ S : ProverStrategy, S.Bounded (prot.msgLen y.length) ∧
      2 / 3 ≤ eventProb (prot.acceptEvent S y))
    (hsound : ∀ y ∉ L, ∀ S : ProverStrategy, S.Bounded (prot.msgLen y.length) →
      eventProb (prot.acceptEvent S y) ≤ 1 / 3)
    (hr : ∀ n, 2 * (2 * (cp.eval n + 1) + (rp.eval n + 1) *
        (2 * (2 * (rp.eval n + 1) + 2 * mp.eval n + 2 * (mp.eval n + cp.eval n)
          + 4 * (cp.eval n + 1) + (rp.eval n + 1) * (8 * (mp.eval n + cp.eval n) + 4) + 10)
        + 2) + 10) + 2 + n ≤ r.eval n)
    (hw : ∀ n, cp.eval n + 2 + (2 * mp.eval n + 3) * rp.eval n ≤ w.eval n) :
    L ∈ PSPACE := by
  classical
  obtain ⟨vd, hvdFP, hvd⟩ := exists_verdictFlag prot
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hfst : (fun z : List Bool => pairFst z) ∈ FP := Cobham.fstBlock_mem_FP
  have hsnd : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
  have hcr : (fun z => polyRuler cp (pairSnd z)) ∈ FP := polyRulerFn_mem_FP cp hsnd
  have hmr : (fun z => polyRuler mp (pairSnd z)) ∈ FP := polyRulerFn_mem_FP mp hsnd
  have hrr : (fun z => polyRuler rp (pairSnd z)) ∈ FP := polyRulerFn_mem_FP rp hsnd
  have hGfp : ipG prot vd rp cp mp ∈ FP := by
    refine Cobham.pairFn_mem_FP (Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hfst)
      (IPM.ipInitFn_mem_FP hcr hrr) ?_) hsnd
    exact IPM.ipStepFn_mem_FP hmr hcr hfst
      (fun hu hv => okFnFn_mem_FP prot.vmsg_mem hvdFP hrr hsnd hu hv)
  have hex := ipRun_exists prot rp hrp hcomp hsound
  have horb := ipG_iterate prot vd rp cp mp hcp hmp hvd
  have hN : ∀ x : List Bool, (fun y => ipT prot L rp hex y + 2) x = ipT prot L rp hex x + 2 :=
    fun _ => rfl
  refine SpaceIter.mem_PSPACE_of_iterate hGfp r w (fun x => ipT prot L rp hex x + 2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- lengths
    intro x i _
    have hbase := hr x.length
    have hM : IPM.msgW (prot.walkParams x) ≤ mp.eval x.length + cp.eval x.length := by
      show max (prot.msgLen x.length) (prot.coins x.length) ≤ _
      rw [hmp, hcp]
      omega
    cases i with
    | zero =>
        rw [Function.iterate_zero_apply, pair_length, List.length_nil]
        omega
    | succ j =>
        rw [horb x j, pair_length]
        have hlen := IPM.encSst_length_le (prot.walkParams x) ((polyRuler rp x).length + 1) _
          (IPM.iterate_encOk (prot.walkParams x) _ j _
            (IPM.encOk_start (prot.walkParams x) (polyRuler rp x)))
          (IPM.iterate_sizeOk (prot.walkParams x) j _
            (IPM.sizeOk_start (prot.walkParams x) (polyRuler rp x)))
        have hbound := IPM.stateBound_le (prot.walkParams x) ((polyRuler rp x).length + 1)
          (mp.eval x.length + cp.eval x.length) hM
        have ht : (prot.walkParams x).t = cp.eval x.length := by
          show prot.coins x.length = _
          rw [hcp]
        have hm : (prot.walkParams x).m = mp.eval x.length := by
          show prot.msgLen x.length = _
          rw [hmp]
        rw [ht, hm, polyRuler_length] at hbound
        rw [polyRuler_length] at hlen
        omega
  · intro x
    omega
  · -- the step count
    intro x
    obtain ⟨hT, _, _, _⟩ := ipT_spec prot L rp hex x
    have hle := IPM.runBound_le (prot.walkParams x) (prot.rounds x.length)
    have ht : (prot.walkParams x).t = cp.eval x.length := by
      show prot.coins x.length = _
      rw [hcp]
    have hm : (prot.walkParams x).m = mp.eval x.length := by
      show prot.msgLen x.length = _
      rw [hmp]
    rw [ht, hm, hrp] at hle
    rw [hrp] at hT
    have hmono : (2 : ℕ) ^ (cp.eval x.length + 2 + (2 * mp.eval x.length + 3) * rp.eval x.length)
        ≤ 2 ^ w.eval x.length := Nat.pow_le_pow_right (by omega) (hw x.length)
    omega
  · -- the flag stays down
    intro x i hi hlt
    obtain ⟨_, hdown, _, _⟩ := ipT_spec prot L rp hex x
    cases i with
    | zero => omega
    | succ j =>
        rw [horb x j, IPM.headD_pair_encSst]
        exact hdown j (by omega)
  · -- the flag goes up
    intro x
    obtain ⟨_, _, hup, _⟩ := ipT_spec prot L rp hex x
    erw [show ipT prot L rp hex x + 2 = (ipT prot L rp hex x + 1) + 1 from rfl,
      horb x (ipT prot L rp hex x + 1), IPM.headD_pair_encSst]
    exact hup
  · intro x
    erw [horb x (ipT prot L rp hex x + 2)]
    intro hc
    have := congrArg List.length hc
    rw [pair_length] at this
    simp at this
  · -- the answer
    intro x
    obtain ⟨_, _, _, hans⟩ := ipT_spec prot L rp hex x
    erw [horb x (ipT prot L rp hex x + 2), IPM.headD_pair_encSst]
    exact hans.symm

/-- The polynomial bounding the length of the state the walk carries. -/
noncomputable def ipStatePoly (rp cp mp : Polynomial ℕ) : Polynomial ℕ :=
  2 * (2 * (cp + 1) + (rp + 1) *
    (2 * (2 * (rp + 1) + 2 * mp + 2 * (mp + cp) + 4 * (cp + 1)
      + (rp + 1) * (8 * (mp + cp) + 4) + 10) + 2) + 10) + 2 + Polynomial.X

/-- The polynomial bounding the logarithm of the number of steps it takes. -/
noncomputable def ipCountPoly (rp cp mp : Polynomial ℕ) : Polynomial ℕ :=
  cp + 2 + (2 * mp + 3) * rp

theorem ipStatePoly_eval (rp cp mp : Polynomial ℕ) (n : ℕ) :
    (ipStatePoly rp cp mp).eval n
      = 2 * (2 * (cp.eval n + 1) + (rp.eval n + 1) *
        (2 * (2 * (rp.eval n + 1) + 2 * mp.eval n + 2 * (mp.eval n + cp.eval n)
          + 4 * (cp.eval n + 1) + (rp.eval n + 1) * (8 * (mp.eval n + cp.eval n) + 4) + 10)
        + 2) + 10) + 2 + n := by
  simp [ipStatePoly]

theorem ipCountPoly_eval (rp cp mp : Polynomial ℕ) (n : ℕ) :
    (ipCountPoly rp cp mp).eval n
      = cp.eval n + 2 + (2 * mp.eval n + 3) * rp.eval n := by
  simp [ipCountPoly]

/-- **`IP ⊆ PSPACE`.** The optimal prover's acceptance count is the value of a polynomially deep
game tree, and a stack machine walks that tree in polynomial space. -/
theorem IP_subset_PSPACE_internal : IP ⊆ PSPACE := by
  intro L hL
  obtain ⟨prot, rp, cp, mp, hrp, hcp, hmp, hcomp, hsound⟩ := hL
  exact ip_mem_PSPACE prot rp cp mp (ipStatePoly rp cp mp) (ipCountPoly rp cp mp)
    hrp hcp hmp hcomp hsound
    (fun n => le_of_eq (ipStatePoly_eval rp cp mp n).symm)
    (fun n => le_of_eq (ipCountPoly_eval rp cp mp n).symm)

end Complexity
