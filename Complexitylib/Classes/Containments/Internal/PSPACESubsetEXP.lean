/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.Exponential
public import Complexitylib.Classes.Containments.Internal.ConfigCount
public import Complexitylib.Classes.P.Cobham.Internal.Simulate

/-!
# `PSPACE ⊆ EXP` — proof internals

⚠️ Unreviewed by Bolton

A space-bounded machine has only exponentially many configurations, and a deterministic run
visits each at most once before halting, so its halting time is bounded by that count. The
machine is unchanged: only the time bound is new.

The counting needs one invariant the space predicate does not state. `Cfg.WithinDecisionSpace`
bounds head *positions*, not tape *contents*; but a head that never leaves `[0, S]` can never
write outside it, so every cell beyond the window still holds its initial blank. `Windowed`
records that, and `Windowed.step` propagates it.
-/

@[expose] public section

namespace Complexity

variable {k : ℕ} {tm : TM k}

/-- A step of a machine whose heads stay inside the window preserves the invariant. -/
theorem Windowed.step {x : List Bool} {S : ℕ} {c c' : Cfg k tm.Q}
    (hw : Windowed x S c) (hstep : tm.step c = some c')
    (hspace : c.WithinDecisionSpace x.length S) :
    Windowed x S c' := by
  rw [TM.step, ite_eq_right (TM.state_ne_qhalt_of_step hstep)] at hstep
  injection hstep with hstep
  subst hstep
  refine ⟨?_, ?_, ?_⟩
  · show (c.input.move _).cells = _
    cases (tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.1 <;>
      exact hw.input
  · intro i p hp
    have hhead : (c.work i).head ≤ S := hspace.1.1 i
    show ((c.work i).writeAndMove _ _).cells p = Γ.blank
    rw [cells_writeAndMove_of_ne _ _ _ (by omega)]
    exact hw.work i p hp
  · intro p hp
    have hhead : c.output.head ≤ S + 1 := hspace.2
    show (c.output.writeAndMove _ _).cells p = Γ.blank
    rw [cells_writeAndMove_of_ne _ _ _ (by omega)]
    exact hw.output p hp

namespace TM

/-! ## Counting the configurations inside the window -/

/-! ## A halting deterministic run is short

The deterministic iteration `TM.runCfg` and its algebra come from
`Complexitylib.Classes.P.Cobham.Internal.Simulate`, where the Cobham simulation already needed
them. -/

/-- Every configuration of a run is reachable. -/
theorem reaches_runCfg (tm : TM k) (c : Cfg k tm.Q) : ∀ n, tm.reaches c (TM.runCfg tm c n)
  | 0 => Relation.ReflTransGen.refl
  | n + 1 => by
      rw [TM.runCfg_succ]
      cases hs : tm.step (TM.runCfg tm c n) with
      | none => simpa using reaches_runCfg tm c n
      | some c' =>
          simp only [Option.getD_some]
          exact Relation.ReflTransGen.tail (reaches_runCfg tm c n) hs

/-- Once a configuration repeats, the run is periodic from that point on. -/
theorem runCfg_periodic (tm : TM k) (c₀ : Cfg k tm.Q) {i d : ℕ}
    (h : TM.runCfg tm c₀ i = TM.runCfg tm c₀ (i + d)) (r : ℕ) :
    TM.runCfg tm c₀ (i + r) = TM.runCfg tm c₀ (i + d + r) := by
  rw [TM.runCfg_add, TM.runCfg_add, h]

/-- A repeat before the first halt is impossible: periodicity would pull a halted
configuration back before time `t`. -/
theorem repeat_contradiction (tm : TM k) (c₀ : Cfg k tm.Q) {t : ℕ}
    (hmin : ∀ s, s < t → ¬ tm.halted (TM.runCfg tm c₀ s))
    (hhalt : tm.halted (TM.runCfg tm c₀ t)) {a b : ℕ} (hb : b ≤ t) (hlt : a < b)
    (hab : TM.runCfg tm c₀ a = TM.runCfg tm c₀ b) : False := by
  have hd : b = a + (b - a) := by omega
  have hper := runCfg_periodic tm c₀ (d := b - a) (by rw [← hd]; exact hab) (t - b)
  have h1 : a + (t - b) < t := by omega
  have h2 : a + (b - a) + (t - b) = t := by omega
  rw [h2] at hper
  exact hmin _ h1 (hper ▸ hhalt)

/-- Before the first halt, the configurations of a deterministic run are pairwise distinct. -/
theorem runCfg_injective_before_halt (tm : TM k) (c₀ : Cfg k tm.Q) {t : ℕ}
    (hmin : ∀ s, s < t → ¬ tm.halted (TM.runCfg tm c₀ s))
    (hhalt : tm.halted (TM.runCfg tm c₀ t)) :
    Function.Injective fun i : Fin (t + 1) => TM.runCfg tm c₀ i.val := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  by_contra hne
  have hne' : a.val ≠ b.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_ge a.val b.val with hlt | hge
  · exact repeat_contradiction tm c₀ hmin hhalt (by omega) hlt hab
  · exact repeat_contradiction tm c₀ hmin hhalt (by omega) (by omega) hab.symm

/-! ## From a space bound to a time bound -/

/-- Reachability gives a step count. -/
theorem exists_reachesIn {tm : TM k} {c c' : Cfg k tm.Q} (h : tm.reaches c c') :
    ∃ t, tm.reachesIn t c c' := by
  induction h with
  | refl => exact ⟨0, TM.reachesIn.zero⟩
  | tail _ hstep ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨t + 1, tm.reachesIn_snoc ht hstep⟩

/-- Before the first halt, the run is a genuine `reachesIn` run. -/
theorem reachesIn_runCfg (tm : TM k) (c : Cfg k tm.Q) :
    ∀ t, (∀ s, s < t → ¬ tm.halted (TM.runCfg tm c s)) → tm.reachesIn t c (TM.runCfg tm c t)
  | 0, _ => TM.reachesIn.zero
  | t + 1, hmin => by
      have hprev := reachesIn_runCfg tm c t fun s hs => hmin s (by omega)
      have hnh : ¬ tm.halted (TM.runCfg tm c t) := hmin t (by omega)
      rw [TM.runCfg_succ]
      cases hs : tm.step (TM.runCfg tm c t) with
      | none => exact absurd (TM.step_eq_none_iff_halted.mp hs) hnh
      | some c'' =>
          simp only [Option.getD_some]
          exact tm.reachesIn_snoc hprev hs

/-- Every configuration of a run from the initial configuration is windowed. -/
theorem windowed_runCfg {tm : TM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L f) (x : List Bool) :
    ∀ n, Windowed x (f x.length) (TM.runCfg tm (tm.initCfg x) n)
  | 0 => windowed_init tm.qstart x (f x.length)
  | n + 1 => by
      have hprev := windowed_runCfg hdec x n
      have hspace := hdec.1 x _ (reaches_runCfg tm (tm.initCfg x) n)
      rw [TM.runCfg_succ]
      cases hs : tm.step (TM.runCfg tm (tm.initCfg x) n) with
      | none => simpa using hprev
      | some c'' =>
          simp only [Option.getD_some]
          exact hprev.step hs hspace

/-- The exponential configuration bound of a space-`f` machine. -/
def spaceTimeBound (tm : TM k) (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Fintype.card tm.Q *
    ((n + f n + 2) * (((f n + 1) * 4 ^ (f n + 1)) ^ k * ((f n + 2) * 4 ^ (f n + 2))))

/-- **A space-bounded machine halts within its configuration count.** -/
theorem halt_time_le {tm : TM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L f) (x : List Bool) {t : ℕ}
    (hmin : ∀ s, s < t → ¬ tm.halted (TM.runCfg tm (tm.initCfg x) s))
    (hhalt : tm.halted (TM.runCfg tm (tm.initCfg x) t)) :
    t < spaceTimeBound tm f x.length := by
  have hinj : Function.Injective
      fun i : Fin (t + 1) =>
        cfgCode x.length (f x.length) (TM.runCfg tm (tm.initCfg x) i.val) := by
    intro a b hab
    refine runCfg_injective_before_halt tm (tm.initCfg x) hmin hhalt ?_
    exact cfgCode_inj (windowed_runCfg hdec x a.val)
      (hdec.1 x _ (reaches_runCfg tm (tm.initCfg x) a.val))
      (windowed_runCfg hdec x b.val)
      (hdec.1 x _ (reaches_runCfg tm (tm.initCfg x) b.val)) hab
  have hcard := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin, card_Code] at hcard
  exact hcard

/-- The configuration count is at most exponential in the space bound. -/
theorem spaceTimeBound_le_two_pow (tm : TM k) (f : ℕ → ℕ) (n : ℕ) :
    spaceTimeBound tm f n
      ≤ 2 ^ (Fintype.card tm.Q + (n + f n + 2) + 3 * k * (f n + 1) + 3 * (f n + 2)) := by
  have h : spaceTimeBound tm f n = Fintype.card (Code tm.Q k n (f n)) :=
    (card_Code tm.Q k n (f n)).symm
  rw [h]
  exact card_Code_le_two_pow tm.Q k n (f n)

/-- A polynomial dominating the exponent of the configuration count. -/
noncomputable def boundExp (tm : TM k) (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (Fintype.card tm.Q) + (Polynomial.X + p + Polynomial.C 2)
    + Polynomial.C (3 * k) * (p + 1) + Polynomial.C 3 * (p + Polynomial.C 2)

/-- The configuration count is at most `2` to a polynomial. -/
theorem spaceTimeBound_le_two_pow_poly (tm : TM k) (f : ℕ → ℕ) (p : Polynomial ℕ)
    (hf : ∀ n, f n ≤ p.eval n) (n : ℕ) :
    spaceTimeBound tm f n ≤ 2 ^ (boundExp tm p).eval n := by
  refine le_trans (spaceTimeBound_le_two_pow tm f n) (Nat.pow_le_pow_right (by norm_num) ?_)
  have h := hf n
  simp only [boundExp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (le_refl _) (by omega))
    (Nat.mul_le_mul_left _ (by omega))) (Nat.mul_le_mul_left _ (by omega))

/-! ## The time bound -/

open Classical in
/-- **A space-bounded decider is a time-bounded decider**, with no change of machine: the run
halts by the time it would have to repeat a configuration. -/
theorem decidesInTime_of_decidesInSpace {tm : TM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L f) : tm.DecidesInTime L (spaceTimeBound tm f) := by
  intro x
  obtain ⟨c', hreach, hhalted, hone, hzero⟩ := hdec.2 x
  obtain ⟨t₀, ht₀⟩ := exists_reachesIn hreach
  have hrun₀ : TM.runCfg tm (tm.initCfg x) t₀ = c' := TM.runCfg_of_reachesIn tm ht₀
  have hex : ∃ m, tm.halted (TM.runCfg tm (tm.initCfg x) m) := ⟨t₀, by rw [hrun₀]; exact hhalted⟩
  set t := Nat.find hex with hts
  have hhalt : tm.halted (TM.runCfg tm (tm.initCfg x) t) := Nat.find_spec hex
  have hmin : ∀ s, s < t → ¬ tm.halted (TM.runCfg tm (tm.initCfg x) s) :=
    fun s hs => Nat.find_min hex hs
  have hle : t ≤ t₀ := Nat.find_le (by rw [hrun₀]; exact hhalted)
  have hfreeze : TM.runCfg tm (tm.initCfg x) t = c' := by
    rw [← hrun₀, show t₀ = t + (t₀ - t) from by omega, TM.runCfg_add,
      TM.runCfg_of_halted tm hhalt]
  refine ⟨TM.runCfg tm (tm.initCfg x) t, t, (halt_time_le hdec x hmin hhalt).le, ?_, hhalt, ?_, ?_⟩
  · exact reachesIn_runCfg tm (tm.initCfg x) t hmin
  · rw [hfreeze]; exact hone
  · rw [hfreeze]; exact hzero

/-- A polynomial is eventually dominated by the next power. -/
theorem eval_le_pow_succ (q : Polynomial ℕ) :
    ∃ N, ∀ n, N ≤ n → q.eval n ≤ n ^ (q.natDegree + 1) := by
  refine ⟨max (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnS : (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i) ≤ n :=
    le_trans (le_max_left _ _) hn
  have h1 : q.eval n ≤ (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i) * n ^ q.natDegree := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ q.natDegree := by rw [Finset.mem_range] at hi; omega
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn1 hi')
  calc q.eval n ≤ (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i) * n ^ q.natDegree := h1
    _ ≤ n * n ^ q.natDegree := Nat.mul_le_mul_right _ hnS
    _ = n ^ (q.natDegree + 1) := by rw [pow_succ]; ring

/-- **The configuration count is exponential.** -/
theorem spaceTimeBound_bigO {tm : TM k} {f : ℕ → ℕ} {m : ℕ} (hf : f =O (· ^ m)) :
    ∃ j, spaceTimeBound tm f =O (fun n => 2 ^ n ^ j) := by
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hf
  obtain ⟨N, hN⟩ := eval_le_pow_succ (boundExp tm p)
  refine ⟨(boundExp tm p).natDegree + 1, ?_⟩
  rw [BigO]
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  simp only [Real.norm_natCast, one_mul]
  have h1 : spaceTimeBound tm f n ≤ 2 ^ (boundExp tm p).eval n :=
    spaceTimeBound_le_two_pow_poly tm f p hp n
  have h2 : (2 : ℕ) ^ (boundExp tm p).eval n ≤ 2 ^ n ^ ((boundExp tm p).natDegree + 1) :=
    Nat.pow_le_pow_right (by norm_num) (hN n hn)
  exact_mod_cast le_trans h1 h2

end TM

/-- **`PSPACE ⊆ EXP`.** A polynomial-space decider halts within its configuration count, which
is exponential, so the same machine is an exponential-time decider. -/
theorem PSPACE_subset_EXP_internal : PSPACE ⊆ EXP := by
  intro L hL
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hL
  obtain ⟨k, tm, f, hdec, hbig⟩ := hm
  obtain ⟨j, hO⟩ := TM.spaceTimeBound_bigO (tm := tm) hbig
  exact Set.mem_iUnion.mpr
    ⟨j, k, tm, TM.spaceTimeBound tm f, TM.decidesInTime_of_decidesInSpace hdec, hO⟩

end Complexity
