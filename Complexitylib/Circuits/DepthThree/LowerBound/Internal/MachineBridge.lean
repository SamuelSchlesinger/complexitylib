/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Machine.Defs
public import Complexitylib.Interop.Cslib.FromMultiTape

/-!
# Correctness of the finite-alphabet multitape simulator

The tape invariant uses coordinates relative to each work head. Initialization copies the
input to its symbol tracks, then rewinds those heads; simulation preserves all relative cells.
-/

@[expose] public section

namespace Complexity.DepthThreeLowerBound.FiniteMultiTapeBridge

lemma encode_injective {Γ : Type*} [Inhabited Γ] :
    Function.Injective (encode (Γ := Γ)) := SymbolTracks.encode_injective

lemma decode_encode {Γ : Type*} [Inhabited Γ] (a : Γ) : decode (encode a) = a :=
  SymbolTracks.decode_encode a

lemma encode_default {Γ : Type*} [Inhabited Γ] :
    encode (default : Γ) = fun _ => none := SymbolTracks.encode_default

lemma move_nth {Γ : Type*} [Inhabited Γ] (d : HeadMove) (t : Turing.Tape Γ) (z : ℤ) :
    (d.apply t).nth z = t.nth (z + (moveSign d : ℤ)) := by
  cases d <;> simp [HeadMove.apply, moveSign, sub_eq_add_neg]

/-- Relative tape contents agree and the simulator is running the source control. -/
structure Sim (M : FiniteMultiTapeMachine) {input : List Bool} (c : M.Cfg)
    (d : Turing.Cfg (Fintype.card (M.K × M.Γ)) Bool (Control M.Q) input) : Prop where
  /-- The controls correspond. -/
  state : d.state = some (.run c.q)
  /-- No output is emitted before source halting. -/
  output : d.output = []
  /-- Every track agrees at every offset from its head. -/
  tape : ∀ i z, d.workTapes i (d.workTapePos i + z) =
    encode ((c.tapes (trackEquiv M i).1).nth z) (trackEquiv M i).2

lemma Sim.read {M : FiniteMultiTapeMachine} {input : List Bool} {c : M.Cfg}
    {d : Turing.Cfg (Fintype.card (M.K × M.Γ)) Bool (Control M.Q) input}
    (h : Sim M c d) (k : M.K) :
    decode (fun a => d.workTapeSymbols (track M k a)) = (c.tapes k).head := by
  have he : (fun a => d.workTapeSymbols (track M k a)) = encode ((c.tapes k).head) := by
    funext a
    simpa [Turing.Cfg.workTapeSymbols, track] using h.tape (track M k a) 0
  rw [he, decode_encode]

lemma Sim.step {M : FiniteMultiTapeMachine} {input : List Bool} {c c' : M.Cfg}
    {d : Turing.Cfg (Fintype.card (M.K × M.Γ)) Bool (Control M.Q) input}
    (h : Sim M c d) (hs : M.step c = some c') :
    Sim M c' ((machine M).step d) := by
  have hread : (fun k => decode (fun a => d.workTapeSymbols (track M k a))) =
      (fun k => (c.tapes k).head) := funext h.read
  change (M.code c.q (fun k => (c.tapes k).head)).map
    (fun out => multiTapeUpdate c out.1 out.2.1 out.2.2) = some c' at hs
  cases hcode : M.code c.q (fun k => (c.tapes k).head) with
  | none => simp [hcode] at hs
  | some out =>
    rcases out with ⟨q, writes, moves⟩
    simp only [hcode, Option.map_some, Option.some.injEq] at hs
    subst c'
    have he : (machine M).step d =
        (Turing.Action.mk 0
          (fun i => (some (encode (writes (trackEquiv M i).1) (trackEquiv M i).2),
            moveSign (moves (trackEquiv M i).1))) none (some (.run q))).apply d := by
      rw [Turing.MultiTapeTM.step_apply_of_state h.state]
      simp only [machine, runAction, hread, hcode]
    rw [he]
    refine ⟨rfl, ?_, ?_⟩
    · simpa [Turing.Action.apply] using h.output
    · intro i z
      simp only [Turing.Action.apply, multiTapeUpdate, move_nth, Turing.Tape.write_nth]
      let δ : ℤ := moveSign (moves (trackEquiv M i).1)
      change Function.update (d.workTapes i) (d.workTapePos i)
        (encode (writes (trackEquiv M i).1) (trackEquiv M i).2)
        (d.workTapePos i + δ + z) =
        encode (if z + δ = 0 then writes (trackEquiv M i).1
          else (c.tapes (trackEquiv M i).1).nth (z + δ)) (trackEquiv M i).2
      by_cases hz : z + δ = 0
      · have hp : d.workTapePos i + δ + z = d.workTapePos i := by lia
        simp [hp, hz]
      · have hp : d.workTapePos i + δ + z ≠ d.workTapePos i := by lia
        rw [Function.update_of_ne hp, ite_eq_right hz]
        convert h.tape i (z + δ) using 1
        congr 1
        ring

lemma Sim.halt {M : FiniteMultiTapeMachine} {input : List Bool} {c : M.Cfg}
    {d : Turing.Cfg (Fintype.card (M.K × M.Γ)) Bool (Control M.Q) input}
    (h : Sim M c d) (hs : M.step c = none) :
    ((machine M).step d).state = none ∧ ((machine M).step d).output = [M.accept c.q] := by
  have hread : (fun k => decode (fun a => d.workTapeSymbols (track M k a))) =
      (fun k => (c.tapes k).head) := funext h.read
  have hcode : M.code c.q (fun k => (c.tapes k).head) = none := by
    simpa [FiniteMultiTapeMachine.step, multiTapeStep] using hs
  rw [Turing.MultiTapeTM.step_apply_of_state h.state]
  simp [machine, runAction, hread, hcode, idle, Turing.Action.apply, h.output]

lemma Sim.run {M : FiniteMultiTapeMachine} {input : List Bool} {c c' : M.Cfg}
    {d : Turing.Cfg (Fintype.card (M.K × M.Γ)) Bool (Control M.Q) input}
    (h : Sim M c d) (t : ℕ) (hs : runSteps M.step t (some c) = some c') :
    Sim M c' ((machine M).runFrom d t) := by
  induction t generalizing c' with
  | zero =>
    have hc : c = c' := Option.some.inj hs
    subst c'
    exact h
  | succ t ih =>
    have ht : runSteps M.step (t + 1) (some c) =
        (runSteps M.step t (some c)).bind M.step := by
      simp only [runSteps, Function.iterate_succ_apply']
    rw [ht] at hs
    cases hc : runSteps M.step t (some c) with
    | none => simp [hc] at hs
    | some q =>
      have hq : M.step q = some c' := by simpa only [hc, Option.bind_some] using hs
      simpa only [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply'] using
        (ih hc).step hq

lemma nth_mk₁ {Γ : Type*} [Inhabited Γ] (l : List Γ) (z : ℤ) :
    (Turing.Tape.mk₁ l).nth z = if z < 0 then default else l.getI z.toNat := by
  cases z with
  | ofNat n => simp [Turing.Tape.mk₁, Turing.Tape.mk₂]
  | negSucc n =>
    simp [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.nth, Turing.Tape.mk']

lemma nth_mk₁_nil {Γ : Type*} [Inhabited Γ] (z : ℤ) :
    (Turing.Tape.mk₁ ([] : List Γ)).nth z = default := by
  rw [nth_mk₁]
  simp

lemma nth_mk₁_append_singleton {Γ : Type*} [Inhabited Γ] (l : List Γ) (a : Γ) (z : ℤ) :
    (Turing.Tape.mk₁ (l ++ [a])).nth z =
      if z = l.length then a else (Turing.Tape.mk₁ l).nth z := by
  rw [nth_mk₁, nth_mk₁]
  by_cases hz : z < 0
  · have hne : z ≠ l.length := by lia
    simp [hz, hne]
  · simp only [hz, ite_false]
    by_cases hlt : z.toNat < l.length
    · have hne : z ≠ l.length := by lia
      rw [List.getI_append _ _ _ hlt, ite_eq_right hne]
    · have hle : l.length ≤ z.toNat := by lia
      rw [List.getI_append_right _ _ _ hle]
      by_cases he : z = l.length
      · subst z
        simp
      · have hpos : 1 ≤ z.toNat - l.length := by lia
        rw [List.getI_eq_default _ (by simpa using hpos),
          List.getI_eq_default _ hle, ite_eq_right he]

/-- The track contents after copying an input prefix. -/
noncomputable def inputContents (M : FiniteMultiTapeMachine) (bits : List Bool)
    (i : Track M) (z : ℤ) : Option Bool :=
  if (trackEquiv M i).1 = M.inputTape then
    encode ((Turing.Tape.mk₁ (bits.map M.inputSymbol)).nth z) (trackEquiv M i).2
  else none

lemma inputContents_nil (M : FiniteMultiTapeMachine) :
    inputContents M [] = fun _ _ => none := by
  funext i z
  simp [inputContents, nth_mk₁_nil, encode_default]

lemma inputContents_append (M : FiniteMultiTapeMachine) (bits : List Bool) (b : Bool)
    (i : Track M) :
    inputContents M (bits ++ [b]) i =
      if (trackEquiv M i).1 = M.inputTape then
        Function.update (inputContents M bits i) (bits.length : ℤ)
          (encode (M.inputSymbol b) (trackEquiv M i).2)
      else inputContents M bits i := by
  classical
  funext z
  by_cases hi : (trackEquiv M i).1 = M.inputTape
  · simp only [inputContents, hi, ite_true, List.map_append, List.map_singleton,
      nth_mk₁_append_singleton, List.length_map]
    by_cases hz : z = bits.length
    · subst z
      simp
    · simp [hz, inputContents, hi]
  · simp [inputContents, hi]

/-- The configuration after copying an input prefix of length `t`. -/
noncomputable def copyCfg (M : FiniteMultiTapeMachine) (w : List Bool)
    (t : ℕ) (ht : t ≤ w.length) :
    Turing.Cfg (Fintype.card (M.K × M.Γ)) Bool (Control M.Q) w where
  state := some .copy
  inputPos := ⟨t + 1, by lia⟩
  workTapes := inputContents M (w.take t)
  workTapePos := fun i => if (trackEquiv M i).1 = M.inputTape then t else 0
  output := []

/-- The configuration with `t` input cells left to rewind. -/
noncomputable def rewindCfg (M : FiniteMultiTapeMachine) (w : List Bool)
    (t : ℕ) (ht : t ≤ w.length) :
    Turing.Cfg (Fintype.card (M.K × M.Γ)) Bool (Control M.Q) w where
  state := some .rewind
  inputPos := ⟨t, by lia⟩
  workTapes := inputContents M w
  workTapePos := fun i => if (trackEquiv M i).1 = M.inputTape then t else 0
  output := []

lemma copyCfg_zero (M : FiniteMultiTapeMachine) (w : List Bool) :
    copyCfg M w 0 (by lia) = (machine M).initCfg w := by
  simp [copyCfg, Turing.MultiTapeTM.initCfg, Turing.Cfg.init, machine, inputContents_nil]

lemma copyCfg_step (M : FiniteMultiTapeMachine) (w : List Bool)
    (t : ℕ) (ht : t < w.length) :
    (machine M).step (copyCfg M w t ht.le) = copyCfg M w (t + 1) (by lia) := by
  have hin : (copyCfg M w t ht.le).inputSymbol = some w[t] :=
    Turing.inputSymbolInner t (by simp [copyCfg, Nat.add_comm]) ht
  have hpos : (copyCfg M w t ht.le).inputPos.val ≠ w.length + 1 := by simp [copyCfg]; lia
  have hw : w.take (t + 1) = w.take t ++ [w[t]] := (List.take_concat_get' w t ht).symm
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .copy) rfl]
  simp only [machine, hin]
  apply Turing.Cfg.ext
  · rfl
  · simpa [Turing.Action.apply, copyCfg] using
      Turing.moveInputPos_pos_of_ne_right (copyCfg M w t ht.le).inputPos hpos
  · funext i
    simp only [Turing.Action.apply, copyCfg, hw, inputContents_append]
    by_cases hi : (trackEquiv M i).1 = M.inputTape
    · simp [hi, List.length_take, min_eq_left ht.le]
    · simp [hi]
  · funext i
    by_cases hi : (trackEquiv M i).1 = M.inputTape <;>
      simp [Turing.Action.apply, copyCfg, hi, Nat.cast_add, Nat.cast_one]
  · rfl

lemma copyCfg_end (M : FiniteMultiTapeMachine) (w : List Bool) :
    (machine M).step (copyCfg M w w.length le_rfl) = rewindCfg M w w.length le_rfl := by
  have hin : (copyCfg M w w.length le_rfl).inputSymbol = none :=
    Turing.inputSymbol_eq_none_of_boundary (Or.inr rfl)
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .copy) rfl]
  simp only [machine, hin]
  apply Turing.Cfg.ext
  · rfl
  · have hp : (copyCfg M w w.length le_rfl).inputPos ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp [copyCfg] at this
    simpa [idle, Turing.Action.apply, copyCfg, rewindCfg] using
      Turing.moveInputPos_neg_of_ne_left (copyCfg M w w.length le_rfl).inputPos hp
  · simp [idle, Turing.Action.apply, copyCfg, rewindCfg]
  · funext i
    simp [idle, Turing.Action.apply, copyCfg, rewindCfg]
  · rfl

lemma rewindCfg_step (M : FiniteMultiTapeMachine) (w : List Bool)
    (t : ℕ) (ht : t + 1 ≤ w.length) :
    (machine M).step (rewindCfg M w (t + 1) ht) = rewindCfg M w t (by lia) := by
  have hin : (rewindCfg M w (t + 1) ht).inputSymbol = some (w[t]'(by lia)) :=
    Turing.inputSymbolInner t (by simp [rewindCfg, Nat.add_comm]) (by lia)
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .rewind) rfl]
  simp only [machine, hin]
  apply Turing.Cfg.ext
  · rfl
  · have hp : (rewindCfg M w (t + 1) ht).inputPos ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp [rewindCfg] at this
    simpa [Turing.Action.apply, rewindCfg] using
      Turing.moveInputPos_neg_of_ne_left (rewindCfg M w (t + 1) ht).inputPos hp
  · rfl
  · funext i
    by_cases hi : (trackEquiv M i).1 = M.inputTape <;>
      simp [Turing.Action.apply, rewindCfg, hi, Nat.cast_add, Nat.cast_one]
  · rfl

lemma runFrom_add (M : FiniteMultiTapeMachine) {w : List Bool}
    (d : Turing.Cfg (Fintype.card (M.K × M.Γ)) Bool (Control M.Q) w) (t u : ℕ) :
    (machine M).runFrom d (t + u) = (machine M).runFrom ((machine M).runFrom d t) u := by
  simp only [Turing.MultiTapeTM.runFrom, Nat.add_comm t u, Function.iterate_add_apply]

lemma runFrom_succ (M : FiniteMultiTapeMachine) {w : List Bool}
    (d : Turing.Cfg (Fintype.card (M.K × M.Γ)) Bool (Control M.Q) w) (t : ℕ) :
    (machine M).runFrom d (t + 1) = (machine M).step ((machine M).runFrom d t) :=
  Function.iterate_succ_apply' _ _ _

lemma run_copy (M : FiniteMultiTapeMachine) (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    (machine M).runFrom ((machine M).initCfg w) t = copyCfg M w t ht := by
  induction t with
  | zero => exact (copyCfg_zero M w).symm
  | succ t ih =>
    rw [runFrom_succ, ih (by lia), copyCfg_step M w t (by lia)]

lemma run_rewind (M : FiniteMultiTapeMachine) (w : List Bool) (t : ℕ)
    (ht : t ≤ w.length) :
    (machine M).runFrom (rewindCfg M w t ht) t = rewindCfg M w 0 (by lia) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (machine M).step^[t + 1] (rewindCfg M w (t + 1) ht) = _
    rw [Function.iterate_succ_apply, rewindCfg_step M w t ht]
    exact ih (by lia)

lemma rewindCfg_zero_sim (M : FiniteMultiTapeMachine) (w : List Bool) :
    Sim M (M.init w) ((machine M).step (rewindCfg M w 0 (by lia))) := by
  have hin : (rewindCfg M w 0 (by lia)).inputSymbol = none :=
    Turing.inputSymbol_eq_none_of_boundary (Or.inl rfl)
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .rewind) rfl]
  simp only [machine, hin]
  refine ⟨rfl, rfl, ?_⟩
  intro i z
  by_cases hi : (trackEquiv M i).1 = M.inputTape <;>
    simp [idle, Turing.Action.apply, rewindCfg, inputContents, FiniteMultiTapeMachine.init,
      hi, nth_mk₁_nil, encode_default]

lemma init_sim (M : FiniteMultiTapeMachine) (w : List Bool) :
    Sim M (M.init w) ((machine M).runFrom ((machine M).initCfg w) (2 * w.length + 2)) := by
  have htime : 2 * w.length + 2 = ((w.length + 1) + w.length) + 1 := by lia
  rw [htime, runFrom_succ, runFrom_add, runFrom_succ, run_copy M w w.length le_rfl,
    copyCfg_end, run_rewind]
  exact rewindCfg_zero_sim M w

lemma computes_proof (M : FiniteMultiTapeMachine) (w : List Bool) (b : Bool) (T : ℕ)
    (h : MultiTapeHaltsIn M w b T) :
    (machine M).ComputesInTimeAndSpace w [b] (2 * w.length + T + 3)
      ((machine M).spaceUsed ((machine M).initCfg w) (2 * w.length + T + 3)) := by
  obtain ⟨k, hk, c, hrun, hhalt, hout⟩ := h
  have hs := (init_sim M w).run k hrun
  rw [← runFrom_add] at hs
  have hh := hs.halt hhalt
  rw [← runFrom_succ] at hh
  have he : 2 * w.length + 2 + k + 1 = 2 * w.length + k + 3 := by lia
  rw [he, hout] at hh
  have heq := (machine M).runFrom_eq_of_halt ((machine M).initCfg w)
    (by lia : 2 * w.length + k + 3 ≤ 2 * w.length + T + 3) hh.1
  exact ⟨by rw [heq]; exact hh.1, by rw [heq]; exact hh.2, rfl⟩

lemma decidableInTimeAndSpace (M : FiniteMultiTapeMachine) (L : List Bool → Bool)
    (T : ℕ → ℕ) (h : ∀ w, MultiTapeHaltsIn M w (L w) (T w.length)) :
    Turing.MultiTapeTM.DecidableInTimeAndSpace {w | L w = true}
      (Function.Embedding.refl _) (fun w => 2 * w.length + T w.length + 3)
      (fun w => (machine M).spaceUsed ((machine M).initCfg w)
        (2 * w.length + T w.length + 3)) := by
  refine ⟨_, Control M.Q, inferInstance, machine M, ?_⟩
  intro w
  refine ⟨_, le_rfl, _, le_rfl, ?_⟩
  have he : Turing.MultiTapeTM.indicator {w | L w = true} w = L w := by
    simp [Turing.MultiTapeTM.indicator]
  simpa only [Function.Embedding.refl_apply, he, Function.Embedding.coeFn_mk] using
    computes_proof M w (L w) (T w.length) (h w)

end Complexity.DepthThreeLowerBound.FiniteMultiTapeBridge

namespace Complexity.DepthThreeLowerBound.FiniteMultiTapeMachine

lemma mem_P_proof {M : FiniteMultiTapeMachine} {L : List Bool → Bool} {p : Polynomial ℕ}
    (h : ∀ w, MultiTapeHaltsIn M w (L w) (p.eval w.length)) :
    {w | L w = true} ∈ Complexity.P := by
  have hd := FiniteMultiTapeBridge.decidableInTimeAndSpace M L p.eval h
  apply Complexity.mem_P_of_decidableInTimeAndSpace
    (p := Polynomial.C 2 * Polynomial.X + p + Polynomial.C 3)
  simpa using hd

end Complexity.DepthThreeLowerBound.FiniteMultiTapeMachine
