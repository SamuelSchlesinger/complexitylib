/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeMultiProgram

/-!
# Unrestricted depth-three lower bound: tape multi routines

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeMultiRoutines.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7 uDepth8 uDepth9 uDepth10 uDepth11
universe uDepth12 uDepth13

namespace DepthThreeLowerBound

theorem runSteps_map_of_some {S : Type uDepth1} {T : Type uDepth2} {step : S → Option S}
    {next : T → Option T} (f : S → T)
    (hstep : ∀ a b, step a = some b → next (f a) = some (f b))
    {n : ℕ} {a b : S} (h : runSteps step n (some a) = some b) :
    runSteps next n (some (f a)) = some (f b) := by
  induction n generalizing a with
  | zero =>
      have hab : a = b := Option.some.inj h
      subst a
      rfl
  | succ n ih =>
      rw [runSteps_succ_left] at h ⊢
      cases he : step a with
      | none =>
          have hfalse : (none : Option S) = some b := by
            simpa only [Option.bind_some, he, runSteps_none] using h
          cases hfalse
      | some c =>
          have hc : runSteps step n (some c) = some b := by
            simpa only [Option.bind_some, he] using h
          simpa only [Option.bind_some, hstep a c he] using ih hc

theorem RunsIn.map {S : Type uDepth3} {T : Type uDepth4} {step : S → Option S} {next : T → Option T}
    (f : S → T)
    (hstep : ∀ a b, step a = some b → next (f a) = some (f b))
    {a b : S} {n : ℕ} (h : RunsIn step a b n) :
    RunsIn next (f a) (f b) n := by
  obtain ⟨k, hk, he⟩ := h
  exact ⟨k, hk, runSteps_map_of_some f hstep he⟩

namespace TapeMultiProgram

/-- Map a configuration's control state while retaining all of its tapes. -/
def mapCfg {Q : Type uDepth5} {R : Type uDepth6} (f : Q → R) (c : TapeMultiCfg Q) : TapeMultiCfg R
  :=
  ⟨f c.q, c.tapes⟩

theorem step_jump {Q : Type uDepth7} (P : TapeMultiProgram Q) (q q' : Q) (T : TapeTapes)
    (h : P q (heads T) = jump q' (heads T)) :
    P.step (cfg q T) = some (cfg q' T) := by
  have he := multiTapeStep_eq_some (c := cfg q T) (code := P) h
  simpa only [step, cfg, heads, jump, multiTapeUpdate, stayMoves,
    HeadMove.apply_stay, Turing.Tape.write_self] using he

theorem step_move {Q : Type uDepth8} (P : TapeMultiProgram Q) (q q' : Q)
    (T : TapeTapes) (r : TapeRegister) (d : HeadMove)
    (h : P q (heads T) = move r d q' (heads T)) :
    P.step (cfg q T) = some (cfg q' (Function.update T r (d.apply (T r)))) := by
  have he := multiTapeStep_eq_some (c := cfg q T) (code := P) h
  change P.step (cfg q T) = some (multiTapeUpdate (cfg q T) q'
    (heads T) (moveOnly r d)) at he
  rw [he]
  congr 1
  apply congrArg (cfg q')
  funext k
  by_cases hk : k = r
  · subst k
    simp [cfg, heads, moveOnly, Turing.Tape.write_self]
  · simp [cfg, heads, moveOnly, stayMoves, hk]

theorem step_writeMove {Q : Type uDepth9} (P : TapeMultiProgram Q) (q q' : Q)
    (T : TapeTapes) (r : TapeRegister) (symbol : TapeSymbol) (d : HeadMove)
    (h : P q (heads T) = writeMove r symbol d q' (heads T)) :
    P.step (cfg q T) =
      some (cfg q' (Function.update T r (d.apply ((T r).write symbol)))) := by
  have he := multiTapeStep_eq_some (c := cfg q T) (code := P) h
  change P.step (cfg q T) = some (multiTapeUpdate (cfg q T) q'
    (writeOnly r symbol (heads T)) (moveOnly r d)) at he
  rw [he]
  congr 1
  apply congrArg (cfg q')
  funext k
  by_cases hk : k = r
  · subst k
    simp [cfg, writeOnly, moveOnly]
  · simp [cfg, heads, writeOnly, moveOnly, stayMoves, hk]

theorem step_map {Q : Type uDepth10} {R : Type uDepth11} (P : TapeMultiProgram Q) (P' :
  TapeMultiProgram R)
    (f : Q → R)
    (hcode : ∀ q h q' writes moves,
      P q h = some (q', writes, moves) →
      P' (f q) h = some (f q', writes, moves))
    (a b : TapeMultiCfg Q) (h : P.step a = some b) :
    P'.step (mapCfg f a) = some (mapCfg f b) := by
  cases hp : P a.q (heads a.tapes) with
  | none =>
      have hn : P.step a = none := (multiTapeStep_eq_none_iff P a).2 hp
      have hfalse : (none : Option (TapeMultiCfg Q)) = some b := hn.symm.trans h
      cases hfalse
  | some out =>
      rcases out with ⟨q, writes, moves⟩
      have hb : b = multiTapeUpdate a q writes moves := by
        exact (Option.some.inj ((multiTapeStep_eq_some (c := a) (code := P) hp).symm.trans h)).symm
      subst b
      have he := multiTapeStep_eq_some (c := mapCfg f a) (code := P')
        (hcode a.q (heads a.tapes) q writes moves hp)
      simpa only [step, mapCfg, multiTapeUpdate, heads] using he

theorem runs_map {Q : Type uDepth12} {R : Type uDepth13} (P : TapeMultiProgram Q) (P' :
  TapeMultiProgram R)
    (f : Q → R)
    (hcode : ∀ q h q' writes moves,
      P q h = some (q', writes, moves) →
      P' (f q) h = some (f q', writes, moves))
    {a b : TapeMultiCfg Q} {n : ℕ} (h : RunsIn P.step a b n) :
    RunsIn P'.step (mapCfg f a) (mapCfg f b) n :=
  h.map (mapCfg f) (step_map P P' f hcode)

end TapeMultiProgram
end DepthThreeLowerBound

end Complexity
