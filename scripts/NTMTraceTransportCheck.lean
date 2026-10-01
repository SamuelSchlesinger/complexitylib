/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Samuel’s dot
-/
module
public import Complexitylib.Models.TuringMachine.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Choice-preserving prefix transport regression examples

Run with `lake env lean scripts/NTMTraceTransportCheck.lean`.
Kernel-checked examples cover zero steps, both choices, a source that halts at the
endpoint, and a target that continues afterwards. Reversing the choice sequence
can introduce an early source halt and invalidate transport beyond that boundary.
-/

namespace Complexity
namespace NTMTraceTransportCheck

private abbrev source : NTM 0 where
  Q := Fin 3
  qstart := 0
  qhalt := 2
  δ := fun choice _ _ _ _ =>
    (if choice then 2 else 1, fun _ => Γw.blank, Γw.blank,
      .right, fun _ => .right, .right)
  δ_right_of_start := fun _ _ _ _ _ => ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

private abbrev target : NTM 0 where
  Q := Fin 4
  qstart := 0
  qhalt := 3
  δ := fun choice _ _ _ _ =>
    (if choice then 2 else 1, fun _ => Γw.blank, Γw.blank,
      .right, fun _ => .right, .right)
  δ_right_of_start := fun _ _ _ _ _ => ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

private def wrap (c : Cfg 0 (Fin 3)) : Cfg 0 (Fin 4) :=
  ⟨c.state.castSucc, c.input, c.work, c.output⟩

private theorem step (choice : Bool) (c : Cfg 0 source.Q)
    (running : c.state ≠ source.qhalt) :
    target.trace 1 (fun _ => choice) (wrap c) =
      wrap (source.trace 1 (fun _ => choice) c) := by
  cases c with
  | mk state input work output =>
      fin_cases state <;> cases choice <;> simp_all [source, target, wrap, NTM.trace]

-- Time zero imposes no running hypothesis, even on an already-halted source.
example (c : Cfg 0 source.Q) :
    target.trace 0 Fin.elim0 (wrap c) = wrap (source.trace 0 Fin.elim0 c) :=
  NTM.trace_map_prefix source target wrap step 0 Fin.elim0 c (by omega)

-- Each first-step choice is preserved, including true, which halts the source.
example (choice : Bool) :
    target.trace 1 (fun _ => choice) (wrap (source.initCfg [])) =
      wrap (source.trace 1 (fun _ => choice) (source.initCfg [])) := by
  apply NTM.trace_map_prefix source target wrap step
  intro t ht
  have : t = 0 := by omega
  subst t
  change (0 : Fin 3) ≠ 2
  decide

private def falseThenTrue (i : Fin 2) : Bool := i.val == 1

-- Both different choices are consumed in order; the source halts exactly at T = 2.
example : target.trace 2 falseThenTrue (wrap (source.initCfg [])) =
    wrap (source.trace 2 falseThenTrue (source.initCfg [])) := by
  apply NTM.trace_map_prefix source target wrap step
  intro t ht
  interval_cases t <;> simp [NTM.trace, source, falseThenTrue]

example : (source.trace 2 falseThenTrue (source.initCfg [])).state = source.qhalt := rfl

-- The target is allowed to continue after the source halts; it is not halt-reflecting.
example :
    (target.trace 1 (fun _ => false)
      (wrap (source.trace 2 falseThenTrue (source.initCfg [])))).state = 1 ∧
    (source.trace 1 (fun _ => false)
      (source.trace 2 falseThenTrue (source.initCfg []))).state = 2 := by
  exact ⟨rfl, rfl⟩

-- Reversing the choices causes an early halt, so the proper-prefix guard is essential.
private def trueThenFalse (i : Fin 2) : Bool := i.val == 0

example : (source.trace 1 (fun _ => trueThenFalse 0) (source.initCfg [])).state =
    source.qhalt := rfl

example : target.trace 2 trueThenFalse (wrap (source.initCfg [])) ≠
    wrap (source.trace 2 trueThenFalse (source.initCfg [])) := by
  intro heq
  have := congrArg Cfg.state heq
  change (1 : Fin 4) = 2 at this
  contradiction

end NTMTraceTransportCheck
end Complexity
