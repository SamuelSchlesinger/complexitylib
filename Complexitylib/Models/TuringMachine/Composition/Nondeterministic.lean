/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Composition.Defs
public import Complexitylib.Models.TuringMachine.Trace.DetPrefix

/-!
# Sequential composition before a nondeterministic machine

`NTM.compositionTM tmF N` runs the deterministic function computation `tmF`,
pipes its output to a fresh virtual-input tape, and then runs the
nondeterministic machine `N` on that virtual input.

The construction shares `TM.compositionTM`'s state skeleton: none of the
deterministic composition's states, start/halt markers, or tape layout
depend on the second machine's transition function, so branch `b` of the
composite can be *defined* as the deterministic composition with branch `b`
of `N`. The `det` projections then coincide with the deterministic
compositions definitionally (`compositionNTM_det`), which lets every
deterministic simulation lemma about `TM.compositionTM` be reused for the
composite's traces through `NTM.trace_of_det_prefix`.
-/


@[expose] public section

namespace Complexity

namespace NTM

variable {nf ng : ℕ}

/-- Sequential composition of a deterministic function computation with a
    nondeterministic machine. Branch `b` of the composite is the
    deterministic composition `TM.compositionTM tmF (N.det b)`; the state
    skeleton is branch-independent. -/
def compositionNTM (tmF : TM nf) (N : NTM ng) :
    NTM (TM.compositionTapeCount nf ng) where
  Q := (TM.compositionTM tmF (N.det false)).Q
  decEq := (TM.compositionTM tmF (N.det false)).decEq
  finQ := (TM.compositionTM tmF (N.det false)).finQ
  qstart := (TM.compositionTM tmF (N.det false)).qstart
  qhalt := (TM.compositionTM tmF (N.det false)).qhalt
  δ := fun b => (TM.compositionTM tmF (N.det b)).δ
  δ_right_of_start := fun b => (TM.compositionTM tmF (N.det b)).δ_right_of_start

/-- The `det` projections of the composite are exactly the deterministic
    compositions with the corresponding branch of `N`. -/
theorem compositionNTM_det (tmF : TM nf) (N : NTM ng) (b : Bool) :
    (compositionNTM tmF N).det b = TM.compositionTM tmF (N.det b) := rfl

/-- The composite and its branch compositions share initial
    configurations. -/
theorem compositionNTM_initCfg (tmF : TM nf) (N : NTM ng) (x : List Bool) :
    (compositionNTM tmF N).initCfg x =
      (TM.compositionTM tmF (N.det false)).initCfg x := rfl

/-! ### Branch agreement on the deterministic phases

The composite's two branches consult `N`'s transition functions only inside
the placed retargeted phase (the innermost `Sum.inr` block of the state
space). At every other state the transition is the same term for both
branches, so agreement holds definitionally once the state shape is fixed.
-/

section BranchAgreement

variable (tmF : TM nf) (N : NTM ng)
  {c : Cfg (TM.compositionTapeCount nf ng) (compositionNTM tmF N).Q}

private theorem branchesAgreeAt_of_state_eq
    {q : (compositionNTM tmF N).Q} (hq : c.state = q)
    (h : (compositionNTM tmF N).δ true q c.input.read
        (fun i => (c.work i).read) c.output.read =
      (compositionNTM tmF N).δ false q c.input.read
        (fun i => (c.work i).read) c.output.read) :
    (compositionNTM tmF N).BranchesAgreeAt c := by
  show (compositionNTM tmF N).δ true c.state c.input.read
      (fun i => (c.work i).read) c.output.read =
    (compositionNTM tmF N).δ false c.state c.input.read
      (fun i => (c.work i).read) c.output.read
  rw [hq]
  exact h

/-- Branch agreement at first-computation states. -/
theorem compositionNTM_branchesAgreeAt_first
    (q : (TM.compositionFirstTM tmF ng).Q) (hq : c.state = Sum.inl q) :
    (compositionNTM tmF N).BranchesAgreeAt c :=
  branchesAgreeAt_of_state_eq tmF N hq rfl

/-- Branch agreement at raw-output-rewind states. -/
theorem compositionNTM_branchesAgreeAt_rewindRaw
    (q : (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)).Q)
    (hq : c.state = Sum.inr (Sum.inl q)) :
    (compositionNTM tmF N).BranchesAgreeAt c :=
  branchesAgreeAt_of_state_eq tmF N hq rfl

/-- Branch agreement at copy states. -/
theorem compositionNTM_branchesAgreeAt_copy
    (q : (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
      (TM.compositionVirtualInputIdx nf ng)).Q)
    (hq : c.state = Sum.inr (Sum.inr (Sum.inl q))) :
    (compositionNTM tmF N).BranchesAgreeAt c :=
  branchesAgreeAt_of_state_eq tmF N hq rfl

/-- Branch agreement at live virtual-input-rewind states. The rewind
    phase's halt state is excluded: the seam out of it enters the placed
    retargeted phase at `N`'s post-first-transition state, which is the
    composite's first branch-dependent transition. -/
theorem compositionNTM_branchesAgreeAt_rewindVirtual
    (q : (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)).Q)
    (hne : q ≠ (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)).qhalt)
    (hq : c.state = Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))) :
    (compositionNTM tmF N).BranchesAgreeAt c := by
  refine branchesAgreeAt_of_state_eq tmF N hq ?_
  dsimp only [compositionNTM, TM.compositionTM, TM.compositionTailTM, TM.seqTM]
  rw [ite_eq_right hne, ite_eq_right hne]
  rfl

end BranchAgreement

end NTM

end Complexity
