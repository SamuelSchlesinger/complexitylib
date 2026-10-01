/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Witness.BoundSetup.Reserved
public import Complexitylib.Models.TuringMachine.Witness.Store
public import Complexitylib.Models.TuringMachine.Subroutines.PairBuild
public import Complexitylib.Models.TuringMachine.Combinators.ApplyDecide
public import Complexitylib.Models.TuringMachine.Placement.Hoare

/-!
# Ordinary finite verifiers compiled to witness machines

The compiler first realizes the witness bound on ordinary tapes, then stores
a finite certificate, builds a canonical pair, and runs the ordinary verifier.
Setup scratch and verifier scratch are separate blocks. Only the external
source stream is uncharged; the stored certificate and paired input are charged.
-/

@[expose] public section

namespace Complexity
namespace WitnessTM

/-- A deterministic phase that leaves the external source stream untouched. -/
def ofDeterministic (M : TM k) : WitnessTM k where
  machine := TM.liftLast M
  advancing := fun _ => false
  protocol := TM.guessProtocol_liftLast M

/-- Compose two witness phases with the standard one-step handoff. -/
def seq (A B : WitnessTM k) : WitnessTM k where
  machine := TM.seqTM A.machine B.machine
  advancing := TM.seqAdv A.advancing B.advancing
  protocol := TM.guessProtocol_seqTM A.protocol B.protocol

namespace Verifier

/-- Charged tape count: private setup block, verifier work, pair, and certificate. -/
abbrev tapes (r k : ℕ) := (r + 1) + (k + 2)

/-- The unary counter remains at the end of the setup's private block. -/
def counterIdx (r k : ℕ) : Fin (tapes r k) := Fin.castAdd (k + 2) (Fin.last r)

/-- The paired virtual input follows the verifier's own work tapes. -/
def pairIdx (r k : ℕ) : Fin (tapes r k) := (Fin.last ((r + 1) + k)).castSucc

/-- The stored finite certificate uses the final charged tape. -/
def witnessIdx (r k : ℕ) : Fin (tapes r k) := Fin.last ((r + 1) + (k + 1))

/-- The finite maximum accommodates time and space bounds without monotonicity. -/
def window (bound resource : ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range (bound n + 1)).sup (fun m => resource (2 * n + 2 + m))

/-- Exact phase-budget expression; all setup and handoff costs are included. -/
def time (setup : WitnessBoundSetup r bound) (T : ℕ → ℕ) (n : ℕ) : ℕ :=
  setup.time n + 1 + (NTM.guessBoundedTime (bound n) 0 + 1 +
    (TM.pairBuildTime n (bound n) + 1 + window bound T n))

/-- Conservative phase-space budget, including stored certificate, relocated
input, setup scratch, and output travel, but no verifier-time contribution. -/
def space (setup : WitnessBoundSetup r bound) (S : ℕ → ℕ) (n : ℕ) : ℕ :=
  max (max (setup.space n)
    (1 + NTM.guessBoundedTime (bound n) 0 + TM.pairBuildTime n (bound n)))
    (2 * n + 2 + bound n + window bound S n + 1)

/-- The bounded existential language of an ordinary paired-input verifier. -/
def language (bound : ℕ → ℕ) (L₀ : Language) : Language :=
  {x | ∃ y : List Bool, y.length ≤ bound x.length ∧ pair x y ∈ L₀}

/-- Once a certificate is stored, pair construction and verification are
ordinary deterministic phases with no further witness-stream access. -/
def suffix (r : ℕ) (M : TM k) : TM (tapes r k) :=
  TM.seqTM (TM.pairBuildTM (witnessIdx r k) (pairIdx r k))
    (TM.placeWorkTM (r + 1) 1 (TM.retargetInputStarted M))

/-- The only witness-consuming prefix: realize the numeric bound, then store
a finite certificate. Later verification can reread that charged copy freely. -/
def guessPrefix (setup : WitnessBoundSetup r bound) (k : ℕ) : WitnessTM (tapes r k) :=
  (ofDeterministic (setup.machine.liftTM (k + 2))).seq
    (storeBounded (witnessIdx r k) (counterIdx r k))

/-- The ordinary finite-verifier compiler. Every data-bearing intermediate tape
is charged; the sole free tape provides online choices for materialization. -/
def compile (setup : WitnessBoundSetup r bound) (M : TM k) : WitnessTM (tapes r k) :=
  (guessPrefix setup k).seq (ofDeterministic (suffix r M))

end Verifier
end WitnessTM
end Complexity
