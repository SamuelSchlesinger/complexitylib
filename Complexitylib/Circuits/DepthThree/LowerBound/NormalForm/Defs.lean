/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.NormalForm.Defs
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Core

/-!
# Canonical CNFs in the imported depth-three model

Literal polarity agrees in both models. Clause conversion removes duplicates, so it preserves
evaluation and does not increase width. An OR of CNFs is converted with an exact gate count.
-/

@[expose] public section

namespace Complexity.CNF

/-- Convert a canonical CNF to the imported set-of-literals representation. -/
def toDepthThree (F : CNF n) : DepthThreeLowerBound.CNF (Fin n) :=
  F.clauses.map fun C => (C.map fun l => (l.var, l.polarity)).toFinset

end Complexity.CNF

namespace Complexity.DepthThreeLowerBound.Circuit3

/-- A clause occurrence, indexed by its CNF and then its position. -/
abbrev BottomIndex (Fs : List (Complexity.CNF n)) :=
  Σ j : Fin Fs.length, Fin Fs[j].clauses.length

/-- Enumerate clause occurrences as numbered bottom gates. -/
noncomputable def bottomEquiv (Fs : List (Complexity.CNF n)) :
    Fin (Fintype.card (BottomIndex Fs)) ≃ BottomIndex Fs := (Fintype.equivFin _).symm

/-- Convert canonical literals to signed gate inputs. -/
def clauseInputs (C : List (Complexity.Literal n)) : RawClause (Fin n) :=
  C.map fun l => .inl (l.var, l.polarity)

/-- Realize an OR of canonical CNFs as an unrestricted three-layer circuit. -/
noncomputable def ofCNFs (Fs : List (Complexity.CNF n)) : Circuit3 (Fin n) where
  bottomCount := Fintype.card (BottomIndex Fs)
  middleCount := Fs.length
  bottom i := clauseInputs (Fs[(bottomEquiv Fs i).1].clauses[(bottomEquiv Fs i).2])
  middle j := Finset.univ.filter fun i => (bottomEquiv Fs i).1 = j
  top := Finset.univ

end Complexity.DepthThreeLowerBound.Circuit3
