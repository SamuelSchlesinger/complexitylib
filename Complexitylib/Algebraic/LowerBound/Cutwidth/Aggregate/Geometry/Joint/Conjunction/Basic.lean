/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Conjunction.Defs

/-!
# Normalizing conjunctions with two primary variables

An inconsistent literal set computes false. Every consistent literal set on
exactly two variables computes a signed edge, independently of literal order
and of repetitions in the circuit that supplied the set.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Entropy
variable {V : Type*} [DecidableEq V]

/-- Every variable in the literal set has a required Boolean value. -/
theorem mem_literalVars {L : Finset (V × Bool)} {v : V} :
    v ∈ literalVars L ↔ ∃ b, (v, b) ∈ L := by
  simp only [literalVars, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, mem, same⟩
    change a = v at same
    subst a
    exact ⟨b, mem⟩
  · rintro ⟨b, mem⟩
    exact ⟨(v, b), mem, rfl⟩

omit [DecidableEq V] in
/-- An inconsistent literal set has no satisfying assignment. -/
theorem evalLiterals_eq_false_of_not_consistent {L : Finset (V × Bool)}
    (bad : ¬ ConsistentLiterals L) : evalLiterals L = fun _ => false := by
  funext x
  apply Bool.eq_false_iff.mpr
  intro hx
  have holds := of_decide_eq_true hx
  apply bad
  intro a ha b hb same
  exact (holds a ha).symm.trans ((congrArg x same).trans (holds b hb))

/-- A consistent conjunction on exactly two variables is a signed two-variable edge. -/
theorem exists_signedEdge_of_card_eq_two {L : Finset (V × Bool)}
    (consistent : ConsistentLiterals L) (two : (literalVars L).card = 2) :
    ∃ e : SignedEdge V, e.eval = evalLiterals L := by
  obtain ⟨a, b, distinct, vars⟩ := Finset.card_eq_two.mp two
  obtain ⟨sa, ha⟩ := mem_literalVars.mp (show a ∈ literalVars L by simp [vars])
  obtain ⟨sb, hb⟩ := mem_literalVars.mp (show b ∈ literalVars L by simp [vars])
  refine ⟨⟨a, b, distinct, sa, sb⟩, ?_⟩
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [SignedEdge.eval, Bool.and_eq_true, beq_iff_eq, evalLiterals, decide_eq_true_eq]
  constructor
  · rintro ⟨xa, xb⟩ t ht
    have mem : t.1 ∈ literalVars L := Finset.mem_image.mpr ⟨t, ht, rfl⟩
    simp only [vars, Finset.mem_insert, Finset.mem_singleton] at mem
    rcases mem with same | same
    · exact (congrArg x same).trans (xa.trans (consistent (a, sa) ha t ht same.symm))
    · exact (congrArg x same).trans (xb.trans (consistent (b, sb) hb t ht same.symm))
  · intro holds
    exact ⟨holds (a, sa) ha, holds (b, sb) hb⟩

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
