/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Mixing
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Count
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Wiring.Graph

/-!
# Guess-independent erased graphs

Changing guessed output bits changes nullary constants but not slots, components,
or their primary inputs. Only original binary gates contribute incoming slots.
-/

@[expose] public section

namespace Algebraic.Aggregate

open Cutwidth.MultiOutput

variable {J : Type} {State : J → Type} {n g : ℕ}

/-- Transfer an erased closed component to another guess, retaining exactly its carrier. -/
def transportClosedSet (p : Program (signature State) n g) (a b : Guess p)
    (K : Internal.ClosedSet (erase p a)) : Internal.ClosedSet (erase p b) where
  carrier := K.carrier
  closed gate wire h := K.closed gate wire ((reads_erase_iff_reads_erase p b a gate wire).mp h)

theorem linked_erase_iff (p : Program (signature State) n g) (a b : Guess p)
    (u v : Wire n g) : Linked (erase p a) u v ↔ Linked (erase p b) u v := by
  simp only [Linked, reads_erase_iff]

theorem connected_transportClosedSet (p : Program (signature State) n g) (a b : Guess p)
    (K : Internal.ClosedSet (erase p a))
    (connected : ∀ u ∈ K.carrier, ∀ v ∈ K.carrier,
      Relation.ReflTransGen (Linked (erase p a)) u v) :
    ∀ u ∈ (transportClosedSet p a b K).carrier,
      ∀ v ∈ (transportClosedSet p a b K).carrier,
        Relation.ReflTransGen (Linked (erase p b)) u v := by
  intro u hu v hv
  exact Relation.ReflTransGen.mono
    (fun x y h => (linked_erase_iff p a b x y).mp h) u v (connected u hu v hv)

/-- Special nullary vertices are never charged as binary gate vertices. -/
theorem card_activeGates_le (p : Program (signature State) n g) (a : Guess p)
    (K : Internal.ClosedSet (erase p a)) :
    (Cutwidth.Aggregate.Wiring.activeGates K).card ≤ ordinaryCount p := by
  rw [← card_filter_ordinary p]
  apply Finset.card_le_card
  intro gate hgate
  simp only [Cutwidth.Aggregate.Wiring.activeGates, Finset.mem_filter] at hgate
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hpos := hgate.2
  change 0 < ordinarySignature.Arity ((erase p a).lines gate).op at hpos
  rw [arity_lines_erase] at hpos
  cases hs : (p.lines gate).op.isSpecial <;> simp_all

end Algebraic.Aggregate
