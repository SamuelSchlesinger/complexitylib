/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Internal.Network

/-!
# Cut counting for commutative aggregate networks

An aggregate network checks local Boolean wire constraints and an arbitrary predicate
of the product of its vertex contributions. The finite state space can be any
commutative monoid, including noncancellative operations such as AND, OR, and capped
counting. Every extra aggregate state multiplies the usual cut-counting bound once.

The proof charges the first large past set to the cut values and accumulator *before*
processing the vertex, together with its incident edge values. This outgoing key
determines the next aggregate even when multiplication cannot be inverted.
-/

@[expose] public section

namespace Algebraic.Cutwidth.AggregateNetwork

open Network

variable {n : Nat} {V E M : Type} [CommMonoid M] [Fintype V] [Fintype E] [Fintype M]
  (N : AggregateNetwork n V E M)

/-- Cut counting with one finite commutative aggregate. The first term accounts for
terminal aggregate states with small past sets; the second counts outgoing transitions. -/
theorem card_accepting_le [LinearOrder V] [Nonempty V]
    {f : Cslib.BooleanFunction n} (hf : N.Computes f) (hdeg : N.MaxDegreeLE 3)
    {w : Nat} (hw : ∀ v, (N.cut (below v)).card ≤ w)
    {K : Nat} (hK : 1 < K) (hrect : RectangleFree f K) :
    (accepting f).card ≤ Fintype.card M * (K - 1) * 2 ^ (n - N.read.card) +
      Fintype.card V * 2 ^ (w + 3) * Fintype.card M * (K - 1) ^ 2 :=
  Internal.card_accepting_le N hf hdeg hw hK hrect

/-- If every input has a port, one additional layer absorbs the terminal-state term. -/
theorem card_accepting_le_of_read_eq_univ [LinearOrder V] [Nonempty V]
    {f : Cslib.BooleanFunction n} (hf : N.Computes f) (hread : N.read = Finset.univ)
    (hdeg : N.MaxDegreeLE 3) {w : Nat} (hw : ∀ v, (N.cut (below v)).card ≤ w)
    {K : Nat} (hK : 1 < K) (hrect : RectangleFree f K) :
    (accepting f).card ≤ (Fintype.card V * 2 ^ (w + 3) + 1) *
      Fintype.card M * (K - 1) ^ 2 :=
  Internal.card_accepting_le_of_read_eq_univ N hf hread hdeg hw hK hrect

end Algebraic.Cutwidth.AggregateNetwork
