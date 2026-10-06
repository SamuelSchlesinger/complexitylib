/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph
public import Mathlib.Tactic.DeriveFintype

/-!
# Comparator networks, ε-halvers, and their wire graphs

A comparator network on `n` wires with `s` comparators (`ComparatorNetwork n s`) applies its
comparators in the order `0, 1, …, s - 1`. Comparator `c` acts on two distinct wires
`minWire c` and `maxWire c`: it puts the smaller of their two values on `minWire c` and the larger
on `maxWire c`. The wires need not satisfy `minWire c < maxWire c`. The network acts on wire
values in any linear order (`ComparatorNetwork.eval`); on `{0, 1}`, encoded as `Bool` with
`false < true`, the minimum is `and` and the maximum is `or`.

The *bottom half* consists of the wires `w < ⌊n/2⌋` and the *top half* of the others. The network
is an *`ε`-halver* (`ComparatorNetwork.IsHalver`) when on every input `x ∈ {0, 1}ⁿ` with `k ≤ n/2`
ones, at most `ε k` ones end in the bottom half, and on every input with `k ≤ n/2` zeros, at most
`ε k` zeros end in the top half. For even `n` this is the `0`-`1` form of the ε-halvers of Ajtai,
Komlós and Szemerédi: among the `k ≤ n/2` largest inputs at most `ε k` end in the bottom half, and
among the `k` smallest at most `ε k` end in the top half.

The *wire graph* (`ComparatorNetwork.wireGraph`) is a directed multigraph. Its vertices
(`WireVertex`) are an input and an output terminal for every wire and, for every comparator `c`,
two vertices `gate c false` and `gate c true`, the ends of `c` on `minWire c` and on `maxWire c`.
Its edges (`WireEdge`) are the *wire segments*, which follow each wire from its input terminal
through the ends of the comparators acting on it, in order, to its output terminal, and for every
comparator a *link* from `gate c false` to `gate c true`. A wire segment is named after the vertex
it enters: `into c b` enters `gate c b` and `last w` enters the output terminal of `w`. It leaves
`lastStop w t`, the end on wire `w` of the last comparator before time `t` acting on `w`, or the
input terminal of `w` if there is none.
-/

@[expose] public section

namespace Algebraic.Cutwidth

/-- A comparator network on `n` wires with `s` comparators, applied in the order
`0, 1, …, s - 1`. Comparator `c` acts on the distinct wires `minWire c` and `maxWire c`. -/
structure ComparatorNetwork (n s : ℕ) where
  /-- The wire that receives the smaller value at comparator `c`. -/
  minWire : Fin s → Fin n
  /-- The wire that receives the larger value at comparator `c`. -/
  maxWire : Fin s → Fin n
  /-- The two wires of a comparator are distinct. -/
  minWire_ne_maxWire : ∀ c, minWire c ≠ maxWire c

/-- A vertex of the wire graph of a comparator network on `n` wires with `s` comparators. -/
inductive WireVertex (n s : ℕ) where
  /-- The input terminal of a wire. -/
  | input (w : Fin n)
  /-- The output terminal of a wire. -/
  | output (w : Fin n)
  /-- The end of comparator `c` on its `minWire` (`false`) or on its `maxWire` (`true`). -/
  | gate (c : Fin s) (b : Bool)
  deriving DecidableEq, Fintype

/-- An edge of the wire graph of a comparator network on `n` wires with `s` comparators. -/
inductive WireEdge (n s : ℕ) where
  /-- The last segment of wire `w`, which enters its output terminal. -/
  | last (w : Fin n)
  /-- The wire segment entering the end `gate c b` of comparator `c`. -/
  | into (c : Fin s) (b : Bool)
  /-- The link of comparator `c`, from its end on `minWire c` to its end on `maxWire c`. -/
  | link (c : Fin s)
  deriving DecidableEq, Fintype

namespace ComparatorNetwork

variable {n s : ℕ} (N : ComparatorNetwork n s)

/-- Apply comparator `c` to the wire values `x`: the smaller of the values on `minWire c` and
`maxWire c` goes to `minWire c`, the larger to `maxWire c`, and the other wires keep their
values. -/
def apply {α : Type*} [LinearOrder α] (c : Fin s) (x : Fin n → α) : Fin n → α := fun w =>
  if w = N.minWire c then min (x (N.minWire c)) (x (N.maxWire c))
  else if w = N.maxWire c then max (x (N.minWire c)) (x (N.maxWire c))
  else x w

/-- The wire values after the first `t` comparators, on input `x`. -/
def state {α : Type*} [LinearOrder α] (x : Fin n → α) : ℕ → Fin n → α
  | 0 => x
  | t + 1 => if h : t < s then N.apply ⟨t, h⟩ (state x t) else state x t

/-- The output of the network on input `x`: the wire values after all `s` comparators. -/
def eval {α : Type*} [LinearOrder α] (x : Fin n → α) : Fin n → α :=
  N.state x s

/-- `N` is an `ε`-halver. The bottom half is the wires `w < ⌊n/2⌋` and the top half the others.
On every input `x ∈ {0, 1}ⁿ` with `k ≤ n/2` ones (`true`), at most `ε k` ones end in the bottom
half; on every input with `k ≤ n/2` zeros (`false`), at most `ε k` zeros end in the top half. -/
def IsHalver (ε : ℝ) : Prop :=
  ∀ x : Fin n → Bool,
    ((Finset.univ.filter fun w => x w = true).card ≤ n / 2 →
      ((Finset.univ.filter fun w : Fin n => (w : ℕ) < n / 2 ∧ N.eval x w = true).card : ℝ) ≤
        ε * (Finset.univ.filter fun w => x w = true).card) ∧
    ((Finset.univ.filter fun w => x w = false).card ≤ n / 2 →
      ((Finset.univ.filter fun w : Fin n => n / 2 ≤ (w : ℕ) ∧ N.eval x w = false).card : ℝ) ≤
        ε * (Finset.univ.filter fun w => x w = false).card)

/-- The wire of the end of comparator `c` on side `b`: `minWire c` for `false`, `maxWire c` for
`true`. -/
def sideWire (c : Fin s) (b : Bool) : Fin n :=
  if b then N.maxWire c else N.minWire c

/-- The vertex of wire `w` last visited before time `t`: the end on `w` of the last comparator
`c < t` acting on `w`, or the input terminal of `w` if no comparator before time `t` acts on
it. -/
def lastStop (w : Fin n) (t : ℕ) : WireVertex n s :=
  if h : (Finset.univ.filter fun c : Fin s =>
      (c : ℕ) < t ∧ (N.minWire c = w ∨ N.maxWire c = w)).Nonempty then
    .gate ((Finset.univ.filter fun c : Fin s =>
      (c : ℕ) < t ∧ (N.minWire c = w ∨ N.maxWire c = w)).max' h)
      (decide (N.maxWire ((Finset.univ.filter fun c : Fin s =>
        (c : ℕ) < t ∧ (N.minWire c = w ∨ N.maxWire c = w)).max' h) = w))
  else .input w

/-- The wire graph of `N`. The segment `last w` runs from the last vertex of wire `w` to its
output terminal, the segment `into c b` from the previous vertex of wire `sideWire c b` to the
end `gate c b`, and the link of comparator `c` from `gate c false` to `gate c true`. -/
def wireGraph : Multigraph (WireVertex n s) (WireEdge n s) where
  fst
    | .last w => N.lastStop w s
    | .into c b => N.lastStop (N.sideWire c b) c
    | .link c => .gate c false
  snd
    | .last w => .output w
    | .into c b => .gate c b
    | .link c => .gate c true

end ComparatorNetwork

end Algebraic.Cutwidth
