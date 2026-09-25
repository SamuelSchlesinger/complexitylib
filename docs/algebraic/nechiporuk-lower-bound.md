# Nechiporuk's bound for rectangle-free functions

`Algebraic.LowerBound.Nechiporuk` proves a superlinear formula lower bound
for the same rectangle-free functions that drive the
[cutwidth circuit bound](cutwidth-lower-bound.md): every formula over the
full binary basis computing such a function has `Ω(n² / log n)` leaves.

## The model

`Algebraic.Binary.Formula n` (in `Algebraic.Basis.Binary.Formula`) is a tree
whose leaves are input variables or constants and whose internal nodes apply
any of the sixteen binary Boolean functions. Its size is `leaves`, the number
of variable leaves. `leavesIn Y` counts the leaves whose variable lies in the
block `Y`.

## Statement

```lean
theorem eventually_sq_le_leaves (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n)) :
    ∀ᶠ n in atTop, ∀ F : Formula n, F.Computes (f n) →
      (n : ℝ) ^ 2 ≤ 64 * (c + 3) * Real.logb 2 n * F.leaves
```

The hypotheses are the same hard-family hypotheses as in the circuit bound.
No graph-theoretic hypothesis is needed. The exact finite version is
`leaves_lower_bound'`: with `8 K ≤ 2 ^ b`, every formula computing the
function satisfies `(n − b)(n − 2b − 1) ≤ 4 b · leaves`.

## The argument

The *subfunctions* of `f` on a block `Y` are the functions of the coordinates
in `Y` obtained by fixing the coordinates outside `Y`
(`Nechiporuk.subfunctions`).

**Rectangle-free functions have many subfunctions**
(`two_pow_card_compl_le`). Group the outside assignments by the subfunction
they induce. For each class, the product of the subfunction's accepting set
with the class is a one-rectangle, so either the subfunction accepts fewer
than `K` inputs or the class has fewer than `K` members. Counting the
accepting inputs of `f` class by class, the small-subfunction classes
contribute at most `K · 2^|Yᶜ|` and each remaining class at most `K · 2^|Y|`,
so once `2^|Y| ≥ 8 K` there are at least `2^|Yᶜ| / (8 K)` classes. Every
block of size about `log₂ K` therefore carries `2^(n − O(log n))` distinct
subfunctions, the maximum any function can have up to the polynomial factor.

**Formulas have few subfunctions** (`card_subfunctions_le`). Fixing the
coordinates outside `Y` turns every leaf outside `Y` into a constant, which
collapses the adjacent gate into one of the four unary functions of its other
input. Unary functions compose, so the count of subfunctions up to unary
post-composition satisfies a clean recursion: a leaf in `Y` gives four, a
gate one of whose sides has no leaf in `Y` inherits the other side's count,
and a gate with leaves on both sides multiplies the two counts by four. A
formula with `l` leaves in `Y` has at most `4^(2l − 1)` subfunctions up to
unary composition, hence at most `2 · 16^l` subfunctions.

**Summing over blocks** (`sum_le_of_computes`, `leaves_lower_bound`). Over
`n / b` disjoint blocks of size `b` with `2^b ≥ 8 K`, each block forces
`n − b ≤ log₂(16 K) + 4 · leavesIn`, and the block leaf counts add up to at
most the leaf size. With `b = O(log n)` this is `Ω(n² / log n)` leaves.

## Context

Nechiporuk's method is the classical route to `n² / log n` formula bounds,
and Andreev's function gives more (`n^(3 − o(1))`) by other means. The
point here is that rectangle-freeness makes a function Nechiporuk-maximal on
every block at once, rather than for one chosen partition, and that the same
hypothesis serves both the circuit and the formula bound. The method does
not extend to circuits, where the subfunction count on a block is only
bounded by an exponential in the whole circuit size.
