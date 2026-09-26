# Karchmer–Wigderson games and the KRW conjecture

`Algebraic.LowerBound.KarchmerWigderson` sets up the communication-game view
of De Morgan formula complexity and states the Karchmer–Raz–Wigderson
composition conjecture. Nothing here is a lower bound; it is the framework in
which the composition approach to superpolynomial formula lower bounds is
expressed, with the elementary facts around the conjecture proved.

## Formulas and protocols

`KW.Formula n` is a De Morgan formula: literal leaves `x_i` and `¬ x_i`,
constants, and binary AND and OR. Its `depth` is the longest root-to-leaf
path and `leaves` counts its leaves.

`KW.Protocol n` is a deterministic two-party protocol tree. Each internal node
belongs to Alice or Bob and branches on the owner's input; each leaf names a
coordinate. In the Karchmer–Wigderson game of `f`, Alice holds `x` with
`f x = 1`, Bob holds `y` with `f y = 0`, and a protocol solves the game
(`Protocol.SolvesKW`) when its output coordinate always separates `x` from
`y`.

## The Karchmer–Wigderson theorem

Formulas and protocols are the same trees. `Formula.toProtocol` turns an OR
gate into a node where Alice reports which side her input satisfies, an AND
gate into a node where Bob reports which side his input violates, and a
literal into a leaf naming its coordinate. `Protocol.toFormula` goes back:
each node of a protocol carries the rectangle of inputs consistent with the
transcript so far, and the formula with OR at Alice's nodes and AND at Bob's
nodes is `1` on Alice's side and `0` on Bob's side of every rectangle. Both
directions preserve depth and leaf count, so for `n ≥ 1`

```lean
formulaDepth f = protocolDepth f      -- formulaDepth_eq_protocolDepth
formulaSize f = protocolSize f        -- formulaSize_eq_protocolSize
```

where the four quantities are infima in `ℕ∞`. Every function has a formula
(`Formula.exists_computes`, by Shannon expansion), so formula depth is
finite.

## Composition

`compose f g` applies `f` to the values of `g` on `m` disjoint blocks of
`n` bits, with positions given by `finProdFinEquiv`. Substituting a formula
for `g` into one for `f` proves

```lean
formulaDepth (compose f g) ≤ formulaDepth f + formulaDepth g
formulaSize (compose f g) ≤ formulaSize f * formulaSize g
```

for all `f` and `g` (`formulaDepth_compose_le`, `formulaSize_compose_le`).
Projections prove one-sided bounds in the other direction:
`formulaDepth g ≤ formulaDepth (compose f g)` when `f` is not constant
(`formulaDepth_inner_le_compose_of_nonConstant`), and
`formulaDepth f ≤ formulaDepth (compose f g)` when `g` is not constant
(`formulaDepth_outer_le_compose_of_nonConstant`). Here `NonConstant f` means
that `f x ≠ f y` for some inputs `x` and `y`.

## The conjecture

The Karchmer–Raz–Wigderson conjecture says that for non-constant `f` and `g`
the upper bounds above are tight up to lower-order terms. The library states
its strong form, with a constant slack, and does not prove it.
`KRWDepthWith c` says that for all `m` and `n` and all non-constant
`f : Cslib.BooleanFunction m` and `g : Cslib.BooleanFunction n`,

```lean
formulaDepth f + formulaDepth g ≤ formulaDepth (compose f g) + c
```

and `KRWSizeWith c` says that for all such `f` and `g`,

```lean
formulaSize f * formulaSize g ≤ c * formulaSize (compose f g)
```

The slack `c` is a single natural number, independent of `m`, `n`, `f`, and
`g`, and the quantities are the `ℕ∞`-valued infima above. The conjectures
themselves are `KRWDepth := ∃ c, KRWDepthWith c` and
`KRWSize := ∃ c, KRWSizeWith c`. A larger slack gives a weaker statement
(`KRWDepthWith.mono`, `KRWSizeWith.mono`). Forms whose slack grows with `m` or
`n` are not formalized.

Both non-constancy hypotheses are necessary. If `f` or `g` is constant then
`f ⋄ g` is constant, of depth `0` and size `1`, while the conjunction of all
`k` bits has formula size at least `k` and depth at least `log₂ k`. So for
every `c`, the statement obtained from `KRWDepthWith c` or `KRWSizeWith c` by
dropping the non-constancy of `g` is false
(`not_forall_depth_of_constant_inner`, `not_forall_size_of_constant_inner`),
and so is the statement obtained by dropping the non-constancy of `f`
(`not_forall_depth_of_constant_outer`, `not_forall_size_of_constant_outer`).

The conjecture is open. The known partial results (composition with parity,
with the universal relation, and with lifted inner functions) are theorems
about these objects and are natural next targets for formalization.
