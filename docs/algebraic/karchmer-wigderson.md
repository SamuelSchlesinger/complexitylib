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

and projections prove the converse one-sided bounds: `formulaDepth g ≤
formulaDepth (compose f g)` when `f` is sensitive at some point, and
`formulaDepth f ≤ formulaDepth (compose f g)` when `g` is not constant.

## The conjecture

`KRWDepth s` states that for all `f` and `g`,

```lean
formulaDepth f + formulaDepth g ≤ formulaDepth (compose f g) + s m n
```

with an explicit slack `s`; `KRWSize c` is the multiplicative size form. The
conjecture, in any form with sublinear slack, is open. The known partial
results (composition with parity, with the universal relation, and with
lifted inner functions) are theorems about these objects and are natural
next targets for formalization.
