# Jointly encode visible signals and affine syndromes

Mirrored from the frontier-method research notes at `d81d97a`; Lean names are in the
namespace `Complexity.Frontier` (see the [frontier-method note](index.md)).

The unrestricted coefficient remains `4.562497...`. This refines the
[additive compiler](additive.md), which generates original inputs while checking
an affine interface and an arbitrary nonlinear suffix. It removes an overcount:
visible interface values and the syndrome need not be independent information.

Lean checks the abstract subspace identity and dimension formula below as
`LinearBoundary.joint_eq` and `finrank_joint`. The code instantiation, graph
formula, and compiler are paper proofs with finite checks. They are not an
end-to-end formal circuit lower bound, and no universal quarter-coefficient
layout theorem is proved here.

## The joint code

Keep the notation `y=Lx+a`, `rank L=r`, and `ker R=im L`, with `R` of full row
rank `c=m-r`. At a transition let:

- `P` be the interface coordinates already read, and `F` their complement;
- `B` be the distinct circuit signals on the union of the two adjacent frontiers;
- `Q` be the interface coordinates whose signal is in `B`.

Every interface signal is used by the suffix. Consequently, if this transition
reads `y_j`, its signal belongs to the adjacent-frontier union, so `j in Q`.
There is no separate read-bit charge when these values are encoded.

The linear information needed by the transition is

```
(y_Q, z),    z=R_P y_P.
```

Over valid interface words `y in a+im L`, the exact number of such pairs is
`2^rho(P,Q)`, where

```
rho(P,Q) = rank L_(P union Q) + rank L_(F union Q) - r.          (1)
```

Offsets translate the set of pairs without changing its cardinality. In
particular, (1) is no larger than `|Q|+lambda(P)`, where
`lambda(P)=rank L_P+rank L_F-r` is the standalone syndrome dimension.
It can be strictly smaller even when the visible signals themselves are
independent: with `y=(x,x)`, `P=Q={0}`, the visible value and syndrome are the
same bit. The joint code has two states, whereas their product has four.

### Proof of the rank formula

Let `U` and `V` be the row spaces of `L_P` and `L_F`. The row space of
`R_P L_P` is exactly `U intersect V`. One containment follows from
`R_P L_P+R_F L_F=0`. Conversely, an equality between a row combination from
`L_P` and one from `L_F` gives a linear relation among all rows of `L`.
The rows of `R` span every such relation, since `ker R=im L`.

Write `U_Q=span L_(P intersect Q)` and `V_Q=span L_(F intersect Q)`.
The joint observation map therefore has row space

```
(U intersect V) + (U_Q+V_Q).
```

For subspaces `U_Q<=U` and `V_Q<=V`, modularity gives

```
(U intersect V) + (U_Q+V_Q)
    = (U+V_Q) intersect (V+U_Q).                              (2)
```

Explicitly, if `w=u+v_q=v+u_q` belongs to the right side, then
`w-u_q-v_q=u-u_q=v-v_q` belongs to `U intersect V`. The other containment
is immediate. Also `(U+V_Q)+(V+U_Q)=U+V`. The dimension formula for an
intersection now gives (1). Equations (2) and its dimension formula are the
precise Lean-checked statements; identifying the code's observation map with
these row spaces is the paper proof just given.

## A smaller transition budget

Modify the additive generator by requiring that all frontier copies of a signal
agree, and that `(y_Q,z)` belongs to the affine image in (1). These are necessary
conditions on every genuine accepting trace. They retain every valid path and
remove some paths that could never extend to a valid interface word. Feasibility
of a proposed pair can be tested by solving linear equations; the reference
checker uses enumeration only because its instances are small.

The other `|B|-|Q|` signal values, together with this joint code, determine the
old frontier and syndrome, the read value (if any), the new frontier and
syndrome, and the emitted original-input vector. Thus this layer has at most

```
2^(|B|-|Q|+rho(P,Q))                                         (3)
```

transitions. This bound retains every affine equation and every nonlinear suffix
gate equation. Summing over the polynomially many layers and appending the
constant translation and kernel choices gives total additive-generator size

```
D <= poly(n+s+m) 2^J + O(n),
J = max_i (|B_i|-|Q_i|+rho(P_i,Q_i)).                         (4)
```

The additive threshold theorem therefore forces `J>=n-o(n)` for a dense
sumset-free target with `log K=o(n)`. This sharpens the earlier sufficient
layout target: to reach five it would suffice to establish

```
J <= (s-n)/4+o(n)                                            (5)
```

after the profitable restrictions, uniformly for every residual circuit.
Equation (5) remains open. A smaller code for one layout does not prove that
all circuits admit a layout meeting (5).

## Graphic interpretation, with a full-rank interface

For a connected graph `H` on `n` inputs, first consider the interface consisting
of its edge parities. Put `c=|E(H)|-n+1`. Let `beta` denote cycle rank, counting
all components of a spanning subgraph, including isolated vertices. Incidence
rank is `n-components`, so (1) becomes

```
rho(P,Q) = c+|Q|-beta(H_(P union Q))-beta(H_(F union Q)).        (6)
```

Since `P,F` partition the edges, the two enlarged edge sets have total size
`|E(H)|+|Q|`; applying `rank=edges-beta` proves (6). Consequently the
joint transition exponent is

```
|B|+c-beta(H_(P union Q))-beta(H_(F union Q)).                 (7)
```

The earlier separate-syndrome bound only credited cycles entirely within `P`
or entirely within `F`. Formula (7) also credits cycles completed using the
visible edges `Q`. It accounts for their information once.

An unanchored edge-parity map loses the global input flip. To avoid a potentially
vacuous hard example, pass one original input `x_v` alongside all the parities.
Connectedness makes this interface injective. Its image is the edge-parity code
times a free anchor bit, so its parity-check matrix has a zero anchor column.
The anchor contributes one extra bit precisely when visible. Formula (7) still
holds, with `P,F,Q` restricted to graph edges inside the cycle-rank terms and
the anchor included among signals `B` when it crosses the transition.

For a cubic graph, this interface has `m=3n/2+1`, rank `n`, and `c=n/2+1`,
using `ell=3n/2` prefix gates. The global-syndrome estimate still gives the
restricted coefficient `4.781248...` up to an additive constant. At `s=5n`,
the earlier suffix-layout estimate leaves `0.061403874...n` bits to save.
Equation (7) enlarges the class of cycles that can provide this saving, but
no theorem yet supplies enough of them in a layout of an arbitrary suffix.

## What has been checked

[syndrome_generator.py](data/syndrome_generator.py) verifies:

- 24 coded circuits in 48 arbitrary layouts, with identical original-input
  supports in the global, pruned, and joint-state generators and direct circuit
  evaluation. The joint exponent improves the peak bound in 38 layouts relative
  to separated **distinct-signal** and syndrome charges. This comparison has
  already removed the repeated-wire and read-bit overcounts.
- 1,024 affine profiles, comparing enumerated joint states, the rank of the
  actual observation matrix, and (1).
- 320 graph edge partitions for standalone syndrome ranks, and 2,560 profiles
  with visible edges for (6).
- The one-bit overlap example, a full-rank anchored graphical interface with a
  nonlinear suffix, and a negative control showing false acceptances if the
  affine constraints are omitted.

The layouts are unoptimized and the circuits are tiny, sometimes redundant.
These checks establish no universal improvement in a circuit-size coefficient.

The shared-syndrome interpretation follows the standard code-trellis viewpoint;
see [kashyap08][kashyap08].
The joint-rank calculation is elementary linear algebra and modularity of
subspaces; no novelty claim is made. The additive-demand note separately credits
the Minkowski-circuit and sumset-extractor precedents.

[kashyap08]: ../sources.md#kashyap08
