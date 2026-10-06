# Additive generation and the cost of an affine interface

Mirrored from the frontier-method research notes at `d81d97a`; Lean names are in the
namespace `Complexity.Frontier` (see the [frontier-method note](index.md)).

The unrestricted coefficient remains `L=4.5624976789...`. This note proves an
additive threshold lemma and gives a compiler for a circuit with an affine prefix
and an arbitrary nonlinear continuation. It also identifies the joint layout
bound still needed for five. The abstract threshold and finite-code interface are
checked in Lean; the compiler and its asymptotic consequences below are paper
proofs with independent finite checks, not end-to-end formal circuit theorems.

## Demand without coordinate read sites

Let `S` be a subset of a finite additive monoid. Say it is `K`-sumset-free when

```
A+B subset S  ==>  |A|<K or |B|<K.
```

This is the thin-set condition, not the usual definition of a sum-free set.
Every fiber of a sumset disperser has this property. A layered additive generator
labels its edges with monoid elements; the sum along each accepting path is in
`S`, and every element of `S` is generated. Labels may be dense vectors, and
different accepting paths may generate the same element. Size here counts edges,
including parallel edges with different labels. Multiple accepting states can be
joined to one sink with zero labels.

For `K>=2` and `|S|>=K`, a generator with `D` edges satisfies

```
|S| <= (K-1)^2 D.                                             (1)
```

Choose one accepting path for each element. At a state, every selected prefix
can be followed by every selected suffix through that state, so their sumset lies
in `S`. Follow the chosen path until its state's set of selected prefix sums first
has size at least `K`. Such a time exists: all initial prefixes are zero and the
final prefixes cover `S`. The preceding prefix set has size at most `K-1`, and
the new state's suffix set has size at most `K-1`. Charge to the intervening edge.
For a fixed edge of label `z`, an element charged there is reconstructed as
`p+z+q` from those two small sets. At most `(K-1)^2` elements charge to the edge.
This only uses reconstruction; injectivity of addition on arbitrary sets and
uniqueness of paths are unnecessary.

`Complexity.Frontier.AdditiveSweep.ncard_le` formalizes this argument for abstract additive
splicing data. `SumsetDisperser.sumsetFree` supplies the fiber property, and
`AdditiveSweep.transitionCount_le_codes` allows finite codes determining the
complete old-state/new-state/label transition. The direct sound program-to-sweep
construction above is a paper proof. No converse from arbitrary sweeps to sound
programs is asserted.

Consequently, if `|S|=2^(n-o(n))` and `log K=o(n)`, additive generation needs
`D>=2^(n-o(n))`, just as coordinate sweeps do. Sumset hardness permits a larger
class of representations than coordinate-rectangle hardness alone.

## Compile an affine prefix using one syndrome

Work over `F_2`. Suppose `ell` prefix gates compute

```
y = Lx+a in F_2^m,   rank L=r,   c=m-r,
```

and a suffix `h` with `t` binary gates uses the original input only through `y`.
Include any bypassed original inputs in `y`, and remove interface signals not
syntactically reachable from the suffix output. Put `s=ell+t`. Let `R` be a
full-row-rank `c`-by-`m` matrix with `ker R=im L`, and let `B:F_2^m -> F_2^n`
be a linear map with `LBv=v` for `v in im L`. Fix a basis of `ker L`.

Compile the suffix alone into its usual exact constraint network. Along any
layout, keep the edge frontier assignment and one partial syndrome

```
z = sum_{j already read} (R e_j) y_j.
```

When the unique input site for `y_j` reads a bit, update `z` by `(R e_j)y_j`
and emit the original-input vector `(B e_j)y_j`. All suffix gate equations and
the accepting output condition remain enforced. At the end require `z=Ra`,
emit the fixed label `Ba`, and append a sequence that independently includes or
omits each kernel basis vector. The generated elements are exactly

```
{ B(y+a)+u : h(y)=1, Ry=Ra, u in ker L }
    = { x : h(Lx+a)=1 }.                                      (2)
```

For the forward inclusion, `Ry=Ra` implies `y+a in im L`, so applying `L`
to the generated element gives `y+a`. Conversely, every `x` is
`B(Lx)+u` for some `u in ker L`; its suffix trace and those kernel choices
give an accepting path. Thus the construction retains the affine constraints
even for an arbitrary nonlinear continuation.

If the suffix layout has width `w`, the adjacent frontiers have union size at
most `w+3`. An old syndrome, that union's assignment, and at most one read bit
determine the entire transition and its emitted label. The new syndrome is
determined, not independently guessed. Therefore

```
D <= poly(n+s+m) 2^(w+c+O(1)) + O(n).                          (3)
```

There is no guessed tuple of special-gate outputs. This is why (3) pays one
syndrome rather than applying the existing aggregate-gate ledger estimate.
Dense vector labels require only polynomial description length.

## The exact communication state at each cut

We can improve (3) for a specified layout. If `P` is the set of interface
coordinates read so far and `F` its complement, retain only syndromes in

```
im R_P intersect (Ra + im R_F).
```

This slice is nonempty and has exactly `2^lambda(P)` elements, where

```
lambda(P) = rank R_P + rank R_F - c.                           (4)
```

It is a translate of `im R_P intersect im R_F`. Every accepting path already
satisfies this test, so imposing it at every layer preserves (2). The homogeneous
state count and completion equivalence are the existing checked
`LinearBoundary.ncard_syndromes` and `completions_eq_iff`; the affine translation
and this compiler instantiation are paper proofs.

Write `C_i` for the suffix edge frontier before step `i`, and `P_i` for the
interface inputs already read. The sharper transition bound is

```
D <= poly(n+s+m) 2^W + O(n),
W = max_i (|C_i union C_(i+1)| + lambda(P_i) + read_i),           (5)
```

where `read_i` is zero or one. For the fixed split linear equation, different
feasible syndromes have different right-completion sets; the syndrome state is
the exact communication interface. Nonlinear constraints may permit additional
compression, which is not assumed in (5).

Crucially, **the same order determines both terms**. A small suffix cutwidth
and a small code trellis width obtained in different orders cannot be added.

The [joint-code refinement](joint.md) improves (5) further: visible interface
values and the syndrome can contain the same information. Their combined rank
replaces their separate charges, with the code constraints still enforced.

## A quantitative architecture bound

Assume `s,m=O(n)` and the accepted set is dense and `K`-sumset-free with
`log K=o(n)`. The existing Gaussian layout theorem for the connected suffix
network gives `w<=A(t-m)+o(n)`, where

```
A=0.2807019372716472...,   L=1+1/A=4.562497678925021... .
```

Combining (1) and (3) gives

```
n <= A(t-m)+c+o(n),
s >= L n + ell - (n-r) - (L-2)c - o(n).                       (6)
```

The accepted set is invariant under `ker L`; hence its sum with that kernel
is still inside itself. If `|S|>=K`, thinness forces `|ker L|<K`, so
`n-r<log_2 K=o(n)`. The abstract stability implication is checked as
`SumsetFree.ncard_lt_of_stable`.

For a connected `D`-regular graph on the `n` inputs, take one prefix gate
`y_uv=x_u XOR x_v` for each edge. Then

```
ell=m=Dn/2,   r=n-1,   c=(D/2-1)n+1,
s >= [D + (2-D/2)/A] n - o(n).                               (7)
```

Thus a cycle prefix gives `5.562497...`, and a cubic prefix gives
`4.781248...`, even with an arbitrary nonlinear continuation. A quartic prefix
only gives `4` from this estimate, so the old universal bound is stronger there.
These are conditional bounds on circuit architectures computing an eligible
target. They neither improve the unrestricted coefficient nor assert that the
particular explicit extractor factors through these prefixes.

For a test that can represent an arbitrary target, include one original input
alongside the graph parities. This makes the interface full rank: edge parities
and the anchor determine every original input. It adds one interface signal,
no prefix gate, and leaves the leading constants in (7) unchanged. The joint-code
note uses this anchored version, avoiding dependence on a target's global-flip
symmetry.

For graphic prefixes, (4) has a useful combinatorial form. If `H_P,H_F` are the
two spanning subgraphs (including all isolated vertices), then

```
lambda(P) = n+1-components(H_P)-components(H_F)
          = c-beta1(H_P)-beta1(H_F).                           (8)
```

To see this, dual code connectivity gives
`lambda(P)=rank L_P+rank L_F-rank L`; incidence rank is `n-components`.
Equivalently, use `rank R_P=|P|-r+rank L_F`, which follows by counting
the codewords supported on `P`. Cycle rank on disconnected graphs is
`|E|-|V|+components`. Thus cycles completed entirely on either side save
communication states. A split with two forests earns no such saving.

## The next theorem to pursue

For the exact lower bound, keep the restriction potential `5d-s`: a selected
restriction deleting at least five gates does not decrease it. The
[restriction note](restrictions.md) proves that the hard target survives such
coordinate restrictions while its remaining dimension is linear. This avoids
requiring good progress in both branches merely to prove the exact bound.

The unresolved part is a **global restriction-or-terminal theorem**. After
profitable restrictions stop, find an affine interface and a common suffix
layout with

```
W <= (s-d)/4 + o(d),                                         (9)
```

or another sound additive generator of that cost. This would contradict (1)
below `(5-epsilon)d`. Setting the interface to the identity always recovers
the old method, but only with coefficient `A`, not `1/4`.

The first controlled test should be the cubic parity prefix with arbitrary
nonlinear continuation, including the anchor just described. At `s=5n`, its
suffix has `t-m=2n-O(1)`. Using the old
suffix bound, it is enough to arrange

```
lambda(P_i) <= (1-2A)n+o(n) = 0.438596125... n
```

at all steps in that same layout. Relative to the global `c=n/2+1` bound,
this asks for `0.061403874... n` saved bits, or an equivalent saving shared
between the two terms in (5). Equation (8) identifies exactly which cycles
give that saving. This sufficient simultaneous bound is **unproved**. The
quartic case needs a larger saving, and handling either family alone would
still not prove the global coverage theorem (9).

No weighted additive-peeling theorem is established here. In particular, the
coordinate average-case theorem does not automatically transfer through
possibly colliding additive representations. Prove the exact coefficient first;
an average-case extension would require its own compatible mass argument.

## Verification and sources

Run [syndrome_generator.py](data/syndrome_generator.py). It independently
compares generated original-input sets with exhaustive truth-table evaluation
for affine offsets, rank-deficient interfaces, arbitrary binary suffix gates,
sharing, and arbitrary non-topological layouts. The global syndrome, pruned
trellis, and joint-code versions are checked. Exhaustive edge bipartitions of two
small graphs check (8), including disconnected sides. A negative control with
`y=(x,x)` and suffix XOR produces false accepted inputs if the syndrome
constraint is dropped. These tests verify finite implementations, not (9).

The thin-sumset threshold technique has close antecedents in Gashkov's and
Gashkov--Sergeev's Minkowski-circuit lower bounds and Jukna's content-propagation
proof; see Jukna's author exposition and primary references [jukna-minkowski][jukna-minkowski].
Those results concern union/sumset circuits over `N^n`; (1) is the path-generator
version over finite additive monoids. No priority claim is made for the technique.

The exact syndrome-state interpretation is the standard code-trellis/matroid
connection discussed by Kashyap [kashyap08][kashyap08].
Chattopadhyay and Liao [chattopadhyay-liao23][chattopadhyay-liao23]
previously connect sumset extractors with hardness for strongly read-once linear
query branching programs. Our additive generator is a different model; their
query-program theorem is not being substituted for (1) or the compiler proof.
The adaptive-substitution framework is credited to Golovnev, Kulikov, Smal,
and Tamaki in the restriction note.

[chattopadhyay-liao23]: ../sources.md#chattopadhyay-liao23
[jukna-minkowski]: ../sources.md#jukna-minkowski
[kashyap08]: ../sources.md#kashyap08
