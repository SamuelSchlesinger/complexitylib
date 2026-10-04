# Branch decompositions: an exact compiler and its price

Status: bounded author pass, 2026-10-04. Two proposals; neither claims a new
unrestricted-circuit lower-bound coefficient. The deductions below have written
proofs and finite checks, not Lean proofs or independent mathematical review.
Novelty of the sharpened cardinality argument is **unverified**.

The baseline is full `B₂`, repeated input slots, unrestricted fanout, internal
gate count `s`, and the full input length `n`. The repository presently proves
`L₀ = 1 + 1/A₀ = 4.5624976789...`, with `A₀ = 0.2807019373...`.
Its family has `F = |f⁻¹(1)| ≥ 2^(n-2)` and every one-rectangle, under **every**
coordinate partition, has a side smaller than `K`, where `log₂ K = o(n)`.
These are the hypotheses used here; ordinary balanced-cut hardness is weaker.
The circuit compiler/counting baseline is credited in the [complexitylib26][complexitylib26]
to Ryan Williams's private working note and Samuel Schlesinger's counting note.

## Precursors and exact representation choices

Darwiche's DNNF work and compiler [darwiche02][darwiche02] predate this investigation.
Structured decomposability and its compilation role are developed by
Pipatsrisawat–Darwiche [pipatsrisawat08][pipatsrisawat08]. Bova–Capelli–Mengel–Slivovsky
[bova16][bova16], Theorems 1 and 6, connect DNNF gate certificates to rectangles
and balanced multi-partition covers. These are central precursors, not incidental
analogies. Their gate-context rectangle theorem is the starting point below.

Amarilli–Capelli–Monet–Senellart [amarilli20][amarilli20], Theorem 4.2, construct a
complete extended d-SDNNF from circuit treewidth `k`, in time
`O(|T| 2^((4+η)k))` for every fixed `η>0`, with width at most `2^(2(k+1))`.
That theorem does not supply an exponent-one compiler from ordinary treewidth.
Here the width counts *edge bits in a joint cut*, not vertices in a bag.
Markov–Shi [markov08][markov08], Proposition 4.2, relate contraction complexity to
treewidth of the line graph. Their scalar simulation theorem alone is not a
symbolic Boolean compiler and does not imply an OBDD size bound.

## Proposal 1: near-maximal hardness for unstructured DNNF

**Exact larger restricted model.** An NNF is a DAG with binary AND/OR nodes,
literal leaves, and constants. Every AND has children with disjoint *syntactic*
variable sets. OR nodes may overlap; there is no vtree, fixed variable order,
read-once path requirement, or restriction on DAG sharing. Size `S` counts all
nodes. A smooth NNF has equal child scopes at every OR. Its root is initially
required to mention all `n` variables; the overhead for removing this condition
and for smoothing is given below. Thus this covers all binary DNNFs, including
structured and deterministic subclasses, after the stated conversion.

**Target lemma, proved here as a deduction.** If a smooth `S`-node DNNF computes
a `K`-rectangle-free function, `K≥2`, and `F≥K`, then

```text
F ≤ E_OR (K-1)² + N_AND (K-1)³ ≤ 2 S (K-1)³.                 (1)
```

Here `E_OR` counts ordered parent-child incidences, including repeated slots;
`N_AND` counts AND nodes. The second inequality uses `E_OR+N_AND≤2S`.
This is a derivation from the known context-rectangle mechanism, not a claim
that (1) is new in the literature; our fresh search did not establish priority.

**Gate-context proof, including sharing.** For a gate `g`, let `X_g` be its
syntactic variable set and `A_g` its satisfying assignments on `X_g`.
Unfold a satisfied certificate: choose one child of each OR and both children
of each AND. Remove the occurrence of `g` and its descendants. All remaining
literal constraints concern the complement of `X_g`, by decomposability at
every AND on the path to the root. Let `B_g` be the union of the satisfying
outside assignments of all such contexts. Substituting **any** certificate of
`g` into **any** of these contexts proves `A_g × B_g ⊆ f⁻¹(1)`.
Moreover every full assignment having a certificate through `g` lies in this
product. These statements do not require OR determinism or unique certificates.
A nonempty-scope gate cannot occur twice in one certificate: its two paths
would separate at an AND and violate decomposability. Empty-scope gates have
`|A_g|≤1<K`; they will never be a large gate. DAG sharing across different
certificates is absorbed by the union defining `B_g`, without unfolding costs.
Consequently `|A_g|≥K` implies `|B_g|≤K-1` by rectangle-freeness.

**Charging proof.** For each accepted assignment, fix one satisfied certificate.
Start at the root, whose satisfying-set cardinality is at least `K`.
At a large OR `g`, follow its chosen child `h` if `|A_h|≥K`; otherwise stop and
charge the incidence `(g,h)`. Smoothness gives `X_g=X_h`, so that the assignments
charged to it lie in `A_h × B_g`, of size at most `(K-1)²`.
At a large AND `g`, descend to a child with cardinality at least `K`, if one
exists. Both children are satisfied, so this is permitted. If neither is large,
stop at `g`: its assignments lie in `A_left × A_right × B_g`, with three
disjoint scopes and size at most `(K-1)³`. A large leaf cannot occur because
a literal or constant has at most one satisfying assignment on its scope.
The DAG is acyclic, hence the descent terminates in one of the charged cases.
There are at most `E_OR+N_AND` keys; choosing certificates need not be efficient.
Summing bounds proves (1), with no balanced-partition assumption.

**Smoothing and skipped variables.** Given any binary `S`-node DNNF on a declared
set of `n` variables, create shared tautologies `τ_x=(x∨¬x)` using at most `3n`
new nodes. On every original OR incidence `g→h`, conjoin the missing
`τ_x`, for `x∈X_g\X_h`, using at most `n` new AND nodes on that incidence.
There are at most `2S` incidences. This preserves scopes at old nodes and
decomposability at all new ANDs; their added variables are mutually distinct
and absent from the child. Finally conjoin the at most `n` variables absent
from the root. The resulting smooth circuit has full root scope and

```text
S' ≤ (2n+1)S + 4n,
F ≤ 2((2n+1)S+4n)(K-1)³, provided F≥K.                       (2)
```

Thus the repository family needs `S≥2^(n-o(n))` in **arbitrary binary DNNF**.
For unbounded fanin, first binarize and charge incidences; do not count an
unbounded truth-table gate as one node. This is a precise restricted-model
consequence; it supplies no unrestricted `B₂` gate bound by itself.

**Smallest decisive check / stop.** Independently verify the context substitution
and smooth OR charging above, then formalize (1) before a graph extension.
A counterexample with valid decomposability and smoothness would kill this route.
An exponentially expensive conversion back to OBDD would not improve it.

## Proposal 2: compile a vertex partition tree, charging the actual joint cut

Take a loopless Boolean constraint multigraph with `N` vertices; parallel edges
are distinct bits. A vertex has a local check and at most one input-variable
owner. Every read variable has exactly one owner. Repeated uses are represented
by wires and equality/copy checks, not by new independent input leaves.
The repository's subcubic wiring network has these properties and `N≤2s+1`.

Let a rooted binary tree have these graph vertices as leaves. For its region
`U`, let `δU` denote crossing graph edges. Define carving width and joint width:

```text
b = max_U |δU|,
W = max_(U,V siblings) |δU ∪ δV|.
2|δU ∪ δV| = |δU| + |δV| + |δ(U∪V)|, so W ≤ floor(3b/2).    (3)
```

**The factor `3/2` is a real obstruction.** On the triangle with merge
`({0},{1})`, all three region boundaries have size `2`, but their joint bit set
has size `3`. Thus a table-width-`b` argument cannot silently use `2^b` merge
work. This example refutes that local accounting, not every possible compiler.
Neither ordinary treewidth nor graph branchwidth can replace `b` without an
explicit conversion; the present tree has *vertices*, not graph edges, as leaves.

**Exact Boolean compiler.** For every region `U` and boundary string `σ`, keep
a symbolic function `D[U,σ]` on the input variables owned in `U`: existence of
internal edge bits satisfying its checks and agreeing with `σ`.
At a leaf this function is `0`, `1`, `x`, or `¬x`; local-check rejection gives `0`.
At a merge `P=U∪V`, for each parent boundary `σ`, form

```text
D[P,σ] = OR_(τ on E(U,V))
           (D[U,(σ,τ)|δU] AND D[V,(σ,τ)|δV]).                (4)
```

Gluing witnesses proves (4) in both directions. Ownership makes each AND
decomposable; the partition tree fixes its structure. Discard zero terms;
simplify empty-scope constants. Every remaining state has its entire owned
scope, so OR is smooth. Suppress graph-tree leaves with no input owner to obtain
a vtree for the remaining variables; discarded constants do not add gates.
There is at most one AND per assignment to `δU∪δV`; binarizing each parent OR
uses fewer additional nodes than its number of terms. With shared literals
and constants, then tautologies for unread variables, this gives exactly

```text
S ≤ 2 Σ_(merges t) 2^w_t + 4n + 2 ≤ 2(N-1)2^W + 4n + 2.   (5)
```

The target is smooth structured DNNF for arbitrary constraint networks.
For **acyclic deterministic circuit wiring**, it is d-SDNNF: fixing incoming
boundary values and locally owned inputs determines every internal wire by
topological evaluation. Hence distinct `τ` in (4) have disjoint supports for
a fixed `σ`. Global uniqueness alone is not the justification; this regional
topological argument is. Existentially forgotten witness ports may destroy
determinism, but (1) still applies to the resulting DNNF. This is not an OBDD.

**Exact asymptotic target.** Write `e=(M-N)⁺` for wiring excess. A universal bound
`W≤(γ+η)e+C_η log₂(N+1)+D_η`, for every fixed `η>0`, together with (1) and (5),
would give `s>(1+1/γ-ε)n`. Indeed the existing support argument gives
`n'>n-ceil(log₂ K)`, and wiring has `M-N=s'-n'` with `s'≤s`.
Under a contrary linear bound on `s`, (5) yields
`n-2 ≤ W + O(log n + log K)`, contradicting the positive linear deficit.
The concrete target is therefore **`γ<A₀=0.2807019373...`**.

Via (3), a sufficient carving target is `b≤βe+O(log N)` with
`β<0.1871346248...`; the resulting coefficient is `1+2/(3β)`.
If a cubic core with `h≤2e` has carving width at most `(c+η)h+O(1)`, one needs
`c<0.0935673124...`. Restoring a compressed block by its existing prefix order
costs joint width at most its prefix boundary plus the next vertex's degree,
`3 ceil(log₂ N)+3`; attaching these trees at core leaves preserves core cuts.
Thus the coefficient loss is `γ=3c`, not `2c`. No universal bound meeting this
target is supplied here. Treewidth smaller than pathwidth is not enough.

**Falsifiers and stop conditions.** Optimize `W`, not just `b`, on candidate cubic
families, including expanders; a lower bound on minimum `W/h` at or above
`A₀/2` obstructs this graph-only transfer. Unbalanced tree cuts are allowed and
handled by the cardinality charging. Stop claiming a better coefficient until
a universal joint-width theorem with its restoration constants is proved.

## Tensor and semantic stress tests

Nonnegative *symbolic* arithmetic DAGs with binary `+` and `×`, unary leaves,
and disjoint variable scopes at products map to DNNF by taking positive support:
addition becomes OR, multiplication becomes AND. For `S_a` arithmetic nodes,
shared support leaves give at most `S_a+2n+2` Boolean nodes; apply (2) with that
size. This yields the same exponential bound for this precisely restricted
nonnegative decomposable model, including nonnegative weights and DAG reuse.
Arbitrary signed tensor contractions do not satisfy this support argument:
`x-x` vanishes, while OR of the two nonzero supports accepts `x=1`.
Evaluating a contracted scalar after fixing all inputs also supplies no symbolic
size bound. No rank-to-nonnegative-rank or tensor-to-OBDD conversion is assumed.

Dropping ownership is invalid: `x∧¬x` has zero satisfying assignments, whereas
independent leaf copies `x₁∧¬x₂` have one. Parity has small DNNFs and large
one-rectangles, so it fails the hard-family hypothesis rather than refuting (1).
A multiplexer also has a large rectangle: fix the selector and selected data
bit on one side, leaving many other data bits and controls freely varying.
The compiler accepts all 16 binary gate semantics; it never assumes monotonicity.

## Validation and limitations

Run `python3 research/circuit-lower-bound-frontiers/branch-decompositions/data/validate.py`.
The [script](data/validate.py) states its finite claim; [saved output](data/validation.json) records
seed `20261004`. It checks (3) on all 960 graph/tree pairs on four vertices,
including triangle saturation; (4) against independent edge-assignment
enumeration on 64 subcubic constraint networks and 288 circuit/tree cases using
all 16 binary truth tables, repeated slots, and shared signals. Arbitrary
networks exhibited 195 overlapping merge terms; deterministic circuits had none.
It checks contexts and 1,785 charged frontiers for 256 four-variable smooth
shared DNNFs, including parity and a multiplexer table. All assertions pass.
These are small checks of formulas and implementation, not asymptotic evidence.
The script does not implement or test smoothing; its overhead is proved above.
The primary sources below were freshly retrieved; no strongest-known or broad
breakthrough claim follows from this bounded search.

[amarilli20]: ../sources.md#amarilli20
[bova16]: ../sources.md#bova16
[complexitylib26]: ../sources.md#complexitylib26
[darwiche02]: ../sources.md#darwiche02
[markov08]: ../sources.md#markov08
[pipatsrisawat08]: ../sources.md#pipatsrisawat08
