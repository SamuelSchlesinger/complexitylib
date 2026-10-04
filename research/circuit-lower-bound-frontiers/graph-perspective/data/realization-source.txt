# Cubic kernels with critical supplied-circuit budgets

[Structural results](index.md) | [Research overview](../index.md)

This is a representation theorem. Every simple 2-vertex-connected cubic graph
occurs as the **exact retained kernel**, with zero cycle-rank loss, of a
normalized acyclic B2 verifier whose parameters are within an additive constant
of the critical balance. For triangle-free graphs the budget is exact whenever
the kernel cycle rank is divisible by three. All inputs are essential and the
projection is nonconstant. The displayed verifier is nevertheless nonminimal;
its minimum size and the projection's minimum size are computed below.

## The realization theorem

An orientation is *bipolar* here if it is acyclic and has exactly one source
and exactly one sink. Let K be a finite simple connected cubic graph supplied
with such an orientation, and put

    k = |V(K)|/2 + 1.

Choose

    t = floor(k/3) + 1,

or, if K is triangle-free, the sharper choice

    t = ceil(k/3).

There is a concretely specified AND-only B2 circuit on ordinary inputs
x_1,...,x_t and witnesses y_0,...,y_(t-1) with the following properties:

| Quantity | Exact value |
| --- | --- |
| Witness-independent gates p | 0 |
| Witness-dependent gates q | k + 2t - 1 |
| Distinct independent signals h | t |
| Used witnesses b | t |
| Dependent input pins ell | 2k + 3t - 2 |
| Initial consistency cycle rank kappa | k |
| Retained kernel | K, with its vertex and edge incidences unchanged |
| Cycle-rank loss in the reductions | 0 |

Every gate has two distinct input wires and uses AND as a genuinely binary
Boolean operation. The circuit has no constants, unary gates, unused inputs,
or gates outside its output cone. Thus constant propagation, deletion of
irrelevant formal pins, and pruning do not alter these counts. This is a
syntactic normal form; it does not forbid Boolean identities involving several
gates.

The verifier and its projection are exactly

    f(x,y) = (AND_i x_i) AND (AND_j y_j),
    g(x)   = AND_i x_i.

Consequently every input of f is essential, g is nonconstant, and

    C(f) = 2t - 1,       C(g) = t - 1.

In particular the supplied circuit exceeds its minimum size by exactly k
gates. Nothing here shows that a minimum circuit can be structurally critical,
or that the graph width obstructs a smaller circuit for the projection.

Since q+1=k+2t, the consistency budget h+b+kappa=q+1 is saturated. In every
case t=k/3+O(1), so q=5k/3+O(1) and h:b:kappa tends to 1:1:3 as k grows.
For a triangle-free K with k=3t the exact equalities are

    (p,q,h,b,ell,kappa) = (0, 5t-1, t, t, 9t-2, 3t).

## 1. A substantial graph class admits the required orientation

A Hamiltonian path gives an immediate bipolar orientation: order its vertices
along the path and orient every graph edge forward. Every internal vertex has
a preceding and a following path neighbor.

More generally, every 2-vertex-connected graph admits such an ordering. This
is the classical st-numbering property [even-tarjan-st][even-tarjan-st]. The
following existence argument makes this application self-contained. Start
with a cycle, designate adjacent vertices s,t, and order the remaining cycle
along the s-to-t path obtained by deleting the edge st. If not all vertices
have been included, a component of the graph outside the current vertex set
has neighbors at two distinct current vertices: a single attachment would
be a cut vertex of the original graph. A path through that component gives
an ear between distinct old vertices a,b, with all internal vertices new.
Assume a precedes b and insert the new vertices, in path order, immediately
after a. Each old internal vertex keeps a neighbor on each side, and each new
one has its preceding and following ear neighbors. Repeat until all vertices
are present, then orient every edge by the resulting total order. Only s is
a source and only t is a sink.

Thus the theorem covers every simple 2-vertex-connected cubic graph. For a
simple connected cubic graph, absence of bridges also suffices: a cut vertex
would separate its three incident edges among at least two components, one
of which has a single incident edge, making that edge a bridge. The theorem
also applies directly to graphs with bridges when a bipolar orientation is
supplied; it does not assert that all connected cubic graphs admit one.

## 2. Orient the kernel as a circuit skeleton

Write s and z for the source and sink. Every other vertex is either a *fork*,
with one incoming and two outgoing edges, or a *join*, with two incoming and
one outgoing edge. If F and J count these vertices, degree balance gives

    3 + F = J + 3,       F + J + 2 = 2(k-1),
    F = J = k - 2.

Place witness y_0 at s and copy its signal along the outgoing edges. A fork
copies its incoming signal. A join computes the AND of its two incoming
signals. At z use two AND gates to combine its three incoming signals.
All gates are ordered topologically. This skeleton has J+2=k gates.

Some skeleton joins may receive the same wire twice. We will repair those
joins before declaring the circuit normalized. For this purpose, temporarily
regard every join output as a distinct formal wire, even if its two inputs
coincide. Forks copy these wire names literally. A *conflict* is a join whose
two incoming formal wire names are equal. Let r count the conflicts.

The sink receives at least two different formal wire names. To prove this,
suppose all three incoming edges carried one name. Take a topologically last
join; one exists since k>=3. Every path from that join to the sink contains
only forks, so its output must be the common name. The fork tree rooted at
that join can have no outgoing edge to a different join, by its choice as
last. All its outgoing leaf edges therefore reach the sink. A last fork has
two outgoing edges to the sink, contradicting simplicity. If there are no
forks in this tree, the join has only one outgoing edge and cannot supply
the sink's three incoming edges. This proves the assertion.

We may therefore select two different sink input names for its first AND
gate. The second AND receives that new gate output and the remaining sink
input, which are again distinct wire names.

## 3. Bound and repair all repeated-input conflicts

The subgraph on the source and forks is a forest. Every fork has at most one
incoming edge in this subgraph, and an undirected cycle with an acyclic
orientation would have a vertex with two incoming edges. Its components are
exactly the trees along which one formal wire is copied. Besides the component
containing s, each such tree has a unique incoming edge from a join.

Consider a component not containing s, with m fork vertices. Its m-1 internal
edges and one incoming edge leave m+1 outgoing edges. Every conflict supplied
by this component uses two of them. If m=1 there is no conflict, since two
edges from the single fork to the same join would be parallel. For m>=2,

    r_component <= floor((m+1)/2) <= 2m/3.

The last inequality follows directly for m=2 and m=3; for m>=3 it also follows
from (m+1)/2<=2m/3. Distinct components supply disjoint sets of conflicts.

The source component, with m forks in addition to s, has m+3 outgoing edges.
For m=0 simplicity rules out any conflict. For m=1 it has at most two, and
for m=2 it has at most two. For m>=3 the outgoing-edge count gives

    r_source <= floor((m+3)/2) <= 2m/3 + 4/3.

The same final bound covers m=0,1,2. Summing over all F=k-2 forks proves

    r <= floor(2k/3).

For a triangle-free graph, the m=1 source component has no conflict: such a
conflict would make a triangle through its source, fork, and target join.
Now the sharper source bound r_source<=2m/3+1 holds: check m=0,1,2 directly,
and use (m+3)/2<=2m/3+1 for m>=3. Consequently

    r <= floor((2k-1)/3)                 [triangle-free case].

There are 2t-1 new inputs available, namely t ordinary inputs and t-1 new
witnesses. In the general case 2t-1>=floor(2k/3), and in the triangle-free
case 2t-1>=floor((2k-1)/3). For each conflict, choose one of its incoming
edges and insert a gate

    new_value = old_value AND fresh_input,

using a different available input at each insertion. Place any remaining
available inputs on any one original edge, with one such gate per input
in a serial chain. The resulting gate output names are fresh. Splitting
a copied wire into fresh names cannot identify two previously distinct
names, so every original conflict is repaired and no new one is created.
This includes the two distinct sink names chosen above.

Every attachment receives a witness-dependent old value. Thus all gates are
dependent, every ordinary input appears at exactly one gate pin, and each
gate has two distinct input wires. The graph orientation and attachment
chains give an explicit topological gate list.

## 4. Exact circuit and input accounting

There are k skeleton gates and 2t-1 attachment gates, giving q=k+2t-1.
All witnesses and ordinary inputs reach the output, so b=h=t and p=0.
Every gate has two pins and exactly t pins carry independent inputs. Hence

    ell = 2q - t = 2k + 3t - 2,
    kappa = ell - q - b + 1 = k.

All operations are AND and every input is an ancestor of the output. By
topological induction, each wire is the conjunction of the input variables
in its ancestor set; the output therefore equals the displayed f. Setting
all other inputs to one proves that each input is essential. Existentially
setting all witnesses to one gives the displayed g.

A binary circuit depending on d essential inputs needs at least d-1 gates:
its connected output cone has at least s+d-1 edges and at most 2s input
pins. AND chains meet this lower bound for f and g, proving the stated
minimum sizes. In particular, all-input essentiality excludes unused-input
padding but does not exclude redundant shared computation. The supplied
circuits contain exactly the k extra gates quantified above.

## 5. A legal tensor reduction retains precisely K

Start with the manuscript's actual incidence graph: a defining constraint
for every gate, a consistency equality for every witness and gate output,
and the output-one constraint. Ordinary inputs remain coefficients.

Choose the equality splitting as follows. A copied signal with m forks
after its defining gate has m+1 uses and one defining incidence, so its
equality has degree m+2. When m>=1, replace it by precisely its m fork
vertices and their tree edges. This is a permitted tree of degree-three
equalities, with the original incidences at its external ports. When m=0,
its degree-two equality is kept. For the source signal, a tree containing
s and m forks has m+3 uses; its equality splits into precisely m+1 ternary
vertices. Attachments split these trees into smaller copied-signal trees,
and the same count applies to each piece. Every fresh witness used by one
attachment contributes a degree-one equality.

This description can equivalently be checked in reverse: contract each
tree of equality vertices. Its external incidences are exactly the uses
and defining incidence of one actual circuit wire. An equality tree with
D external ports has D-2 ternary vertices, so it is exactly one of the
splittings allowed in the manuscript. A gate-to-gate wire with no fork has
one degree-two equality on it.

Perform the following reductions, retaining their actual Boolean tables.

1. Contract the output-one assertion through the output equality into the
   second sink AND gate. That gate now has two remaining ports. Contract
   the degree-two equality between the sink AND gates and then this
   degree-two constraint into the first sink AND gate. The surviving
   three-port table is the conjunction of the three original incoming
   bits, and is assigned to vertex z.
2. For every new witness, contract its degree-one equality into its attachment
   gate constraint. The resulting constraint has degree two. Its value is
   the OR over the witness value of the gate relation.
3. Every ordinary-input attachment already has a degree-two constraint,
   because its ordinary input is a coefficient rather than an index.
   Contract all these degree-two constraints and their degree-two wire
   equalities along their original kernel edges. This restores each such
   edge topologically. The updated neighboring tables retain the semantic
   effect of the attachments.
4. Contract every remaining degree-two wire equality along its edge.

Every operation is a degree-one or degree-two contraction from the
manuscript. Before and during these operations the graph is obtained from
K by subdividing edges, expanding the sink into a tree, and attaching the
specified leaf trees. With the chosen equality splitting there is never
a need for a loop reduction or parallel-edge contraction. A single-edge
contraction preserves cycle rank, so the loss is exactly zero. The surviving
marked vertices are s, every fork and join, and the first sink gate; their
incidences are exactly those of K. Since K is already simple and cubic,
the manuscript reductions terminate there. All updated tensors have rank
at most three and incur only the manuscript's linear reduction cost.

The assertion concerns the existence of this legal sequence and equality
splitting. Other choices can produce a different retained graph. Semantic
simplification of the resulting tensor entries can also reveal the easy
projection, which is consistent with C(g)=t-1.

## Finite implementation check

The [realization checker](data/check_realization.py) constructs actual gate
lists, verifies the conflict bound and all parameter counts, identifies the
split equality trees with the circuit's incidence graph, and executes a
legal sequence of contractions ending at the labeled target K. The proof
above, rather than finite sampling, establishes the general theorem.

The graph family consists of every perfect matching disjoint from a fixed
Hamiltonian cycle at orders 4,6,8,10,12; 21 lengths of each of two explicit
families of cubic block chains joined by bridges; and 32 seeded random
2-vertex-connected cubic graphs whose orientations are built by ear insertion.
The triangle-containing chains use copies of K4 with an edge removed, with
terminal caps obtained by subdividing an edge of K4. The triangle-free chains
use the corresponding constructions from K_(3,3). All graph-generation and
orientation checks are implemented with the Python standard library. Seven
small representatives additionally undergo full verifier truth-table checks
and symbolic existential compilation using the existing tensor checker.

Command, run from the project root:

```text
python3 research/structural/data/check_realization.py
```

Retained output:

```text
Hamiltonian-cycle plus matching graphs, n=4: 1 OK
Hamiltonian-cycle plus matching graphs, n=6: 4 OK
Hamiltonian-cycle plus matching graphs, n=8: 31 OK
Hamiltonian-cycle plus matching graphs, n=10: 293 OK
Hamiltonian-cycle plus matching graphs, n=12: 3326 OK
Bridged triangle block chains: 21 OK
Bridged triangle-free block chains: 21 OK
Seeded 2-connected cubic graphs with ear orders, n=14: 8 OK
Seeded 2-connected cubic graphs with ear orders, n=20: 8 OK
Seeded 2-connected cubic graphs with ear orders, n=30: 8 OK
Seeded 2-connected cubic graphs with ear orders, n=60: 8 OK
Triangle-free Hamiltonian cases: 913 OK
Exact critical Hamiltonian cases (k divisible by 3): 68 OK
Exhaustive verifier truth tables and symbolic projection checks: 7 OK
Legal degree-one/two contractions: 72401 OK
Exact labeled kernels and zero cycle loss: 3729 OK
```

Priority for this joint realization and budget statement is unestablished
beyond the source comparison recorded here. The orientation ingredient is
classical; the construction does not establish hard projected functions.

[even-tarjan-st]: ../sources.md#even-tarjan-st
