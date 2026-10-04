# Paper proof of the aggregate-gate transfer

[Model, literature, experiments, and limitations](index.md)

This is a paper-level deduction from the repository's stated graph ordering theorem.
It has passed an independent adversarial paper review relative to that baseline; it has
not been formalized, and the whole-corpus review remains separate. Every additional
semantic and counting obligation is given below. Symbols follow the parent note.

## Contract

A circuit has `n` primary input vertices, `s` binary Boolean gates, `q` special gates,
and one output. It is acyclic and gates have fixed ordered slots with possible repetition.
For each special gate `j`, its output is a fixed Boolean predicate of an aggregate
of its input signals. We permit two sorts of aggregates:

1. An integer sum `sum_i w_ji z_i`, with `L_j = sum_i |w_ji|` and `R_j=L_j+1`.
   A symmetric gate is the unit-weight case; a threshold is a particular output predicate.
2. A sum in the finite cyclic group `Z/m_j Z`, with positive `m_j` and `R_j=m_j`.

For any subset of a gate's occurrences, its attainable integer partial sums lie in an
interval of cardinality at most `L_j+1`. Repeated signals cause repeated contributions.
Every local aggregate update is a translation, hence is invertible once its increment
is known. Set `D = q + sum_j ceil(log2 R_j)` and assume `K>=2`.

The function `f` has at least `2^(n-2)` accepting inputs and is `K`-rectangle-free:
every one-rectangle across every partition of the input coordinates has a side of
cardinality strictly below `K`. Set `k=ceil(log2 K)` and `r=D+k+2`.

## 1. Conditioning special outputs

Choose a vector `a` of proposed special gate output bits. Delete those gates from the
graph. In a binary input slot previously fed by special gate `j`, substitute `a_j`.
Keep every primary input and binary gate vertex. Keep one ordinary edge per remaining
binary slot; parallel edges are allowed. Let the connected components be `C_i`.

The value of each ordinary signal in `C_i`, after substitution, depends only on `a`
and the primary inputs in `C_i`. This follows by induction along the original DAG:
every remaining ordinary predecessor is joined by an edge and therefore belongs to
the same component. Components with zero primary inputs cause no exception.

Given original input `x`, evaluate all ordinary signals under `a` and verify that each
special gate's predicate returns `a_j`. A vector passing all these checks must equal
the original evaluation's special-output vector. Prove this by induction along the
original topological order, interleaving binary and special gates. Conversely, the true
vector passes. Thus existentially guessing `a` is an exact, unique-witness simulation.

## 2. Exact rectangle cover across components

Let `U` be the primary inputs in any union of components. For each `a` and each possible
aggregate vector `u=(u_j)` from ordinary signals in those components, define:

- `P_(a,u)`: assignments to `U` producing the vector `u` under `a`. If the designated
  output is an ordinary signal on this side, also require that output to be one.
- `Q_(a,u)`: assignments to the remaining inputs such that each special-output check
  passes on aggregate `u_j + v_j + c_j(a)`. Here `v_j` is this side's ordinary-signal
  contribution and `c_j(a)` is the contribution from special-to-special wires.
  Require output one here if the designated output is an ordinary signal on this side;
  if it is special, require its corresponding `a` bit to be one here.

Each product `P_(a,u) x Q_(a,u)` is a one-rectangle by the uniqueness proof.
Every accepted input lies in one, by taking its true `a` and actual `u`.
There are at most `2^q product_j R_j <= 2^D` rectangles. Empty rectangles do not matter.
In particular we have not independently enumerated both sides' sums. This argument
does not assume symmetry of the global function, disjoint special-gate inputs, or that
special gates lie in one layer.

If `h=min(|U|,n-|U|)`, each rectangle contains fewer than
`K 2^(n-h) <= 2^(k+n-h)` inputs. Therefore

`2^(n-2) <= #f^-1(1) < 2^(D+k+n-h)`, hence `h<r`.

## 3. Semantic giant component and density-preserving fixing

Assume `n>=3r`. Apply the preceding inequality to each single component.
Unless some component has more than `n-r` primary inputs, all components have fewer
than `r` primary inputs. Greedily accumulate components until their input count first
reaches `r`. The resulting count is in `[r,2r)`, whose complement has at least `r`
inputs. This contradicts the same inequality for a component union.

Choose a component `C` with `n'>n-r` inputs and `s'` binary vertices.
Partition accepted inputs by the assignment outside `C`; averaging supplies a fixing
with at least `2^(n'-2)` accepted completions. The restricted function is still
`K`-rectangle-free: any rectangle lifts to an original rectangle by putting the fixed
outside coordinates on either side. Its side cardinalities do not change.

For fixed `a`, all ordinary components outside `C` can now be evaluated completely.
Add their aggregate contributions and those of special-to-special wires to the initial
accumulator vector. Enforce an outside output check in the initial state if necessary.
Only the input variables in `C` will be queried by the remaining verifier.

## 4. The graph with observed sinks

Let `t'` be the number of binary input slots in `C` whose predecessors are special.
There are exactly `2s'-t'` ordinary slot edges and `n'+s'` ordinary vertices.
For each signal with `d>=2` ordinary outgoing slots, insert a chain of `d-1` copy
vertices, adding `d-1` edges and preserving connectedness and `M-N`.
Signals with zero outgoing ordinary slots acquire no copy vertex or dummy output edge.

After this transformation each binary vertex has at most two incoming slot edges and
one outgoing copy/slot edge. Input vertices have degree at most one and copy vertices
degree three. No loop is created, including when binary input slots are repeated.
Consequently the result is a connected loopless degree-three multigraph with

`M-N=s'-n'-t'` and `N <= n'+s'+(2s'-t') <= n'+3s'`.

Each binary vertex computes its output from its local slot bits and constants from `a`;
if it has an ordinary outgoing edge, require that edge to agree. Whether or not such
an edge exists, emit the computed bit's aggregate contributions exactly once here.
Input vertices emit contributions when reading their input, including isolated inputs.
Copy vertices only impose equality and emit no contributions.
Thus observing many sink signals costs aggregate states, not extra graph edges.

The graph ordering theorem gives, for every fixed `eta>0`, an ordering with

`w <= (A+eta)(s'-n'-t')^+ + O_eta(log(N+1))`.

## 5. Frontier verifier and its exact state count

Process that vertex ordering, existentially assigning incident wire bits when needed.
A frontier state contains the cut-edge bits, `a`, and the accumulated contributions.
At each layer there are at most

`W_* = 2^(w+q) product_j R_j <= 2^(w+D)` states.

For integer sums, the interval for a partial accumulator can depend on the layer and
on `a`, because the initial offset does. Its cardinality is nevertheless at most `R_j`.
For modular sums use the whole cyclic group. Each layer queries its vertex's primary
input if it has one, otherwise no variable. Each input is queried exactly once.
The final state accepts precisely when all special-output checks pass. The ordinary
output-one condition is enforced locally or initially, as described earlier.

Fix a next state and the local values of all edges incident to the processed vertex.
All unchanged frontier bits are determined. The ordinary signal at that vertex is
determined, except for a primary-input vertex whose queried bit is also specified.
Subtract its aggregate increment to reconstruct the unique previous register contents.
Thus there are at most `2^3=8` incoming labeled transitions per next state: a binary or
copy vertex has at most three incident bits, while a primary input has at most one
incident bit plus its query bit. Fixed output tests only remove transitions.
At most `8N W_*` labeled transitions occur across the complete layered verifier.

## 6. Rectangle counting with registers

For a verifier state `v`, let `P_v` be the set of assignments to already-queried variables
that can reach `v`, and `Q_v` the set of assignments to remaining variables that allow
an accepting continuation. Concatenation of paths proves `P_v x Q_v` is a one-rectangle.
At an initial state `|P_v|<=1<K`.

Consider any accepting path. If every state along it has `|P_v|<K`, its full assignment
belongs to a terminal set of size `<K`. There are at most `W_*` terminal states, so
these assignments contribute fewer than `W_* K` in total.

Otherwise choose its first transition `u -> v` with `|P_u|<K` and `|P_v|>=K`.
Rectangle-freeness forces `|Q_v|<K`. Fix this labeled transition. If it queries a bit,
extend each assignment in `P_u` by that one prescribed bit; otherwise leave it alone.
The resulting prefix set has size `<K` and its product with `Q_v` is a one-rectangle
containing the selected path's input. There are at most `8N W_*` transitions. Hence

`#f_restricted^-1(1) <= (8N+1) W_* K^2`.

This argument deliberately does not assume that *all* predecessors of `v` have small
past sets. Only the chosen transition's predecessor does; counting transitions is
what avoids that common error. The partition is the input set processed at its layer.

## 7. Consequence and precise remaining boundary

Taking logarithms, using retained density, and substituting the graph bound yields

`n' <= (A+eta)(s'-n')^+ + D + 2k + O_eta(log(n+s+1))`.

In the candidate range `s=O(n)` with `D+k=o(n)`, `n'>n-r=n-o(n)`.
The positive part cannot be zero for sufficiently large `n`. Rearrangement gives

`s >= (1+1/(A+eta))(n-r) - (D+2k+O_eta(log(n+s+1)))/(A+eta)`.

Letting `eta` be arbitrarily small proves the claimed paper-level asymptotic deduction
`s >= (1+1/A-o(1))n`. Equivalently, for every fixed epsilon there is a threshold beyond
which no circuit family satisfying the displayed sublinear budget and computing the
fixed hard family has `s <= (1+1/A-epsilon)n`. Thresholds may depend on the budget family.
Since `q<=D=o(n)`, total gate size `s+q` has the same leading lower bound.

No theorem for unrestricted threshold bit lengths follows: `D` is an explicit premise,
not a quantity this proof bounds for every gate. A universal budget-reducing restriction
preserving enough hard inputs is the first unproved extension. Formal verification of
this paper deduction, whole-corpus review, and its exact historical priority remain open.


## 8. Fixed-slack linear parity budget

The finite inequality also applies to a fixed small linear aggregate budget, with an
explicit coefficient loss. Let `L=1+1/A` and fix the dense rectangle-free family with
`k(n)=ceil(log2 K(n))=o(n)`. For every fixed `delta in (0,1/3)` and `epsilon>0`, there is
`n0` such that, for every `n>=n0` and every circuit of the stated model computing that
slice, if its `q` special gates are parity gates and

`2q <= (1/3-delta)n`,

then its total charged size satisfies

`S=s+q >= L n - (1+4/A)q - epsilon n`.

The threshold is uniform over circuits and over permitted values of `q` at each length;
it can depend on the fixed family, `delta`, and `epsilon`. In particular every sequence
with that fixed slack satisfies `S >= L n - (1+4/A)q - o(n)`.

**Proof.** Write `B=A+eta` for a fixed positive graph slack `eta`. A circuit with
`s>Ln` already satisfies the conclusion, so restrict to `s<=Ln`; then the graph and
counting remainders are uniformly `O_eta(log n)`. Since parity has `R_j=2`, `D=2q`.
The budget and `k=o(n)` imply

`n-3D >= 3 delta n >= 3(k+2)`

for sufficiently large `n`. Thus `n>=3(D+k+2)` and Section 3 gives `n'>n-D-k-2`.
The zero positive-part branch in Section 7 would imply

`n' <= D+2k+O_eta(log n)`,

contradicting `n'>n-D-k-2` for large `n`, since `D<=n/3`. Consequently Section 7
rearranges, including the constant `+2` in `r`, to

`s >= (1+1/B)n - (1+2/B)D - (1+3/B)k - O_eta(log n)`.

Substitute `D=2q` and add `q` to obtain the total-size inequality

`S >= (1+1/B)n - (1+4/B)q - (1+3/B)k - O_eta(log n)`.

The difference of its first two terms from the desired first two terms is

`[(1+1/B)n-(1+4/B)q] - [L n-(1+4/A)q]`
`= -eta/(AB) * (n-4q) >= -eta/(AB) * n`.

Choose a fixed `eta` making this loss less than `epsilon n/2`. With that `eta` fixed,
`k=o(n)` and `log n=o(n)` absorb the remaining loss into `epsilon n/2` for sufficiently
large `n`. This proves the uniform assertion without substituting `eta=0` into a bound
whose additive constant depends on `eta`.

Numerically, `1+4/A = 15.249990716...`. If `q<=0.01n`, a fixed slack is available and

`S >= (L-0.01(1+4/A)-o(1))n = (4.409997772...-o(1))n`.

The finite proof also works whenever `n>=3(2q+k+2)` holds eventually, even without a
fixed density gap, because that guard implies `D<=n/3` and the same zero-branch argument.
The pointwise condition `2q/n<1/3` alone does not guarantee this guard when its gap
tends to zero. No conclusion for that entire boundary regime is claimed here.
