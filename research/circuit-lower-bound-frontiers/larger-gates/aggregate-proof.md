# The formalized aggregate-gate transfer and paper extensions

[Model, literature, experiments, and limitations](index.md)

The finite commutative-monoid transfer is now formalized in
[`Aggregate/Hardness.lean`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Hardness.lean).
For the same fixed full-input-length family in P, it gives more than
`(1+1/A-epsilon)n` **total gates** when the aggregate budget is bounded by a fixed
sequence `D(n)=o(n)`. The Gaussian specialization is unconditional and gives
`1+1/A = 4.562497679...`. The affine-input extension and the fixed linear parity
budget in Section 8 remain paper deductions, not consequences claimed by the checked
mixed-circuit theorem. Historical priority remains unresolved.

The inherited architecture follows Ryan Williams's private working note, the graph
compiler is Schlesinger's, and the explicit extractor construction is due to
Chattopadhyay–Liao; see the [source guide](../../../docs/algebraic/cutwidth-lower-bound.md).
The following argument explains the aggregate extension, using outgoing transitions
so that no cancellation or inverse operation is needed.

## Contract

A circuit has `n` primary input vertices, `s` binary Boolean gates, `q` special gates,
and one output. It is acyclic and gates have fixed ordered slots with possible repetition.
For each special gate `j`, its output is a fixed Boolean predicate of an aggregate
of its input signals in a finite commutative monoid `M_j`. Each ordered slot has a
fixed map from its Boolean signal to `M_j`; repeated slots contribute separately.
The output is any Boolean predicate of the product. Write `R_j=|M_j|` and
`D = q + sum_j ceil(log2 R_j)`, and assume `K>=2`. The checked theorem imposes no
fan-in, fanout, depth, or wire-count bound beyond finiteness and acyclicity.

This includes noninvertible AND, OR, and capped counters, as well as modular sums.
For signed integer weights with `L_j=sum_i |w_ji|`, shift each slot's two possible
contributions to be nonnegative. Their total lies in `[0,L_j]`, so a counter capped
at `L_j` has `R_j=L_j+1` states and the readout can undo the fixed offset. Symmetric
gates are the unit-weight case. Cyclic sums use `R_j=m_j` states directly.

The function `f` has at least `2^(n-2)` accepting inputs and is `K`-rectangle-free:
every one-rectangle across every partition of the input coordinates has a side of
cardinality strictly below `K`. Set `k=ceil(log2 K)` and `r=D+k+3`, matching the
checked finite guard.

For the repository's sumset-derived hard family, the
[affine transport deduction](../hard-functions/index.md) supplies these same two
function hypotheses, with the same threshold uniformly over every invertible affine
basis. Coordinate rectangle-freeness alone does not imply affine invariance. This
separate, unformalized paper extension also permits a free choice of exactly `n` affine
input coordinates before the augmented circuit. The aggregate budget is measured on
those transformed signals; it does not charge the input matrix or permit free internal
linear gates. This composes hypotheses, not lower-bound coefficients.

## 1. Conditioning special outputs

The paper graph below deletes special vertices entirely; the checked compiler keeps
their indices as nullary constants, as detailed in the exact checked interface below.
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
  passes on aggregate `u_j * v_j * c_j(a)` in `M_j`. Here `v_j` is this side's ordinary-signal
  contribution and `c_j(a)` is the contribution from special-to-special wires.
  Require output one here if the designated output is an ordinary signal on this side;
  if it is special, require its corresponding `a` bit to be one here.

Each product `P_(a,u) x Q_(a,u)` is a one-rectangle by the uniqueness proof.
Every accepted input lies in one, by taking its true `a` and actual `u`.
There are at most `2^q product_j R_j <= 2^D` rectangles. Empty rectangles do not matter.
In particular we have not independently enumerated both sides' products. This argument
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
Input vertices emit contributions when reading their input. In the chosen connected
component with at least two inputs, each input has an outgoing edge and hence a port.
Copy vertices only impose equality and emit no contributions.
Thus observing many sink signals costs aggregate states, not extra graph edges.

The graph ordering theorem gives, for every fixed `eta>0`, an ordering with

`w <= (A+eta)(s'-n'-t')^+ + O_eta(log(N+1))`.

## 5. Frontier verifier and its exact state count

Process that vertex ordering, existentially assigning incident wire bits when needed.
A frontier state contains the cut-edge bits, `a`, and the accumulated contributions.
At each layer there are at most

`W_* = 2^(w+q) product_j R_j <= 2^(w+D)` states.

Use the full finite monoid for each register. Each layer queries its vertex's primary
input if it has one, otherwise no variable; each input is queried exactly once.
The final state checks all special outputs. The ordinary output-one condition is
enforced locally in this paper accounting. The checked compiler instead uses a
one-bit Boolean observation register, giving the extra factor two recorded below.

Fix a state **before** processing a vertex and the values of all incident edges.
These data determine the next cut bits and the vertex contribution, hence the next
aggregate by multiplication. There are at most `2^3=8` such outgoing keys per state.
For an input vertex, the port edge determines the queried bit. A nullary or binary
vertex computes its value from its incident slots, including when it is a sink.
Copy vertices contribute the identity. No previous register is reconstructed from a
next register, so noninvertible updates create no extra factor. At most `8N W_*`
labeled transitions occur across the verifier.

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

Letting `eta` be arbitrarily small proves the asymptotic deduction
`s >= (1+1/A-o(1))n`. Equivalently, for every fixed epsilon there is a threshold beyond
which no circuit family satisfying the displayed sublinear budget and computing the
fixed hard family has `s <= (1+1/A-epsilon)n`. Thresholds may depend on the budget family.
Since `q<=D=o(n)`, total gate size `s+q` has the same leading lower bound.

No theorem for unrestricted threshold bit lengths follows: `D` is an explicit premise,
not a quantity this proof bounds for every gate. A universal budget-reducing restriction
preserving enough hard inputs is the first unproved extension. The generic monoid
transfer is formalized; its exact historical priority remains open.


### Exact checked interface

The implementation replaces special gates by nullary constants at the same wire
indices. Its graph compiler uses the resulting closed component, emits each signal's
aggregate contribution once, and copies with the identity. With total gate count
`g=s+q`, it proves `|V|<=n+3g` and `|E|-|V|<=g-m` for a component with `m` inputs.
The output check uses at most one additional state bit. The checked finite slice bound is

`2^(m-2) <= ((n+3g) * 2^((A+eta) max(g-m,0) + 3 log2(n+3g) + C+3) + 1)`
`             * 2^(D+1) * K^2`,

with `2<=m<=n` and `n-m<=D+ceil(log2 K)+3`. The formal asymptotic theorem uses this
bound on **total** gates, rather than asserting the sharper ordinary-gate intermediate
above. `AggregateNetwork.card_accepting_le_of_read_eq_univ` supplies the outgoing-key
count, `Aggregate.exists_large_component` supplies the component, and
`Aggregate.sourceReductionHardFamily_eventually_lt_size_gaussian` is the final theorem.

## 8. Fixed-slack linear parity budget

This section is an unformalized paper deduction from the sharper ordinary-gate
accounting above. The finite inequality also applies to a fixed small linear budget, with an
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

`n-3D >= 3 delta n >= 3(k+3)`

for sufficiently large `n`. Thus `n>=3(D+k+3)` and Section 3 gives `n'>n-D-k-3`.
The zero positive-part branch in Section 7 would imply

`n' <= D+2k+O_eta(log n)`,

contradicting `n'>n-D-k-3` for large `n`, since `D<=n/3`. Consequently Section 7
rearranges, including the constant `+3` in `r`, to

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

The finite proof also works whenever `n>=3(2q+k+3)` holds eventually, even without a
fixed density gap, because that guard implies `D<=n/3` and the same zero-branch argument.
The pointwise condition `2q/n<1/3` alone does not guarantee this guard when its gap
tends to zero. No conclusion for that entire boundary regime is claimed here.
