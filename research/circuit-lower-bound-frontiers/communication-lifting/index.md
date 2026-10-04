# Communication and lifting: preserving sharing without losing the leaf condition

**Status, 4 October 2026.** DAG lifting is already a successful circuit-size method for
monotone circuits. This note proves two elementary transfer/obstruction lemmas and derives
restricted-class consequences of published results. It obtains no improved unrestricted
`B₂` coefficient, superlinear unrestricted bound, or separation of `NC¹` from `P`.
The useful next target is robustness to distributed negative information, with every shared
gate charged once. Merely replacing communication trees by arbitrary reusable DAGs is unsafe.
The [baseline guide](../../../docs/algebraic/cutwidth-lower-bound.md) gives coefficient
`L = 1 + π/(3 arccos((1+2√2)/4)) ≈ 4.5625`; its size is internal `B₂` gates.
Unlike its variable-partition rectangles, a KW rectangle concerns **two complete inputs**.
These are different domains, and their hardness hypotheses cannot be interchanged.

## Models and the published transfer

Write `N` for the final Boolean input length, `s` for internal binary gates, and `D` for
all nodes of a protocol DAG, including terminals. Fanout is unrestricted in the circuit.
For `A=f⁻¹(1)` and `B=f⁻¹(0)`, `KW_f` outputs `i` with `x_i ≠ y_i`;
when `f` is monotone, `mKW_f` instead requires `x_i=1, y_i=0`.
The parties hold `x∈A` and `y∈B`, respectively, throughout the protocol.
A semantic rectangle DAG labels each node by `R_v=X_v×Y_v⊆A×B`.
The root is `A×B`; a node's set is covered by its two children's sets; every terminal's
set satisfies its output relation. The children need not partition the parent, and a
node may have many parents. Size counts a shared node once. These are not ordinary
communication trees with their leaves merged after the fact. Triangle DAGs replace
rectangles by `{(x,y):a(x)<b(y)}`. The monotone Boolean/real circuit correspondences and
the first general DAG lifting theorem are in [garg20][garg20], Sections 2–3.
For a monotone AND/OR circuit, label gate `g` by `{x:g(x)=1}×{y:g(y)=0}`.
At either gate type this set is covered by the two child sets; input terminals are
directed disagreements. This gives `D≤s+N`, with no unfolding and no depth charge.
The converse separator construction is the established monotone circuit correspondence;
its harmless input-node conventions should not be used to claim exact gate coefficients.
For outer search relation `S:Σ^k→O` of conjunction/subcube-DAG width `w`, use
`Ind_m:[m]×Σ^m→Σ`, `Ind_m(a,b)=b_a`, with the same partition in every block.
Binary encodings use exactly `k⌈log₂m⌉` Alice bits and `km⌈log₂|Σ|⌉` Bob bits
(unused codes are promises). This raw length is not the length of a later Boolean function.
Near-linear index gadgets already appear in [lovett22][lovett22], Sections 6–7.

The current colourful-alphabet theorem gives triangle-DAG size at least
`[m/(A|Σ|w log(mk))]^w`, for an absolute `A`; rectangles are included.
Its sparse clique-colouring reduction has `N≤d²km²` variable edges for constant-degree
outer expanders. Taking `m=Ck log k` gives hardness `exp(Ω(k))` with
`N=O(k³ log²k)`. Theorem 10 supplies a total monotone family in `P` with
`L_mon(f_N)≥2^(cH(N))`, `H(N)=(N/log²N)^(1/3)`, for some `c>0` on its parameter family.
These are published results, including the `P` assertion, not a new construction here.
See [rezende-vinyals25][rezende-vinyals25], Theorems 10–11, Lemma 20, and the proof of Theorem 10.
The exact edge count, rather than the number `km` of graph vertices or raw gadget bits,
is the input parameter in all applications below; no all-length padding lemma is asserted.
For comparison, [rezende25][rezende25] proves monotone and special semi-monotone KRW
composition results, measuring communication depth/tree leaves. Its semi-monotone
theorem uses a universal outer relation. The 2025 XOR/random-function strong-composition
result also measures tree leaves [chukhin25][chukhin25]. Neither supplies a DAG-node inequality.
The July 2026 revision of [yang-zhang26][yang-zhang26], Theorem 1.3, lifts one-way two-party cost to
one-way number-on-forehead cost; there is no circuit-DAG compiler in this note for it.
Changing the number of parties or restricting the speaking order is not a free transfer.

## Proposal 1: a signed-leaf DAG target for unrestricted gates

**Exact compiler, proved here.** Any `N`-input `B₂` circuit with `s` gates has a
rectangle DAG for `KW_f` with at most `6s+2N+2` nodes.
Maintain both rails `g` and `¬g`. For each nonconstant two-bit truth table, form the
DNFs for its two output values from the four possible input minterms. Together they
use four AND gates and at most two OR gates. Constants simplify away. Input rails
are `x_i,¬x_i`, so there are at most `2N` terminals; two spare nodes cover conventions.
All parents reuse the same two rails. Applying the preceding rectangle construction
to this monotone network on literals yields a valid DAG on `A×B`.
Positive rail terminals have `x_i>y_i`, negative ones `x_i<y_i`; both output `i`.
The rails are local functions of the original input, not `2N` independent input bits.
Consequently, the precise sufficient target for coefficient `C>L` is
`rect-DAG(KW_fN) > (6C+2)N+2` for an explicit `P` family.
For example, `rect-DAG(KW_fN)>32N+2` would force more than `5N` gates.
This is a valid size implication, not the original `s−N` exponential compiler:
one must not append the baseline's `+1` to it. A lower bound for `mKW_f` is insufficient.
For parity the compiler has `O(N)` nodes because parity has `N−1` XOR gates.

**Smallest missing statement.** Find a hard outer search relation and local reduction
to this **undirected** `KW` relation that preserves a DAG lower bound beyond that
linear threshold, with final `N` explicitly counted. Known reductions into `mKW`
decode a directed edge discrepancy; an undirected answer can have the wrong sign.
No such new reduction is supplied. Calling the desired signed-leaf lower bound a
“lifting conjecture” does not make it easier than the unrestricted circuit problem.

**Decisive falsifier: equality nodes collapse the target.** Allow feasible sets
`{(x,y):a_v(x)=b_v(y)}`, with unrestricted labels, in place of rectangles.
Then **every** nonconstant `N`-bit function has a `KW` DAG of at most `2N−1` nodes.
For `0≤j<N`, let `E_j` mean equality of the first `j` bits (`E_0` is the root).
For `0≤j<N−1`, give `E_j` children `E_(j+1)` and `D_j={x_j≠y_j}`.
Here `D_j` is an equality set, using labels `x_j` and `1−y_j`, and is a terminal
outputting `j`. Finally `E_(N−1)` is a terminal outputting `N−1`: since `A∩B=∅`,
agreement on the first `N−1` bits forces disagreement on the last. There are
`N−1` internal nodes and `N` terminals. This proves the claim for all `N≥1`.
Equality of long labels is free in this semantic model; charging its evaluation
would define a different model requiring a new circuit compiler.
This does not refute equality-DAG research for **monotone** interpolation
[folwarczny22][folwarczny22]. With zero-based coordinates, for `f(z_0,z_1)=z_1`, `x=01`, `y=10`, terminal `0` in this construction
has the wrong direction. **Stop rule:** reject any unrestricted KW route whose
feasible-set family contains these equality sets at constant node cost.

## Proposal 2: arbitrary shared preprocessing on a bounded coordinate set

**Larger restricted model.** Fix any `J⊆[N]`, `|J|=r`. Permit an arbitrary `B₂`
preprocessing DAG whose inputs lie in `J`, with arbitrarily many outputs and fanouts,
followed by a monotone AND/OR DAG reading all original inputs and those outputs.
Count all preprocessing gates `s_P` and monotone gates `s_M`; `s=s_P+s_M`.
There is no bound on depth, number of preprocessing outputs, or graph cutwidth.
This contains monotone circuits and permits, for example, shared parity and multiplexers
on `J`. It does not permit negating a gate depending on inputs outside `J`.

**Restriction/recombination lemma, proved here.** If the output function `f` is
monotone, then `L_mon(f) ≤ 2^r(s_M+r+1) ≤ 2^r(s+r+1)`.
For each assignment `a∈{0,1}^J`, preprocessing becomes constant and the residual
monotone circuit `f_a` uses at most `s_M` gates. Set

`F(x) = OR_a [ (AND_{j∈J:a_j=1} x_j) AND f_a(x_[N]\J) ].`

If a summand accepts, `a≤x_J`, so monotonicity gives `f(x)=1`.
If `f(x)=1`, the summand `a=x_J` accepts. Thus `F=f`.
Each copy uses at most `s_M` gates, its positive mask at most `r−1`, attachment
at most one, and the final OR at most `2^r−1`; the displayed looser bound covers
`r=0` and empty masks too. Constants are permitted and need no internal gates.
Sharing is kept inside every residual copy; duplication is charged exactly once
for each of the `2^r` assignments, not once for every use of a preprocessing output.

**Consequence already justified.** For the preceding hard family,
`s ≥ 2^(cH(N)−r)−r−1`. Hence `r=o(H(N))` still forces `s=2^Ω(H(N))`.
This is a consequence of a published monotone bound and the elementary lemma,
not a new priority claim. No gadget is added at this stage and input length stays `N`.
The model is closely related to restricting the set of negated input variables;
the more general literature is explicitly treated by [jukna-lingas22][jukna-lingas22].

**Missing extension and falsifier.** The proof needs one global coordinate set `J`.
Replacing `r` by the number of preprocessing *outputs* is invalid: one such output
can be the entire target function. Its circuit must be charged, and after fixing
its value the remaining domain is generally not a subcube. Parity fibers already
violate the restriction step; a polynomial circuit for the hard monotone `P` family
also refutes a transfer charging only one feature instead of its coordinate support.
**Stop rule:** do not extrapolate this
bound to a small number of arbitrary NOT gates or arbitrary global features.

## Proposal 3: distributed negation width with a smaller loss

Use the established DeMorgan model: binary AND/OR gates, literals at the inputs,
unrestricted sharing, and a monotone output function. Formal expansion keeps
contradictory terms and removes repeated literals. Negation width `w` means each
prime implicant `p` of the output has some generated nonzero term `p∧q`, where
`q` contains at most `w` negative literals. Other terms may be unrestricted.
This is the circuit restriction of [jukna-lingas22][jukna-lingas22], Definition 1, not a bound on NOT gates.
Negative coordinates may differ between prime implicants, so no global `J` is needed.

**Existing size transfer.** Theorem 1 of [jukna-lingas22][jukna-lingas22] covers the output by an OR of
monotone subcircuits. Its proof gives at most `⌈4N^w log₂M⌉` copies, using the
`4p^w` bound with maximum prime-implicant length `3≤p≤N` and `M≤2^N` implicants.
Keeping the final OR gates explicit gives the safe bound
`L_mon(f) ≤ (4N^(w+1)+1)(s+1)`.
This is a DAG-size simulation: `s` counts each reused AND/OR gate once, even though
the formal term set used to define width can be enormous.
Applied to the hard family it yields `s+1 ≥ 2^(cH(N))/(4N^(w+1)+1)`.
Thus `w=o(H(N)/log N)` retains exponential hardness. This is another deduction
from existing results, not a claim that all nonmonotone circuits satisfy small width.
The hard family eventually has `p≥3`, since `p≤2` would give a polynomial-size DNF.

**Concrete research target.** For this fixed lifted family, prove the stronger
simulation `L_mon(f_N) ≤ N^C 2^(Cw)(s+1)` for one absolute `C`, preserving DAGs.
This would retain `2^Ω(H(N))` size for `w=o(H(N))`, a factor `log N` wider
negation-width regime than the safe transfer above. It would enlarge the restricted
class, not improve the unrestricted `B₂` coefficient. There is no extra input blow-up.

**Attempt and obstruction.** In the random-restriction proof, a term with disjoint
positive set of size `p` and negative set of size `w` survives with probability
`θ^w(1−θ)^p`. Its maximum is attained at `θ=w/(p+w)` and equals
`(w/(p+w))^w(p/(p+w))^p`. For `p≫w` the reciprocal is
`exp(Θ(w log(p/w)+w))`, not `2^O(w)`. Merely optimizing the independent
restriction probability therefore cannot prove the target. One needs additional
structure of the lifted family's prime implicants or a different DAG invariant.
This calculation isolates a genuine obstruction to this particular proof, not
a counterexample to the conjectured simulation. **Stop rule:** abandon this
proposal if all candidate arguments still pay independently for the `p` positions;
first demand a bound that removes `log(p/w)` in a nontrivial growing-`w` regime.

## Validation, adversarial cases, and recommendation

[check_transfers.py](data/check_transfers.py) and [fixed output](data/check_transfers.txt)
exhaust all 16 gate truth tables; all nonconstant functions through three bits for
the equality-DAG invariant; and all 168 four-bit monotone functions and all their
coordinate subsets for the recombination identity. They also check the wrong-sign
two-bit example. No random seed is needed. The proofs above establish the general
lemmas; finite enumeration does not validate asymptotic lifting or the open simulation.

- **Parity and arbitrary semantics:** dual rails handle every binary truth table;
  no claim that XOR preserves directed disagreement is used.
- **Multiplexers and shared state:** support-local preprocessing can reuse a computed
  address or parity arbitrarily often; its gate count is included once before copying.
- **Expander cores:** the restricted transfer assumes no separator, so expanders do not
  invalidate it; it cannot turn an arbitrary expander-wired `B₂` circuit monotone.
- **Partitions:** all DAG lower bounds use one fixed two-party gadget partition.
  Allowing each node to choose a different partition requires a new theorem.
- **Priority:** monotone DAG lifting and bounded-negation simulation are established
  research programs. The present new work product is the transfer audit and checks;
  novelty of the proposed stronger family-specific simulation is unestablished.

Prioritize Proposal 3 only after checking its prime-implicant structure; Proposal 2
is a rigorous fallback theorem layer. Keep Proposal 1 as the exact unrestricted
contract and its equality-node falsifier. No currently verified ingredient in this
note changes the baseline's leading coefficient.

[chukhin25]: ../sources.md#chukhin25
[folwarczny22]: ../sources.md#folwarczny22
[garg20]: ../sources.md#garg20
[jukna-lingas22]: ../sources.md#jukna-lingas22
[lovett22]: ../sources.md#lovett22
[rezende-vinyals25]: ../sources.md#rezende-vinyals25
[rezende25]: ../sources.md#rezende25
[yang-zhang26]: ../sources.md#yang-zhang26
