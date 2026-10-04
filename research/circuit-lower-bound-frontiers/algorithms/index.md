# Algorithmic engines: pay for discovery and the entire recursion

The most useful result of this investigation is an accounting obstruction: a restriction
that removes many gates **on average** need not improve an exact algorithm. The correct
quantity is the sum of exponential costs of every descendant. Below, an elementary
whole-tree theorem makes this obligation explicit, and a selector circuit defeats the
naive average-deletion criterion. No new universal SAT algorithm or circuit lower bound
is proved here. The three proposals remain conditional research programs.

## Model and exact transfer obligations

Inputs are unrestricted fan-in-two Boolean circuits with `n` declared input bits, `s`
internal gates, arbitrary truth tables, one output, and unrestricted sharing. An ordinary
binary gate record has `O(log(n+s))` bits. All runtimes include reading this description,
finding certificates, simplifying restrictions, arithmetic on counts, and terminal work.
Ignored input bits retain their multiplicity in #SAT; they are not silently discarded.
All logarithms are base two. `O*` below suppresses polynomial factors in `n+s` only.

The [current compiler guide](../../../docs/algebraic/cutwidth-lower-bound.md) and
[transfer ledger](../transfer-ledger.md) give the leading width coefficient
`A = (3/pi) arccos((1+2sqrt(2))/4) ≈ 0.2807019373` on gate surplus `s-n+o(n)`.
Here n counts inputs actually read; for an arbitrary circuit use its read-input count m.
They prove existence of an order and a counting bound; this note supplies no deterministic
time bound for discovering the order. Existence is enough for that circuit lower bound,
but an exact algorithm must construct, read, and use its certificate within its budget.

The relevant external transfer is Williams's Theorem 1.1: a superpolynomial saving for
Circuit SAT on `n` variables and `n^k` gates, **for every fixed k**, yields
`NEXP ⊄ P/poly`. Deterministic algorithms suffice. Theorem 1.3 gives the corresponding
acceptance-probability route. These are separate from strengthening a specified P family's
linear-size lower bound [williams13][williams13].
For a safe target use one constructible `h(n)=omega(log n)` and total time
`2^(n-h(n)) poly(n^k)` for every k. Ordinary constant-factor binary-basis translations
preserve this target. A `2^((1-delta(c))n)` algorithm only for `s<=cn`, with fixed c,
does not meet these quantifiers. Padding to `N≈s` inputs makes its exponent depend on N,
and does not repair the mismatch. Near-linear gains remain meaningful algorithmic results.

## Proposal 1: a discoverable exact semantic-interface compiler

**Mechanism.** Make a terminal certificate a finite Boolean constraint network of maximum
degree three, a vertex order of edge cutwidth w, and a construction-level bijection between
its satisfying edge assignments and the accepted assignments of the used circuit inputs.
Copy constraints encode fanout. Each gate constraint uses its actual truth table, so XOR,
multiplexing, and repeated arguments are covered. The output is constrained to one.
The network transformation must establish the bijection; an arbitrary nondeterministic
cover does not have it. This distinction matters for #SAT, even when SAT is preserved.

**Elementary terminal lemma.** Given such a network with N vertices and its order, exact
counting takes `poly(N,n) 2^(w+3)` bit operations. Maintain, for each assignment to the
crossing edges, the number of compatible assignments inside the processed prefix.
Processing one degree-three vertex introduces at most three edge bits; check its local
predicate, sum over forgotten bits, and retain the next frontier. Induction proves that
each table entry counts exactly those partial assignments. At the end the table is a
single count. Counts have `O(N+n)` bits, and unused original inputs multiply it by a
known power of two. This is a paper proof for the stated certificate, not an implementation
of the repository's full wiring transformation.

The broader knowledge-compilation precedent is established: deterministic decomposable
NNF supports model counting, and compilation can exploit decomposition and caching
[darwiche02][darwiche02]. Our missing quantity is total compilation cost with a useful
exponent on these unrestricted shared circuits, not tractability after compilation.

**Smallest decisive lemma.** For a specified slack eta, deterministically find and construct
the certificate in time `Q(n,s)` with
`Q(n,s) + poly(n,s) 2^((A+eta)(s-m+o(n))) <= 2^(n-g(n,s)) poly(n,s)`.
The error term must be uniform in the size range under consideration. The existing
Gaussian construction suggests randomized search followed by width verification, but
continuous samples, finite precision, probability of success, and expansion of the
compressed graph need resource proofs. Expected randomized construction by itself does
not instantiate the deterministic Williams premise used here.

If discovery is subexponential and `s<=cn` with `1<c<1+1/A`, combine this bound with
brute force on the m read inputs. Its leading exponent is
`min(m,A(s-m)) <= A s/(1+A) < n`; sufficiently small slack preserves a fixed saving.
Unused inputs contribute their exact multiplicity. This is a conditional near-linear
#SAT consequence of the compiler. To reach the larger model of all polynomial
size Boolean circuits and hence the NEXP transfer, replace its surplus exponent by
`n-h(n)` uniformly for each polynomial size bound; the current graph estimate cannot do so.
A terminal representing only one satisfying assignment supplies neither this count nor
a small representation of the whole function for a separate P-family lower bound.

**Falsification and stopping condition.** Include arbitrary relabelings, duplicated signals,
large fanout, XOR cancellation, selector circuits, and cubic expander cores. Reject the
algorithm claim if searching for the layout or checking semantic equivalence consumes
the saving. A polynomially checkable width certificate is not a polynomial-time search
algorithm; `N!` enumeration is plainly outside the intended near-linear budget.

## Proposal 2: a global semantic-terminal-or-profitable-restriction theorem

This is the preferred nonlocal target. A search state includes a residual circuit and its
remaining input domain. A branch partitions that domain into disjoint cylinders by fixing
one or more input bits. A terminal returns an exact count using a certified interface,
affine elimination, or another fully specified algorithm. A syntactically all-affine
circuit, for example, admits polynomial-time exact counting by Gaussian elimination.
This is an example terminal, not a completeness claim about semantically affine circuits.
Every nonterminal branch must fix at least one previously unfixed bit, giving depth `D<=n`.

**Whole-tree cost theorem (proved here).** Assign each state C a nonnegative real potential
`mu(C)`. Suppose the algorithm's *entire local work*, including failed certificate searches,
branch discovery, restriction construction, recombination, and any terminal solver, is at
most `P 2^mu(C)`, where P is polynomial in the root description length. Require

`sum_children 2^mu(C_child) <= 2^mu(C)`.

Then the total runtime is at most `(D+1)P 2^mu(root)`. Proof: the sum of `2^mu` over
any level is at most its value at the root, by induction using the displayed inequality.
Sum local costs across the at most D+1 levels. Exact #SAT follows because restrictions
partition assignments; sum child counts, retaining factors for deleted unused variables.
No particular branching strategy or certificate discovery theorem is hidden in this
argument. This is a cost-aware specialization of the standard branching-vector analysis
in measure-and-conquer, rather than a new general recurrence technique [fgk09][fgk09].

**Quantitative obstruction.** Consider the unclipped surplus potential
`mu=A(s-m+1)`, where m is the residual input count. Fix b inputs and delete `d_a` gates
in assignment branch a. Provided this potential stays nonnegative, the branch condition is

`sum_(a in {0,1}^b) 2^(-A(d_a-b)) <= 1`.

If every branch deletes d gates, this requires `d >= (1+1/A)b ≈ 4.5625b`.
Thus a five-gate deletion per input can pay at this coefficient, while four cannot.
By Jensen's inequality the same threshold is necessary for the *average* deletion, but
is not sufficient: the abstract binary profile `(d_0,d_1)=(1,9)` has mean five yet mass
`1+2^(-8A)>1`. That numerical profile is an arithmetic counterexample to an inference,
not a claim about the minimal size of a particular circuit.

There is also an actual circuit obstruction. Write `C(x,y)=x AND B(y)`, with B on k>=1
essential inputs and t gates, `t>=k-1`. C has k+1 inputs and t+1 gates. On x=1 it becomes
B, whose `max(s-m+1,0)` equals C's; on x=0 it is constant and has zero clipped surplus.
Hence the child mass ratio is `1+2^(-A(t-k+1))>1`, although the average number of removed
gates is `(t+2)/2`. This obstructs the scalar-surplus analysis of that branch, even if
one child is exceptionally easy. It does not rule out choosing a different branch,
using another potential, direct terminal counting, or eliminating redundant gates first.

Parity gives the complementary warning. A parity tree uses m-1 gates; fixing one input
leaves parity or its complement on m-1 inputs, with m-2 gates when m>=3. Surplus is zero
throughout, so the two child masses sum to two. The function nevertheless has a tiny
semantic state and an immediate count. A dichotomy that forces profitable branching on
parity because its wiring looks awkward has missed its terminal case. Likewise, an
expander skeleton does not force semantic hardness: affine gate labels remain tractable.

**Smallest decisive lemma.** Construct a sound deterministic procedure that, for every
state in a precisely defined near-linear regime, either completes an exact semantic
terminal or finds a branch satisfying the whole-tree inequality, with root potential
`mu(root)<=n-g(n,s)` and all its discovery costs covered. This is one global coverage
theorem, not separate observations that some circuits have interfaces and others simplify.
The allowed terminal families and branching candidates must be fixed before proving it.

**Consequence and stop rule.** The theorem yields exact #SAT in
`2^(n-g(n,s)) poly(n,s)`. For each fixed c, `g>=delta(c)n` is a near-linear SAT gain;
for every fixed k, `g(n,n^k)>=h(n)=omega(log n)` gives the Williams NEXP consequence.
Neither statement directly raises the current explicit-P coefficient. That would also
need a whole-function compiler and hardness for exactly its output representation.
Stop any proposed proof at its first residual state lacking either an affordable terminal
or a mass-bounded branch. A favorable first restriction or expected gate shrinkage is
insufficient; every descendant and every certificate search must satisfy the contract.

## Proposal 3: adaptive terminal PRGs for CAPP, with a weighted entropy ledger

For approximation, terminal interfaces can be cheaper. Suppose an adaptive restriction
tree partitions the input cube into leaves ell fixing `b_ell` bits. Put
`m_ell=n-b_ell`, `p_ell=2^(-b_ell)`; then `sum p_ell=1`. At each leaf, deterministically
construct a sampler with `r_ell` seed bits whose average evaluation differs from that
leaf's true acceptance probability by at most `epsilon_ell`.
The sampler guarantee must follow from a proved terminal class: checking it against an
arbitrary circuit by exhaustive counting would already spend the target budget.

**Weighted terminal lemma (proved here).** The estimate obtained by multiplying leaf
estimates by `p_ell` and summing has error at most `sum p_ell epsilon_ell`, by the
triangle inequality. If one evaluation and output generation cost at most P, total seed
evaluation cost is at most

`P sum_ell 2^r_ell = P 2^n sum_ell p_ell 2^(r_ell-m_ell)`.

Add the cost of generating the entire adaptive tree and constructing every sampler.
The exponent is controlled by this weighted sum, not the smallest seed at a favorable
leaf. With `epsilon_ell<=1/6`, this is CAPP. With total cost
`2^(n-h(n))poly(s)` and `h=omega(log n)` for every polynomial circuit size, Williams's
CAPP theorem gives `NEXP ⊄ P/poly` [williams13][williams13]. This explicitly names the
larger circuit model; no such sampler/tree construction is supplied here.

**Smallest decisive lemma.** Find the tree and terminal samplers within the same budget,
with weighted seed factor at most `2^-h(n)` and weighted error at most 1/6, uniformly
over the target size regime. If brute-force terminals occupy input probability p, their
contribution to that factor is p. Therefore they must have total probability at most
`2^-h(n)`; saying merely that they are rare is quantitatively inadequate.
Substantial semantic compression at most leaves is useful only with this residual bound.

**Falsification and stop rule.** Constant additive error cannot decide exact SAT: a
singleton accepting assignment has density `2^-n`, and an estimate of zero is valid
for n>=3 at error 1/6. Use the CAPP transfer directly, or demand exponentially smaller
error and pay for it. Random sampling already approximates acceptance; the needed
advance is deterministic construction. A circuit-specific adaptive quadrature rule is
not automatically a single PRG fooling all circuits. Stop if either its proof of accuracy
or its construction assumes the unavailable SAT/counting solution.

## Supplementary code and current boundary

[check_accounting.py](data/check_accounting.py), with fixed seed 20261004 and only Python
stdlib, checks branch factors, parity counts for 3..12 inputs, selector accounting,
the read-input exponent correction, 1,000 finite budget trees, and an adaptive
three-leaf cost/error identity.
[Saved output](data/check_accounting.txt) records the results. These are checks of the
displayed arithmetic and finite semantics, not evidence that the global dichotomy holds.
The paper recurrence and its selector obstruction are the substantive attempted results.
Next work should specify a discoverable semantic certificate and search for a circuit
family escaping both its terminal solver and a paid restriction rule. Coverage remains
open; no exhaustive classification or independent novelty claim is made.

[darwiche02]: ../sources.md#darwiche02
[fgk09]: ../sources.md#fgk09
[williams13]: ../sources.md#williams13
