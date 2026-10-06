# Three investigations from the checked circuit library

Parent: [MCSP from the circuit lower-bound library](../index.md).
Companion: [constructive uses of the proofs](constructive.md), including
counterexample finders, optimal-circuit recognition, and local generators.
Use `n` for inner arity, `N=2^n`, and `s` for the inner threshold.
Here `C_DM` charges AND/OR gates and makes NOT, identity, and constants free;
`M[n,s](T)=1` means `C_DM(T)≤s`. Outer unrestricted circuits have binary gates
and arbitrary fanout. Exact-cost arguments below concern this inner model;
an asymptotic basis simulation does not preserve their exact threshold.

**Outcome.** Repetition gives unusually rigid slices, but those slices admit
linear-size recognition. Counting rules out the direct low-entropy frontier
premises in the sparse regime. A useful next theorem is an interface-capacity
lemma for the actual projections of exact-cost tables; superlinear size still
requires an MCSP-specific bound on repeated use of the charged gates.

**Status convention.** “Checked” identifies existing Lean declarations or the
separate checked research artifact, not a newly checked public library theorem.
“Paper deduction” includes a proof here. “Finite test” checks only the stated
small instances. “Open” identifies the remaining hypothesis, without a novelty
claim. Prior interface work is credited where reused [optimality26][optimality26].

## 1. Exact-cost repetition: powerful rigidity, linear outer consequences

**Checked.** In
[SubcubeRepetition.lean](../../../Complexitylib/Algebraic/LowerBound/MCSP/SubcubeRepetition.lean),
`costComplexity_muxTarget_self` gives `C_DM(mux(u,u))=C_DM(u)`.
`costComplexity_muxTarget_ge_add_one` gives, when `u≠v` and one branch has
positive cost, `C_DM(mux(u,v))≥max(C_DM(u),C_DM(v))+1`.
The proof follows a selector-dependent path to a charged gate and deletes a
charged gate under either selector restriction [complexitylib26][complexitylib26].

**Checked.** Put `E=exactCostSet(n-1,s)`, with `s≥1` and `E` nonempty.
For each `t∈E` and arbitrary `u` of length `N/2`,

`M[n,s](u,t)=1  ⇔  u=t`, and `M[n,s](t,u)=1  ⇔  u=t`.

These are `mcspCostScalar_pairTruthTable_left_eq_true_iff` and its right version.
On the promise `E×E`, MCSP is equality. Fixing the second half to `t` gives
the total minterm `AND_j [u_j=t_j]` on the first half, not a hard arbitrary
function. The exact-cost and positivity assumptions must remain in the statement.

**Checked research artifact.** The stronger arbitrary-repetition statement is
`cost_le_iff_eq_repeatTarget` in [RepeatedAnchor.lean](../data/RepeatedAnchor.lean).
For `1≤k≤n`, let `P=2^(n-k)` and let `t` have exact positive cost `s` on
`n-k` inputs. Fix the all-zero selector block of a length-`N` table to `t`.
Then the only accepted completion is the repetition of `t` in all `2^k` blocks.
The artifact is outside the public import graph; it uses the existing strict
mux lemma and checks the all-zero anchor cofactor explicitly.

**Paper deduction explaining the induction.** Each successive ancestor of the
anchor has cost at least `s` by restriction and at most `s` by the assumed
completion bound. If its two children differed, the positive exact-cost child
would force cost at least `s+1`. Thus the children agree at each level.
Conversely repetition preserves cost. Fixing a different selector block follows
by complementing selector inputs, which is free for `C_DM`.
The resulting outer slice is one minterm on `N-P` free bits, with De Morgan
binary cost exactly `N-P-1` when `N-P≥1`. A balanced AND tree recognizes it.
At `s=0` the selector function itself is a counterexample to rigidity.

**Checked and paper consequences.** The diagonal `(t,t)` has sensitivity `N`
by `sensitiveCoordinates_mcsp_pairTruthTable_eq_univ`. Consequently:

- The checked De Morgan formula lower bound is `N` leaves.
- The checked bounded-sharing bound is `N≤(k_share+1)(S+k_share+1)`.
- A paper deduction for any outer fan-in-two DAG is `S≥N-1`: all `N`
  inputs are essential, and a connected output cone with `S` binary gates
  has at most `S+1` distinct input sources. Free unary gates do not alter this count.
- A paper deduction is deterministic decision-tree complexity exactly `N`:
  at the diagonal, leaving a coordinate unread cannot distinguish its one-bit flip.

Full sensitivity does not force `S=ω(N)`: `AND_N` has full sensitivity at
`1^N` and precisely `N-1` binary gates. Repetition additionally exhibits an
actual MCSP restriction attaining this linear behavior, so a proof must use
relationships between slices, rather than charging each slice independently.

**Paper deduction: using every repeated anchor still saturates.** Let `A` be all
two-block diagonals from `E` and `B` their one-bit-flip neighbors. Every edge
goes from YES to NO, `|edges|=N|A|`, and each `b∈B` neighbors at most two
diagonals: its unequal halves identify the two possible anchors. Hence

`N ≤ |edges|²/(|A||B|) ≤ 2N`.

With at least four repeated blocks, distinct diagonals have Hamming distance
at least four, their one-bit neighborhoods are disjoint, and this measure is
exactly `N`. This bounds this specific Khrapchenko witness construction;
it is not an upper bound on MCSP formula complexity or other witnesses.

**Checked cut information.** `mcsp_singleCut_card_exactCostSet_le` supplies
`log₂|E|≤|forward|+|backward|` for every cut separating the two halves,
over any outer Boolean gate basis. This is useful layout information, but
`log₂|E|≤N/2`, and several cuts can reuse the same signals. Likewise, the
checked arbitrary-block subfunction theorem gives only the projections
actually realized by `E`, not every possible label on an arbitrary block.

## 2. Sparse YES sets versus the exact frontier hypotheses

**Paper deduction: an explicit description bound.** Normalize free unary gates
to signs on wires. Pad to `s` charged gates, allowing unused gates. Each gate
has two operation choices and two signed predecessors among at most `n+s+2`
sources, including constants; the output is a signed source. Therefore, for
`n,s≥1`, the YES set `Y` satisfies

`|Y| ≤ 2(n+s+2)[8(n+s+2)²]^s = 2^H`,
`H = log₂(2(n+s+2)) + s[3+2log₂(n+s+2)] = O(s log(n+s))`.

This deliberately overcounts circuits. It bounds functions despite the
unbounded number of syntactically free NOT gates. For other fixed finite
binary bases, analogous counting changes constants; exact repetition is not
being transferred to those bases. For `s=0`, retain the separate `O(log n)` term.

**Paper deduction: missing patterns.** For `Y⊆{0,1}^N` with `0<|Y|<2^N`,
choose `t=floor(log₂|Y|)+1≤N`. Its projection on any chosen `t` coordinates
has fewer than `2^t` patterns. Fix a missing pattern and leave all other
coordinates free. This is a NO cube of dimension `D=N-t`.
In particular, whenever `H<N`, there is a NO cube of dimension at least
`N-floor(H)-1`. This is existence, not an efficient algorithm to find the pattern.

Thus `s log(n+s)=o(N)` gives `D=N-o(N)`. Examples include `s=n^c` for fixed
`c>0` and `s=N^β` for fixed `0<β<1`. For a gap promise, apply the count at
the *upper* NO threshold: excluding every circuit up to that threshold makes
every point of the cube a promised NO instance. Counting only the lower YES
threshold could leave promise-gap points and does not establish a NO cube.

**Checked premise audit.**
[Frontier/Main.lean](../../../Complexitylib/Circuits/Frontier/Main.lean)
requires one-sided rectangle-freeness of the accepted set, `log K=o(N)`,
and logarithmic density deficit `N-log₂|accepted|=o(N)`.
[Rectangle.lean](../../../Complexitylib/Circuits/Frontier/Rectangle.lean)
forbids an accepted rectangle with both sides of size at least `K`, for every
coordinate split. It does not forbid rejected rectangles.
The older dense cut criterion assumes `|accepted|≥2^(N-2)`.
These are stronger density requirements than mere nonemptiness
[complexitylib26][complexitylib26].

**Paper deduction: test the two polarities separately.**

| Accepted set | Density in the sparse regime | Rectangle obstruction |
| --- | --- | --- |
| `Y`, the MCSP YES set | Deficit at least `N-H=N-o(N)`; fails | A NO cube alone says nothing about YES rectangles |
| `Yᶜ`, the MCSP NO set | Density tends to one; passes | Split the `D` free coordinates in half: a YES rectangle has both sides at least `2^floor(D/2)` |

For the complement, rectangle-freeness needs `K>2^floor(D/2)`, contradicting
`log K=o(N)`. Thus neither polarity meets the complete theorem hypotheses.
The two-sided sumset-disperser premise is also impossible: a NO affine cube
`a+V` gives `V+(a+V)=a+V`, with both sets of size `2^D`.
This sharpens the obstruction noted in the prior
[hard-functions investigation](../../circuit-lower-bound-frontiers/hard-functions/index.md).

**Paper deduction: transformations do not repair sparsity.** Any bijection of
the outer cube preserves `|Y|`, so the missing-pattern argument supplies a
new coordinate NO cube even after that bijection. Affine bijections also
transport the displayed affine sumset witness directly. A particular coordinate
rectangle need not remain a coordinate rectangle; the recounting argument is
what justifies the stronger statement. The balancing gadget
`B(T,z)=M[n,s](T) XOR z` has density `1/2`, but `NOcube×{1}` is an accepted
cube of dimension `D`, so it fails the small-`K` rectangle condition as well.

**Paper deduction: what changes near the Shannon scale.** At `s=Θ(N/n)`,
the description exponent is only `H=Θ(N)`, not necessarily `o(N)` or even
less than `N`. The bound can become vacuous. If the *actual* count still
satisfies `log₂|Y|≤(1-δ)N` for fixed `δ>0`, then `D≥δN-1` and both
obstructions remain. Escaping this argument requires `|Y|=2^(N-o(N))`.
That necessary condition proves neither rectangle-freeness nor hardness;
above the maximum inner complexity, MCSP is the constant YES function.

**Open transfer, with quantitative obligations.** A restriction retaining `m`
outer variables has at most `|Y|` accepted assignments. For its YES set to
have density `2^-o(m)`, necessarily `m≤H+o(m)`. Thus in the sparse regime
one cannot obtain a dense YES restriction on `m=Θ(N)` variables. A dense
complement restriction must instead prove its rectangle condition afresh.
The repeated-anchor slices in Section 1 supply minterms, not such a witness.

More generally, suppose a known hard family `h_m` factors as
`h_m=M[n,s]∘R`, with a binary circuit of cost `r` for the entire `N`-output
map `R`. Then `C(M[n,s])≥C(h_m)-r`. A frontier bound `C(h_m)≥L m-o(m)`
only transfers `Lm-r-o(m)`. Restrictions have `m≤N`; a larger fixed `L`
therefore supplies at most a stronger linear bound. To obtain `ω(N)` this
way needs `Lm-r=ω(N)`, plus the exact total factorization. Both are open.

**Published alternative criterion.** Local PRGs use sparsity constructively:
if every output of a distribution generator has inner cost at most `s`,
then MCSP accepts that distribution with probability one, while uniform
acceptance is at most `2^(H-N)`. Any distribution fooling a proposed outer
size-`S` class with error below `1-2^(H-N)` therefore excludes MCSP from
that class. This is the local-PRG mechanism of Cheraghchi, Kabanets, Lu,
and Myrisiotis [cklm20][cklm20]. Turning the repository's linear hard family
into the necessary generator and inner-cost guarantee is a separate open step.
The library also supplies a constant-error average-case bound for its unpadded
extractor. The [constructive companion](constructive.md) derives a randomized
refuter and compares that bound with the stronger NW reconstruction requirements.

## 3. A many-interface route with its reuse cost exposed

**Paper deduction; next useful lemma.** Let `B` contain `p` coordinates in
the left half and let `A_B={t|B:t∈E}`. The checked equality slice implies
that every `a∈A_B` is a total minterm cofactor of `M[n,s]` on `B`: fix
the right half to a witness `t` and the left coordinates outside `B` to `t`.
This is stronger information than counting distinct subfunctions alone.

Write `x∈{0,1}^p` for this block and `w` for its independent complement.
Suppose an actual outer circuit region factors the total function as

`M(x,w)=D(x_R,G(x,z(w)),w)`.

Here `R` lists all `d` raw block bypasses, `G` outputs `r` computed bits,
and `z(w)` lists `b` distinct incoming context signals independent of `x`.
Use the actual context image `Z={z(w)}`. Put `h=p-d`, and for each bypass
value `u` let `A_u` be the hidden-coordinate labels from `A_B` above `u`.
For `0≤r<h`, the proposed exact capacity inequality is

`max_u |A_u| ≤ |Z|(2^r-1) ≤ 2^b(2^r-1)`.  **(Capacity)**

**Proof on paper.** Fix `u,z`. A target `a∈A_u` realized under context `z`
must be a singleton fiber of the map `v↦G((u,v),z)`; otherwise its minterm
cofactor could not distinguish two inputs. A map from `2^h` points to fewer
than `2^h` labels has at most `2^r-1` singleton fibers. Union over the actual
contexts and then maximize over `u`. This proves (Capacity), including the
impossibility of a nonempty `A_u` when `r=0<h`.
If `A_B` is the whole cube and `1≤r<h`, it gives `b≥h-r+1`, recovering the
earlier capacity lemma [optimality26][optimality26]. Without full projections,
use the displayed `A_u`; their required size is a new MCSP-specific obligation.

**Open formalization target.** Formalize (Capacity) with the actual projection
set and total cofactor hypothesis, then instantiate that hypothesis from
`mcspCostScalar_pairTruthTable_left_eq_true_iff`. This is a bounded next lemma
with a complete proof above. A source passing through the region and returning
cannot be called independent context. A prefix leaving all original inputs
available to its suffix has `d=p`, making the capacity bound vacuous.
Restricting to a reachable promise is not automatically a full-cube minterm.

**Paper deduction: the valid global charge.** For each interface `i` with `1≤r_i<h_i`,
let `ell_i` be the smallest nonnegative integer with
`max_u|A_(i,u)|≤2^ell_i(2^r_i-1)`; then `b_i≥ell_i`.
Choose one real incoming wire per distinct context source and charge its
receiving gate, allowing raw outside inputs. Let `a_i(v)` count these wires;
then `Σ_v a_i(v)=b_i` and `a_i(v)≤2` for binary gates.
For weights `λ_i≥0`, set `Q=Σ_i λ_i ell_i` and
`M_load=max_v Σ_i λ_i a_i(v)`. Finite double counting gives

`Q ≤ Σ_v Σ_i λ_i a_i(v) ≤ S M_load`, hence `S≥Q/M_load` if `Q>0`.

This is the prior weighted charge theorem [optimality26][optimality26], now
fed by the exact-cost projection set. Source charges require computed context
gates; receiver charges correctly include raw context inputs without treating
free wires as gates. Neither choice eliminates multiplicity.

**Paper counterexample.** On `2m+1` inputs let `m=2^L`,
`g_j=y_j XOR t`, `e_j=[x_j=g_j]`, and `F=AND_j e_j`, using a balanced tree.
This full-binary-basis circuit has `3m-1` gates. Every dyadic block of `p`
`x`-inputs has a one-output equality module with `d=0`, `r=1`, `b=p`,
and all `2^p` minterm cofactors. The `L` scales give `Q=mL`, while every
`g_j` or receiving `e_j` is charged at every scale: `M_load=L`, `Q/M_load=m`.
For arbitrary weights, put `μ_j=Σ_(B∋j)λ_B`; then `Q=Σ_j μ_j≤m max_j μ_j`.
Reweighting cannot repair this example. Its internal-region charge also
saturates: each region has `2p-1` gates, all inside one pool of `2m-1` gates.

**Open MCSP-specific requirement.** For every circuit computing MCSP, force
genuine interfaces, sufficiently rich `A_B`, and a charge assignment with
`Q/M_load=ω(N)`, or prove that failure to find such interfaces already costs
`ω(N)` gates. Minterms or optimality alone cannot supply this, as the equality
example shows. If one could force `Θ(N)` demand at each of `L` scales and
`M_load=o(L)`, the required ratio would follow. With blocks only up to
`q=poly(n)`, dyadic scales provide merely `L=O(log n)=O(log log N)`.
Even constant load then yields only `Ω(N log log N)`, a preliminary target;
it must not be substituted for a stronger magnification threshold.

## Finite checks and scope

**Finite test.** [check_routes.py](data/check_routes.py), with
[saved output](data/check_routes.json), checks 131,328 anchored completions
at exact inner cost one; all 2,080 nonempty subsets of the six-cube of size
at most two for the missing-pattern lemma; all 65,536 maps from eight points
to four labels for singleton capacity; and eight nested-equality scales.
It also checks the zero-cost counterexample and repeated-anchor neighbor counts.
Run `python3 -B research/mcsp-circuit-vantage/directions/data/check_routes.py`.
These checks support identities and falsifiers, not asymptotic MCSP lower bounds.

[cklm20]: ../sources.md#cklm20
[complexitylib26]: ../sources.md#complexitylib26
[optimality26]: ../sources.md#optimality26
