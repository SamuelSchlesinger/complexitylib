# Why the proposed evaluator fits in logarithmic space

[Return to the main account](../index.md).

Theorem 11.1 must implement the **same actual estimator** analyzed in
Theorem 9.8. For each fixed environment and statistical budget, its values,
lists, port orders, and structural tests are fixed independently of the
requested numerical digit. With description length $B$ and top budget
$M=O(B)$, a request at digit clock $t$ must halt using $O(B+M+t+1)$ space
on every environment. Statistical accuracy is unnecessary for termination.
Sections 10–11 supply the numerical and controller certificates for this
claim. [oai26][oai26]

**Exact streams from finite computations.** Normalize values to $[-1,1]$.
Lemma 10.1 starts with deterministic integers satisfying
$|N_t(z)-2^tz|<2$ and defines

$$
z_0=N_0(z),\qquad z_t=N_t(z)-2N_{t-1}(z).
$$

These digits lie in $\{-6,\ldots,6\}$. Their partial sum through $T$ is
$2^{-T}N_T(z)$, so they represent exactly $z$, with tail at most
$6\cdot2^{-T}$. Residues modulo $16$ determine each bounded difference;
the full integers need not be retained. Crucially, $N_{t-1}$ uses its own
place convention. The finite approximations need not themselves be nested.

Lemma 10.2 evaluates the requisite Boolean circuits by keeping child-choice
paths and bounded pending results. Absolute gates and operand places are
regenerated in shared scratch, without graph queries. Saving an absolute
address at every gate would defeat this accounting.

Multiplication illustrates the numerical certificate (Lemma 10.4).
Group pairs of input places by $r\le\min(i,j)<2r$, for dyadic $r$, plus
a zero band. Retain terms only through
$i+j\le t+h_\circ+\lfloor r/4\rfloor$. Geometrically summable omitted
tails and floor errors give the required approximation. Residue circuits
discard irrelevant high multiples. Their accumulated path through band $r$
costs $O(\log^3(r+2))=O(r+1)$, whereas every queried input there satisfies
$j\le t+h_\circ-3r/4$. Thus the clock gap pays for the path.

Reciprocal evaluation allows long retained words (Lemma 10.5).
On a fixed positive interval, form the prefix through
$k=\lfloor t/2\rfloor+c$, write $x=x^0+e$, and approximate a normalized
reciprocal by $\alpha+\beta e$. The remainder is $O(e^2)=O(2^{-2k})$.
Computing a coefficient digit can retain $O(t+1)$ prefix and arithmetic
bits, but original-input queries then have $j\le t/2+O(1)$, which pays
for them. Release that word before querying late suffix digits; repeated
coefficient requests rebuild it. Calling this operand-dependent word
“scratch” would not make its suspended storage free.

Finite indexed ranks, balanced sums, scales, and clipping preserve these
bounds. Theorem 10.9 exports, at descriptor slack $d$,

$$
j\le t+cd,\qquad \ell_{\rm local}\le ad+b(t-j).
$$

Structural tests use fixed $O(d)$ precision and buffered thresholds
(Lemma 10.8); they do not attempt exact real equality or change the
estimator when the output clock changes. A numerical rank circuit may
select different truncated operands at different clocks, while its exact
semantic list and rank stay fixed. [oai26][oai26]

**One cursor, with explicit return contracts.** Restoring tests and digit
queries return a bit or bounded digit and restore the cursor. A paired
motion returns an endpoint and a short inverse port. A terminal motion
provides no return address; an excursion visits its endpoint, performs a
pure local action, and returns.

For a product $\mathcal F(x,z)\mathcal B(z,y)$, the paired correction
moves the cursor from $x$ to $z$. The right query uses its common table
tuple, which contains no saved $x$; the inverse port restores $x$.
Factor digits are requested separately. Terminal paths have at most one
last unbalanced delegation, followed only by local label completion.
Excursions keep immediate choices and inverse tokens along that path,
then erase deeper records before an earlier inverse motion. No endpoint
action starts another graph query while the entire unbalanced spine
remains live (Lemma 11.8).

At small slack, even a $\log B$-bit saved fingerprint index per comparison
would be too expensive. Lemmas 9.9 and 11.9 use one shared **counted
$B$-bit vector** $V$. Visit $v$ to flip $V_{k(v)}$, visit $w$ to xor
$V_{k(w)}$ into a result bit, then repeat both visits. The two reads
cancel their arbitrary initial contents, leaving exactly
$\mathbf1_{k(v)=k(w)}$, and the flips restore $V$. Nested calls must
restore arbitrary incoming $V$ and choose paths independently of it.
Only phase and result bits survive; keys are recomputed at endpoints.
At larger slack, an exact identifier comparison's index costs $O(d)$.
The arbitrary-state cancellation is related to transparent catalytic
programs of Buhrman, Cleve, Koucký, Loff, and Speelman; the four-visit
identity and its nesting contract are the manuscript's specific use.
[oai26][oai26] [buhrman14][buhrman14]

**Incoming access traverses a raw program.** A raw
program state contains the cursor and delimited caller records. Lower
numerical, cap, rank, and paired procedures are opaque transitions;
their internal working configurations are not copied into this graph.
Marked local edits, restoring branches, and paired steps give bounded
predecessor cases. A value test and a cursor-changing step are separate
instructions (Definitions 11.2–11.3; Lemma 11.4).

Synthetic predecessor candidates can contain fabricated flags. Pure
guards therefore check types, ranges, allowed call recipes, lengths,
and every ancestor-to-query bound before executing a lower query.
Every such query starts at canonical entry; port-dependent calls freshly
check semantic presence. Holes return zero or fail without movement;
baseline and rank padding retain their separately prescribed values. Guards ensure safety
on artificial states; the designated executions must already satisfy
their certificates before guards are added.

The resulting finite graph has outdegree at most one. The component of
a success halt is a tree: a directed cycle cannot share a component
with a sink. Rotate incident edges and flip across them to traverse one
contour, adding a root sentinel for an isolated halt. This is the
forest permutation of Cook and McKenzie, Proposition 1. Mark one
occurrence per canonical initiation. Forward/backward next-mark
operations enumerate exactly the valid row ports reaching the endpoint,
without saving its address or a contour-length counter. Fixed incoming
caps then supply short inverse ports (Lemmas 11.5–11.6).
[oai26][oai26] [cook87][cook87]

Incoming score ranks need more than a capped list (Lemma 11.7).
A success state contains both endpoint and quantized score. Tour each
score's component, in descending score order, saturating the count at
the fixed desired rank. During an inverse tour, the score field is
replaced by an earlier partial suffix; no final score or endpoint copy
is retained. Building digits from least to most significant leaves only
$O(1+(t-j)_+)$ suffix bits above a place-$j$ query. The full word survives
only structural calls, whose clock is zero. Recover it at the sentinel
before decrementing the score. Zero padding supplies missing ranks.
[oai26][oai26]

**Regeneration and concrete certificates.** Lemma 11.10 orders the actual
recipes: constituent tests, intrinsic visits, outer validity, comparisons,
bucket sums, ranks/compression, list lookup, and final wrappers have
separate dependency strata. In particular, validity never asks for the
bucket, shortlist, gate, or cap it helps define. Descriptor loops keep
$O(d)$ indices; sums use balanced arithmetic rather than a retained
high-precision accumulator. The resulting raw bound is
$c_{\rm str}d+c_{\rm num}(t-j)$, with overshoot $j-t\le c_{\rm dig}d$.

Lemma 11.11 regenerates absolute tuples from the top parameters and
active records. A root boundary uses only a constant tag.
Stored immediate choices determine stages, rates, suffixes, and effective
environment transformations without needing an abandoned cursor.
A table tuple specifies an entire table; forward and inverse motions
regenerate the same tuple. Its program graph is independent of an externally
fixed originating row or ancestral transformation word.
Lower-budget procedures ignore later *effective* salt blocks; endpoint
actions use their invoking comparison's salt without changing lower
paths. Physical replay may read differently indexed master bits to
derive that effective environment. [oai26][oai26]

**One potential suffices for the final accounting.** Choose constants
$K_0>S+1$ and $K_1>2(K_0+S+1)$ for the finite number $S$ of strata, and set

$$
w=K_1(1+M)-(K_0+s)d.
$$

Descending a stratum, moving to the preceding prefix of slack $2d$,
or calling a child of budget at most $M-d$ decreases positive integer
$w$ by $\Omega(d)$. Definition 11.3 then takes the form

$$
w'<w,\qquad j-t\le a'(w-w'),\qquad
\ell_{\rm raw}\le a_0(w-w')+b_0(t-j).
$$

The overshoot bound remains essential when accounting for copies.
For a fixed raw-copy factor $k$ and bounded metadata cost $c_0$, choose

$$
D\ge kb_0,\qquad
A\ge ka_0+(D-kb_0)a'+c_0.
$$

Then $k\ell_{\rm raw}+c_0\le A(w-w')+D(t-j)$ even when $j>t$.
Only the local raw chain is copied; an older physical stack segment or
a lower procedure's internal state is never copied again. This prevents
recursive multiplication of the constants (Lemma 11.4).

With $\Phi(w,t)=Aw+Dt$, every suspended physical segment consequently obeys

$$
0\le\ell_i\le\Phi(w_i,t_i)-\Phi(w_{i+1},t_{i+1}).
$$

Choose positive $A,D$ satisfying these constraints and covering the
innermost intrinsic record. Writing $\Phi_i=\Phi(w_i,t_i)$, the physical stack telescopes:

$$
\sum_{i=0}^{r-1}(\Phi_i-\Phi_{i+1})+\Phi_r+O(1)=\Phi_0+O(1).
$$

Nonnegativity also gives
$\Phi(w_i,t_i)\le\Phi(w_0,t_0)$, hence
$t_i\le\Phi(w_0,t_0)/D$. Thus this one potential bounds both the stack
and every descendant clock; the manuscript's second potential is
unnecessary for this last deduction.

Strictly decreasing $w$, finite local loops, and finite success-root
contours establish totality, including predecessor probes and inaccurate
environments. Shared cursor, environment, catalyst, scratch, and scan
counters occur once. Scratch retains nothing across graph calls; marked
record heads avoid per-frame absolute pointers. Input positions are
regenerated, and the physical input head stays between real endmarkers,
including on synthetic probes. The complete bound is
$O(B+M+t+1)=O(B)$ for the application. This is a reduction of the
manuscript's accounting, resting on its concrete Lemmas 11.8–11.11;
generic reversible simulation alone does not supply those certificates.
[oai26][oai26]

[oai26]: ../sources.md#oai26
[buhrman14]: ../sources.md#buhrman14
[cook87]: ../sources.md#cook87
