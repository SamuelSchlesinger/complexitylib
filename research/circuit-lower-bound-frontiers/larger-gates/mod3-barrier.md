# MOD3: affine obstructions and a restricted superlinear bound

Research audit, 2026-10-04. The half-dimension theorem in Section 2 and the
signed affine-cube construction in Section 5 are now Lean-checked. The other
arguments, including the complete circuit tradeoff, remain paper proofs.
They obstruct extensions of particular proof mechanisms;
they do not refute a stronger circuit lower bound. No bound greater than `n` for
the full signed AND/OR/XOR/MOD3 basis is established here.
Section 5 instead uses MOD3 as the **target**, with no MOD3 gates allowed, and
derives a restricted superlinear gate bound from the affine geometry.

The model permits finite acyclic Boolean circuits of arbitrary depth, fan-in and
fanout, with repeated slots. Every gate costs one. In addition to the signed
AND/OR/XOR basis, allow the standard gate
`MOD3_zero(y) = [sum y_i = 0 mod 3]`. The counterexample in Section 3 uses precisely
this predicate, without a free modular offset or a generalized readout.

## 1. Even one MOD3 gate can require linearly many affine restrictions

Let `R(x)=sum_i x_i mod 3` on `m` independent Boolean variables. For every nonempty
affine subspace `W` of codimension `k` in `F_2^m` and every residue `r`,

\[
 \left|\Pr_{x\in W}[R(x)=r]-\frac13\right|
 \leq \frac23\,2^k\left(\frac{\sqrt3}{2}\right)^m.
\]

**Proof.** Let `omega` be a primitive complex cube root of unity and let
`chi_a(x)=(-1)^(a dot x)`. Under the uniform distribution on the full cube,

\[
 \mathbb E[\omega^{R(x)}\chi_a(x)]
   =\prod_{i=1}^m\frac{1+(-1)^{a_i}\omega}{2}.
\]

Each factor has magnitude `1/2` or `sqrt(3)/2`; thus the product has magnitude at
most `(sqrt(3)/2)^m`. If `W=t+V`, its indicator is
`2^(-k) sum_{a in V^perp} chi_a(x+t)`. Divide the resulting expectation by
`Pr[W]=2^(-k)` and apply the triangle inequality to its `2^k` terms. Finally,
`[R=r]=(1+omega^(R-r)+omega^(2(R-r)))/3` proves the claim.

In particular every residue occurs on `W` whenever

\[
 k<m\log_2(2/\sqrt3)-1
   =0.2075187496\ldots m-1.
\]

Consequently, making the Boolean gate `MOD3_zero` constant, in either color,
can require linearly many independent affine equations. This rules out a
universal extension of the existing affine-pairing proof that pays a fixed
number of affine equations per MOD3 gate, independent of fan-in. It is stronger
than the one-hyperplane obstruction in [the earlier audit](followup-audit.md#5-mod3-an-exact-obstruction-and-an-exact-compression-lemma).

The qualitative low-codimension equidistribution argument is classical:
Chattopadhyay, Koucky, Loff and Mukhopadhyay prove it within the proof of
Theorem 5.17 of *Simulation Beats Richness: New Data-Structure Lower Bounds*,
ECCC TR17-170 (2017), printed pp. 34-35. The explicit constant above is an
elementary specialization obtained directly from the displayed product
[cklm17][cklm17].

## 2. Fixing the entire residue costs at least half the dimension

There is a sharper elementary statement for a more restrictive operation:
if `R` is constant as an `F_3`-valued function on a `d`-dimensional affine
subspace of `F_2^m`, then `2d <= m`. This applies to a constant accepting
restriction of `MOD3_zero`; a constant rejecting restriction need not fix a
single residue and is covered instead by Section 1.

**Proof.** Parametrize the subspace injectively by `t in F_2^d`. Write its
coordinates as `x_i(t)=a_i+(v_i dot t)` over `F_2`. Viewed in `F_3`, this is

\[
 x_i(t)=\frac{1-(-1)^{a_i}\chi_{v_i}(t)}2.
\]

The characters `chi_v` are linearly independent as functions into `F_3`:
their character matrix times its transpose is `2^d I`, which is invertible
in characteristic three. Constancy of `sum_i x_i(t)` therefore forces
`sum_{i:v_i=v} (-1)^{a_i}=0` in `F_3` for every nonzero `v`.
Each occurring nonzero character must have at least two coordinate occurrences.
The vectors `v_i` span a space of dimension `d`, because the parametrization
is injective, so at least `d` distinct nonzero characters occur. Hence `m>=2d`.

The factor two is attained by complementary coordinate pairs
`(t_1,1-t_1,...,t_d,1-t_d)`, whose total Hamming weight is the constant `d`.

**Checked statement:** `Algebraic.BooleanCube.ModThree.two_mul_finrank_le_of_constant`
in [`ModThree.lean`](../../../Complexitylib/Algebraic/BooleanCube/ModThree.lean).
Its hypothesis fixes the full `ZMod 3` residue, not merely the Boolean MOD3 output.
The proof uses linear independence of characters over `ZMod 3` and counts repeated
nonzero coordinate forms. The kernel and supported-block corollaries are checked too.

## 3. Balanced output gates may retain direct primary inputs

Consider the two-gate circuit on three primary bits

```
z = NAND(x2,x3)
y = MOD3_zero(x1,z,z).
```

Since `x1+2z=0 mod 3` exactly when `x1=z`,

`y = x1 XOR (x2 AND x3)`.

This output is balanced, nonlinear, and zero at the all-zero input. Nevertheless
its final MOD3 gate has a direct primary slot. It refutes the extension to MOD3
of the conjunction lemma saying that a balanced nonlinear output cannot have
any direct primary literal. Repeating `z` is allowed by the circuit model.

It also gives a small permutation `(x1,x2,x3) -> (y,x2,x3)`. This is not a
counterexample to the inversion bound: the other output coordinates are primary
projections, and the permutation has only one nonlinear component modulo affine
functions. Its role is to isolate the failed local inference.

## 4. Communication does not remove this obstacle for free

The earlier audit already exhibits `r` independent MOD3 residues followed by one
AND gate whose exact one-way communication requires all `3^r` states. Thus a
generic compression from ternary states to one bit per gate is false. Both
that construction and the obstructions above survive arbitrary depth and fanout.

Classical unrestricted-depth linear gate bounds for circuits consisting only of
MOD_m gates are proved by Chattopadhyay, Goyal, Pudlak and Therien in
*Lower bounds for circuits with MOD_m gates*, FOCS 2006, pp. 709-718,
DOI 10.1109/FOCS.2006.46 [cgpt06][cgpt06]. Their author-hosted manuscript
studies Boolean solutions of modular linear systems. Its arbitrary-depth
gate bound concerns computing MOD_q when `gcd(m,q)=1`; its superlinear wire
bound has a constant-depth restriction. Neither statement supplies the desired
unit-gate bound for the enlarged AND/OR/XOR/MOD3 basis. In particular, the
MOD2 target is already one gate in that enlarged basis.

A useful next potential must charge the interaction of primary modular forms
with already computed Boolean signals, or exploit a property of the actual
target under mixed-characteristic constraints. Neither a constant-cost affine
kill step nor the balanced-output exclusion above can serve that role unchanged.
No uninstantiated target-hardness premise is being presented as a new result.

## 5. A positive use: few conjunctions feeding later conjunctions

**Status:** a paper proof using the classical Razborov--Smolensky approximation
method, independently audited in this research session. Its affine geometry is
Lean-checked; the circuit-freezing and approximation transfer are not yet formalized.
bibliographic novelty and optimality of this parameter tradeoff remain unresolved.

Return to the signed unbounded AND/OR/XOR signature, equivalently affine Boolean
gates and signed, optionally complemented conjunctions. Let `h` count conjunction
gates, and let `q` count those having a directed path to another conjunction with
only affine gates internally. Direct edges qualify. These are the nonterminal
conjunctions in the nonlinear dependency graph; the original circuit is acyclic.
The definition is syntactic, so affine cancellations can harmlessly overcount `q`.
All arities, signs, repetitions, fanout, and total depth are unrestricted.

**Paper theorem.** There is an absolute `c>0` such that every such circuit computing
any Hamming-weight residue predicate modulo three, or its complement, satisfies

```
(q+1) * (log2(h+2))^2 >= c*n.                              (S)
```

In particular, `h+2 >= 2^{Omega(sqrt(n/(q+1)))}`. Thus `q<=sqrt(n)` forces
`2^{Omega(n^(1/4))}` gates, and `q=o(n/log^2 n)` excludes polynomial-size
circuits. Total gate count is at least `h`; this is not a wire bound. The class
allows growing nonlinear depth, but does not contain every constant-depth
circuit: a shallow circuit can have many nonterminal conjunctions. The
restriction on `q` is essential; this is not an unrestricted superlinear bound.

### Freeze only the nonterminal conjunctions

Process the `q` designated gates in topological order. Maintain a nonempty affine
flat on which earlier designated outputs are constant. Every conjunction affecting
an input of the next designated gate is an earlier nonterminal conjunction: take
the last conjunction on the path to that input. Consequently that input is affine
on the current flat. If any literal is nonconstant, fix it to its controlling
value, making the gate constant at a cost of one independent affine equation.
If all literals are constant, no equation is needed.

This leaves a nonempty affine flat `W` of codimension at most `q`. Every remaining
conjunction has affine inputs on `W`; affine closure expresses every circuit
output as an affine function plus an XOR of at most `h` conjunctions of affine
forms. This is a semantic expression used for polynomial approximation, not a
claim that a newly implemented circuit has free affine gates.

### Find a MOD3 copy inside the flat

Set `r=floor(n/(2q+1))` and partition `r(2q+1)` coordinates into disjoint blocks
of size `2q+1`. Write `W=a+V`. Within each block `B`, the vectors of `V` supported
on `B` form a space `V_B` of dimension at least `q+1`: at most `q` linear
constraints remain. Section 2 shows that `a_B+V_B` cannot have constant full
Hamming residue. Choose a supported vector `v_B` whose addition changes that
residue by `delta_B != 0` modulo three.

The directions have disjoint supports, so `phi(z)=a+sum_B z_B*v_B` is an affine
embedding of `F2^r` into `W`, and

```
weight(phi(z)) = weight(a) + sum_B delta_B*z_B (mod 3).
```

Every `delta_B` is `+1` or `-1`. Complement variables with negative coefficients
and absorb constants into the target residue. The restricted target is therefore
an ordinary MOD3 residue predicate on `r` independent bits. The embedding is a
disjoint-support affine cube; it need not be a coordinate subcube. The argument
uses the full-residue lemma, not an assertion about constant Boolean MOD3 outputs.

This embedding is checked as
`Algebraic.BooleanCube.ModThree.exists_signed_cube` in
[`ModThree/Cube.lean`](../../../Complexitylib/Algebraic/BooleanCube/ModThree/Cube.lean).
For any map `R : F2^n -> F2^q` and any `a`, it supplies an injective linear map
`L : F2^floor(n/(2q+1)) -> F2^n` with `R(L z)=0` and the exact signed-residue
identity on `a+L z`. The result also covers redundant equations and zero dimensions.

### Approximate once and apply the classical degree obstruction

A conjunction of affine equations `L_j(z)=b_j` has a random degree-`ell`
approximant over `F2`:

```
P(z) = product_{i=1}^ell (1 + sum_j c_ij*(L_j(z)+b_j)),
```

with independent uniform binary coefficients. It is always correct when every
equation holds. Otherwise each random parity of the nonzero violation vector is
uniform, so the error probability at that point is `2^(-ell)`. This is the
classical Razborov--Smolensky construction [smolensky87][smolensky87].

Use the same at most `h` approximants for all output expressions. With
`ell=ceil(log2(12(h+1)))`, their joint pointwise error is less than `1/12`, and
each output polynomial has degree at most `ell`. To change the surviving residue
predicate to residue zero, fix two cube variables whose sum is the selected
residue. Pointwise error is preserved. Only then average over the random choices
to obtain a deterministic polynomial agreeing with MOD3 on at least `11/12` of
the remaining `m=r-2` inputs.

The classical characteristic-two MOD3 approximation bound implies degree at least
`kappa*sqrt(m)` for absolute `kappa>0` and all `m>=m0`; Bhowmick--Lovett Section
1.2 records the bound with its Razborov--Smolensky attribution
[bhowmick-lovett15][bhowmick-lovett15]. Thus

```
ceil(log2(12(h+1))) >= kappa*sqrt(floor(n/(2q+1))-2)
```

whenever the square-root argument is at least `m0`. Put `R=max(4,m0+2)` and
`L=log2(h+2)>=1`; the ceiling is at most `6L`. If `r>=R`, use `r-2>=r/2` and
`n<4r(q+1)` to obtain (S) with `c=kappa^2/288`. If `r<R`, then
`n<2R(q+1)`, so `c=1/(2R)` suffices. Taking the smaller constant proves (S)
uniformly. No numerical value of `kappa` is asserted.

## 6. The same tradeoff for integer multiplication and division

Here `n` is the bit width of each operand: the original circuit has `2n` input
bits. For division it outputs the unsigned quotient; for multiplication it outputs
the complete `2n`-bit product. The same bound (S), with a possibly smaller absolute
constant, holds for their original conjunction counts `h,q`.

Let `A` be an unsigned `n`-bit integer, `Q=floor(A/3)`, and index bits starting
at zero. Since `A-3Q` lies in `{0,1,2}` and is congruent to `A+Q` modulo four,
divisibility by three has the exact degree-two readout over `F2`

```
[3 divides A] = (1+A_0+Q_0)*(1+A_1+A_0+Q_1).              (R)
```

Indeed a zero remainder is equivalent to `Q=-A mod 4`, whose two bit conditions
are `Q_0=A_0` and `Q_1=A_1 XOR A_0`. Set `A_i=z_i` for even `i` and
`A_i=1-z_i` for odd `i`. Then `A mod 3=sum_i z_i-floor(n/2) mod 3`, so (R)
computes a MOD3 residue on all `n` free bits. For division, fix the divisor to
three (`n>=2`); its zero-divisor convention is irrelevant.

For multiplication (`n>=3`), put `T=2^(n+1)` and fix the second operand to
`C=ceil(T/3)<2^n`. For every `0<=A<2^n`,

```
floor(A*C/T) = floor(A/3).
```

To prove this, write `C=T/3+delta`, where `0<delta<=2/3`. Then
`0<=A*delta/T<1/3`. In `A=3Q+R`, the sum `R/3+A*delta/T` is in `[0,1)`,
proving the identity. Product bits `n+1,n+2` are therefore exactly `Q_0,Q_1`,
which supplies (R) without a padded-input loss.

Freeze the **original** `q` nonterminal conjunctions after these input
specializations. Jointly approximate the two selected outputs using the same
terminal-conjunction approximants. Compose their polynomials with (R) only after
approximation. The degree is at most `2ell`, and the joint pointwise error is
unchanged. The block-cube and MOD3 degree arguments prove (S), losing only a
constant factor.

Appending a readout AND to the circuit itself would be unsound for this
parameter: many formerly terminal conjunctions could become nonterminal at once.
The polynomial composition avoids that reclassification. These integer readout
identities and their application are deductions here, with no novelty claim.

## 7. Finite audits and the next formalization boundary

Run `python3 research/circuit-lower-bound-frontiers/larger-gates/superlinear_checks.py`.
The [finite checker](superlinear_checks.py) verifies the residue-flat bound and
block construction on all 29,210 affine flats in ambient dimensions one through
six, plus 288 seeded larger examples. It also verifies the reciprocal identity
and quadratic readout for all 8,184 operands of widths three through twelve.
These checks are finite evidence, not substitutes for the proofs above or Lean
formalization.

The next reusable Lean layer is the disjoint-block affine-embedding lemma;
it turns a restriction that previously looked like a loss of hardness into a
new explicit hard instance. The remaining layers are the actual-circuit
nonterminal-freezing theorem, pointwise random-polynomial approximation, and the
classical MOD3 degree obstruction. None of those new combined lower-bound
statements is currently in the checked theorem inventory. At `q=Theta(n)`, (S)
does not imply a superlinear gate bound; controlling that regime remains open.

[smolensky87]: ../sources.md#smolensky87
[bhowmick-lovett15]: ../sources.md#bhowmick-lovett15
[cklm17]: ../sources.md#cklm17
[cgpt06]: ../sources.md#cgpt06
