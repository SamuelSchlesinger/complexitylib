# Why unrestricted MOD3 needs a different potential

Research audit, 2026-10-04. The arguments below are paper proofs, not
new Lean declarations. They obstruct extensions of particular proof mechanisms;
they do not refute a stronger circuit lower bound. No bound greater than `n` for
the full signed AND/OR/XOR/MOD3 basis is established here.

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

[cklm17]: ../sources.md#cklm17
[cgpt06]: ../sources.md#cgpt06
