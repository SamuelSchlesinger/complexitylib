# Sources

[Back to the overview](index.md).

Canonical primary sources and prior research, checked on 2026-10-06.
Production repository references are pinned to the audited commit.
The new research artifact is linked separately from that snapshot.

<a id="complexitylib26"></a>

## complexitylib26

Samuel Schlesinger and contributors. *Complexitylib*,
  source snapshot `b030149cd09f755bfead55f473d670f0880eedb0`, inspected locally
  2026-10-06. [Pinned repository](https://github.com/SamuelSchlesinger/complexitylib/tree/b030149cd09f755bfead55f473d670f0880eedb0).
  Primary audited roots:
  [algebraic MCSP](https://github.com/SamuelSchlesinger/complexitylib/blob/b030149cd09f755bfead55f473d670f0880eedb0/Complexitylib/Algebraic/LowerBound/MCSP.lean),
  [canonical MCSP](https://github.com/SamuelSchlesinger/complexitylib/blob/b030149cd09f755bfead55f473d670f0880eedb0/Complexitylib/Metacomplexity/MCSP.lean),
  [blueprint](https://github.com/SamuelSchlesinger/complexitylib/blob/b030149cd09f755bfead55f473d670f0880eedb0/blueprint/src/chapters/metacomplexity.tex),
  [roadmap](https://github.com/SamuelSchlesinger/complexitylib/blob/b030149cd09f755bfead55f473d670f0880eedb0/ROADMAP.md).
  The pinned [dependency file](https://github.com/SamuelSchlesinger/complexitylib/blob/b030149cd09f755bfead55f473d670f0880eedb0/lakefile.toml)
  selects CSLib `311d27ad8458b61e9b7461fc83a480e4be97aef2` and Mathlib
  `728a93eeff833da3173895bb0575752fdc24edb0`; `lean-toolchain` selects
  `leanprover/lean4:v4.35.0-rc3`.

<a id="cklm20"></a>

## cklm20

Mahdi Cheraghchi, Valentine Kabanets, Zhenjian Lu, Dimitrios Myrisiotis. *Circuit
  Lower Bounds for MCSP from Local Pseudorandom Generators*. ACM Transactions on Computation
  Theory 12(3), article 21, 2020. DOI: https://doi.org/10.1145/3404860. Checked full text: ECCC
  TR19-022, revision 1, July 16, 2020,
  https://eccc.weizmann.ac.il/report/2019/022/revision/1/download.

<a id="giikkt19"></a>

## giikkt19

Alexander Golovnev, Rahul Ilango, Russell Impagliazzo, Valentine Kabanets,
  Antonina Kolokolova, Avishay Tal. *AC⁰[p] Lower Bounds Against MCSP via the Coin Problem*.
  ICALP 2019, LIPIcs 132, 66:1–66:15. https://doi.org/10.4230/LIPIcs.ICALP.2019.66.

<a id="hs17"></a>

## hs17

Shuichi Hirahara, Rahul Santhanam. *On the Average-Case Complexity of MCSP and Its
  Variants*. CCC 2017, LIPIcs 79, 7:1–7:20. https://doi.org/10.4230/LIPIcs.CCC.2017.7.

<a id="mmw19"></a>

## mmw19

Dylan M. McKay, Cody D. Murray, R. Ryan Williams. *Weak Lower Bounds on
  Resource-Bounded Compression Imply Strong Separations of Complexity Classes*. STOC 2019.
  https://doi.org/10.1145/3313276.3316396. Checked author PDF:
  https://people.csail.mit.edu/rrw/MCSP-MKTP-stoc19.pdf.

<a id="ops21"></a>

## ops21

Igor C. Oliveira, Ján Pich, Rahul Santhanam. *Hardness Magnification Near
  State-of-the-Art Lower Bounds*. Theory of Computing 17(11):1–38, 2021.
  https://doi.org/10.4086/toc.2021.v017a011.

<a id="cly22"></a>

## cly22

Lijie Chen, Jiatu Li, Tianqi Yang. *Extremely Efficient Constructions of Hash
  Functions, with Applications to Hardness Magnification and PRFs*. CCC 2022, LIPIcs 234,
  23:1–23:37. https://doi.org/10.4230/LIPIcs.CCC.2022.23.

<a id="am25"></a>

## am25

Albert Atserias, Moritz Müller. *Simple general magnification of circuit lower
  bounds*. arXiv:2503.24061v2, June 21, 2025. https://arxiv.org/html/2503.24061v2;
  https://doi.org/10.48550/arXiv.2503.24061.

<a id="chhoprs22"></a>

## chhoprs22

Lijie Chen, Shuichi Hirahara, Igor C. Oliveira, Ján Pich, Ninad Rajgopal,
  Rahul Santhanam. *Beyond Natural Proofs: Hardness Magnification and Locality*. Journal of the
  ACM 69(4), article 25, 2022. https://doi.org/10.1145/3538391. Checked accepted manuscript:
  https://wrap.warwick.ac.uk/id/eprint/170343/2/WRAP-Beyond-natural-proofs-hardness-magnification-locality-22.pdf.

<a id="ilango26"></a>

## ilango26

Rahul Ilango. *SAT Reduces to the Minimum Circuit Size Problem with a Random
  Oracle*. SIAM Journal on Computing, published online June 9, 2026; conference version FOCS
  2023. https://doi.org/10.1137/24M1652568.

<a id="gjk26"></a>

## gjk26

Halley Goldberg, Mandar Juvekar, Valentine Kabanets. *Non-Levin NP-Hardness of
  Implicit MCSP and PAC Learning under Few Assumptions*. ECCC TR26-091, June 4, 2026.
  https://eccc.weizmann.ac.il/report/2026/091/.

<a id="optimality26"></a>

## optimality26

Samuel Schlesinger, *MCSP optimal-circuit structure research*,
  2026, local research notes, snapshot `1a4a09000f1797117e3e8d066d561f08016f8889`.
  [Interface capacity](/Users/samuelschlesinger/projects/complexity/structure-from-optimality/research/sharing/interface-capacity.md)
  and [gate charging](/Users/samuelschlesinger/projects/complexity/structure-from-optimality/research/sharing/charging.md).
  Their proofs were re-read here; the projection-set extension above is a paper deduction.

<a id="cdj26-refute"></a>

## cdj26-refute

Marco Carmosino, Ngu Dang, Tim Jackman. *Constructive Separations from Gate Elimination*. arXiv:2604.23958v1, 2026. https://arxiv.org/html/2604.23958v1

<a id="cdj26-xor"></a>

## cdj26-xor

Marco Carmosino, Ngu Dang, Tim Jackman. *Simple Circuit Extensions for XOR in PTIME*. STACS 2026, LIPIcs 364, 23:1–23:20. https://doi.org/10.4230/LIPIcs.STACS.2026.23

<a id="cjsw24"></a>

## cjsw24

Lijie Chen, Ce Jin, Rahul Santhanam, Ryan Williams. *Constructive Separations and Their Consequences*. TheoretiCS 3, 2024. https://doi.org/10.46298/theoretics.24.3 ; checked full text: https://arxiv.org/html/2203.14379v5
