## Selected submission: First Proof Q4 and Gowers--Long

This fork contains six selected Lean proofs developed by Zhang Xiaolong with
ChatGPT assistance. `comparator.json` selects the six `Palomar.*` entry points.
`Solution.lean` delegates to the substantive developments in
`FormalConjectures/Arxiv/2602.05192/FirstProof4.lean` and
`FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean`.
The original proof-development snapshot is `dac8718dcc821af2af99c8b2f430635ab4701d6d`;
the subsequent mechanically verified submission snapshot is
`c148b4b061db036a99efa56422b6fb54e0581334`.

### The six statements

In the table, `F(n)` is defined below and all inequalities involving it use its
natural-number value, cast to the reals where a real power occurs.

| Comparator declaration, in namespace `Palomar` | Exact mathematical scope |
| --- | --- |
| `finiteAdditiveConvolution_degree` | For every natural n and real polynomials p,q of degree n, their finite additive convolution has degree n. Monicity and real-rootedness are not assumed. |
| `four_2` | The finite free Stam inequality below for every pair of monic real-rooted degree-2 polynomials, including repeated roots. |
| `four_3` | The same inequality for every pair of monic real-rooted degree-3 polynomials, including repeated roots. |
| `maximalLength_ge_of_isSquare` | For every perfect-square natural n, `(Nat.sqrt n)^3 <= F(n)`; equivalently, `F(m^2) >= m^3` for every natural m. |
| `maximalLength_pow` | For every natural n > 1 and real e satisfying `F(n) = n^e`, there are arbitrarily large natural m with `F(m) >= m^e`. |
| `maximalLength_pow_eventually` | Under the same n,e hypotheses, for each real b < e, every sufficiently large natural m satisfies `F(m) >= m^b`. |

### Finite additive convolution and the polynomial inequality

Write
$p(x)=\sum_{i=0}^n a_i x^{n-i}$ and
$q(x)=\sum_{j=0}^n b_j x^{n-j}$. Their finite additive convolution is

$$
(p\boxplus_n q)(x)=\sum_{k=0}^n
\left(\sum_{i+j=k}\frac{(n-i)!(n-j)!}{n!(n-k)!}a_i b_j\right)x^{n-k}.
$$

For a monic polynomial whose n roots are real and distinct, define

$$
\Phi_n(p)=\sum_{i=1}^n\left(\sum_{j\ne i}\frac1{\lambda_i-\lambda_j}\right)^2.
$$

Set $\Phi_n(p)=+\infty$ at repeated roots. The two selected cases prove

$$
\frac1{\Phi_n(p\boxplus_n q)}\ge
\frac1{\Phi_n(p)}+\frac1{\Phi_n(q)},\qquad n=2,3.
$$

The Lean value lies in the extended nonnegative reals; `1 / infinity = 0`.
The hypotheses `p.degree = n` and `p.roots.card = n` express that all roots,
counted with multiplicity, are real. There is no simple-root assumption.
The degree result is a supporting coefficient fact: the leading coefficient
of the convolution is the product of the two nonzero leading coefficients.

The mathematical source is First Proof, Question 4; its v2 Appendix B.4,
*The finite free Stam inequality*, by Jorge Garza Vargas, Nikhil Srivastava,
and Zack Stier, gives the general mathematical theorem.

### What the low-degree proofs implement

The quadratic proof factors each input into real linear factors. For roots a,b,
the reciprocal functional equals $(a-b)^2/2$. The convolution root gap squared
is the sum of the two input gaps squared. This supplies the selected inequality,
with equality in this degree, and includes the coincident-root boundary.

For cubic roots a,b,c, let $\mu=(a+b+c)/3$, and put

$$
s=\frac{(a-b)^2+(b-c)^2+(c-a)^2}{6},\qquad
t=(a-\mu)(b-\mu)(c-\mu).
$$

The source proves the identities

$$
4s^3-27t^2=((a-b)(b-c)(c-a))^2,
\qquad H(s,t)=\frac{4s^3-27t^2}{18s^2}=\frac1{\Phi_3(p)}.
$$

Here the last expression is interpreted as zero at s=t=0. The invariants of
the convolution are $(s_p+s_q,t_p+t_q)$. For positive s_p,s_q the proof checks
the following exact remainder identity:

$$
\begin{aligned}
&H(s_p+s_q,t_p+t_q)-H(s_p,t_p)-H(s_q,t_q)\\
&=\frac{3\bigl[(t_p s_q^2-t_q s_p^2)^2
 +2s_p s_q(t_p^2s_q^2+t_q^2s_p^2)\bigr]}
 {2s_p^2s_q^2(s_p+s_q)^2}\ge0.
\end{aligned}
$$

This is the algebraic content of `cubic_stam_sos`. The implementation also
handles zero-variance cases, constructs real cubic roots from the discriminant
condition through trigonometric identities, and proves the reciprocal formula
at repeated roots. The quadratic and cubic targets do not apply the general
`four` declaration, which remains unfinished in this fork.

These formulas explain the specific proof implementation offered here.
No claim is made that the cubic identity or proof route is mathematically new.
The identities are supporting facts inside the existing proof; this documentation
revision does not add them to the six Comparator-selected declarations.

### 2-increasing sequences and their growth

A triple a is 2-less than b when at least two of its three coordinates are
strictly smaller. A sequence is 2-increasing if this holds for every pair of
positions i < j. The relation is not transitive, so an adjacent-pair condition
would give a different notion. `F(n)` is the maximal length of such a sequence
whose coordinates all belong to $\{1,\ldots,n\}$.

The source is Gowers and Long, *The length of an s-increasing sequence of
r-tuples*, arXiv:1609.08688v2, Section 1.1: the lower-bound part of Proposition
1.4, Lemma 1.7, and the paragraph immediately after that lemma, respectively.
These results are introductory construction and amplification results in that
paper. The paper's later main upper-bound and comparable-set theorems are
outside the selected scope.

For the square bound, the implementation enumerates triples

$$
(mi+j+1,\ mi+k+1,\ mj+k+1),\qquad 0\le i,j,k<m,
$$

in lexicographic order of (i,j,k). This gives m^3 entries in $[m^2]^3$.
If the first differing digit is i, the first two coordinates increase;
if it is j, the first and third increase; if it is k, the last two increase.

The product construction encodes a pair of coordinates by
$n(a-1)+b$. Applied to two valid sequences, it proves
$F(mn)\ge F(m)F(n)$. Consequently
$F(n^k)\ge F(n)^k=n^{ke}$ when $F(n)=n^e$, giving arbitrarily large
instances with exponent e. Monotonicity then gives, for m >= 1,
$F(m)\ge (m/n)^e$. For each b < e, this implies the eventual bound
$F(m)\ge m^b$. The implemented proof uses the sufficient threshold
$m\ge\max(1,\lceil(n^e)^{1/(e-b)}\rceil)$.

The research use of this amplification is precise: a finite-size improvement
above exponent 3/2 would propagate to an eventual exponent above 3/2 by taking
3/2 < b < e. The selected theorems provide the propagation mechanism; they do
not supply such a finite-size improvement or settle the conjectured upper bound.

### Earlier formalizations and the scope of comparison

The accompanying `related_formalizations` records the following work.

- [Archon general Q4 proof](https://github.com/frenzymath/Archon-FirstProof-Results/blob/35550f2bc0a58289bbe2342a64f10a46ada0f52f/FirstProof/FirstProof4/Problem4.lean), in particular
  `Problem4.harmonic_mean_inequality_full`, addresses all n >= 2 using
  `polyBoxPlus` and the real-valued `invPhiN_poly`. Its intended mathematical
  scope includes the selected n=2,3 inequalities. This fork uses different
  definitions, including an extended-nonnegative-real Phi. A Lean bridge
  between the two representations has not been checked. The arbitrary-degree,
  nonmonic degree-preservation declaration also has a different formal scope
  from a monic degree helper in that development.
- [Wentao Li's square-bound proof](https://github.com/VictorLiwentao/fc-palomar-proofs/blob/9b2a1eeaa6d00172a8e08351ed43b896e21ce950/FCPalomar/GowersLongSquare/Solution.lean) is registered as
  [PALOMAR-2026-11-13-000015 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-13-000015&version=1). Source comparison found the same
  `lt₂`, `IsIncreasing₂`, and `maximalLength` definitions after ignoring
  whitespace and comments, with the same lower-bound hypothesis and conclusion.
  The namespace differs. This is a same-result registration precedent and a
  prior formalization to credit; it does not establish novelty of this fork.
- [weiyangzen's earlier square-bound proof](https://github.com/weiyangzen/awesome_theorems/blob/32e5f75412a804463a0b0c6fff1362d4ab5275b3/Formalizations/Lean/AwesomeTheorems/Stage5/Theorems/S5_CLM_00003491/Proof.lean) states the lower
  bound with the maximal-length definition expanded.
- [Daniel Puri's growth proof](https://github.com/danielpuri1901/erdos-lean-formalization/blob/c838d73/proofs/triplespow/Solution.lean) explicitly targets the
  `maximalLength_pow` type through `increasing_triples_power`.
- [Wentao Li's eventual-growth proof](https://github.com/VictorLiwentao/fc-palomar-proofs/blob/9b2a1eeaa6d00172a8e08351ed43b896e21ce950/FCPalomar/GowersLongPow/Solution.lean) targets
  `maximalLength_pow_eventually` with the same core definitions; its metadata
  credits an adaptation of Daniel Puri's product construction.

The present targets are implemented in this fork rather than importing these
external proofs. A source inspection does not establish the historical origin
of every proof idea. The sources are credited without a first-proof or
first-formalization claim.

### Audience, limits, and verification

The polynomial part is relevant to readers studying polynomial inequalities
and finite free convolution, with explicit low-degree formulas and boundary
cases that can be compared with a general proof. The sequence part concerns
the extremal function in Loh's 2-increasing-triples problem and the exact
finite-to-asymptotic product mechanism. The already registered square bound
provides a concrete comparison for assessing this result family's research
scope. Registration precedent does not by itself establish that another proof
of the result merits a separate record.

Four other theorem declarations in the two substantive files remain unfinished:
the general `four`, `maximalLength_four`, `maximalLength_le_isBigO`, and
`maximalLength_le_strong`. They are outside this six-target selection. No claim
is made to have proved every result in either cited paper or the whole repository.

The fixed earlier snapshot c148b4b passed Palomar mechanical verification in
[run 43814428822](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/43814428822).
This documentation revision preserves all existing Lean code in `Challenge.lean`
apart from comments; the substantive proofs and Comparator selection are unchanged.
The revised snapshot must be built and checked again before submission.
The original workflow was human-led with ChatGPT assistance; no independent
human mathematical referee review is claimed.

---

# Formal Conjectures

[![.github/workflows/push_master.yml](https://github.com/google-deepmind/formal-conjectures/actions/workflows/build-and-docs.yml/badge.svg)](https://github.com/google-deepmind/formal-conjectures/actions/workflows/build-and-docs.yml)
[![arXiv](https://img.shields.io/badge/arXiv-2605.13171-b31b1b.svg)](https://arxiv.org/abs/2605.13171)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/google-deepmind/formal-conjectures)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://leanprover.zulipchat.com/#narrow/channel/524981-Formal-conjectures)

A collection of formalised statements of conjectures in
[Lean](https://leanprover.github.io/lean4/doc/whatIsLean.html), using
[mathlib](https://github.com/leanprover-community/mathlib4).

Explore the docs: [Formal Conjectures Documentation](https://google-deepmind.github.io/formal-conjectures/)

Join our [channel on the leanprover Zulip](https://leanprover.zulipchat.com/#narrow/channel/524981-Formal-conjectures)

## Goals

While there is a growing corpus of formalised theorems including proofs, there
is a lack of open conjectures where only the statement has been formalised. This
would be useful for a few reasons. It could

*   Become a great benchmark for automated theorem provers and automated
    formalisation tools.
*   Help clarify the precise meaning of conjectures through formalisation.
*   Encourage the expansion of `mathlib` by highlighting needed definitions.

It is our hope that this initiative will form the seed of a much richer dataset of
formalised conjectures.

### Note on Formalisation Accuracy

Formalizing mathematical statements without proofs is inherently challenging.
Subtle inaccuracies can arise where the formal statement might not perfectly
capture the nuances of the original conjecture. To mitigate this issue, we will
rely on careful human review of contributions, and plan to periodically leverage
AlphaProof to help identify potential misformalisations.

## Contributing

Contributions are most welcome — consider adding (or even just opening an issue
describing) your favourite conjecture. See [CONTRIBUTING.md](./CONTRIBUTING.md)
for the full contribution guide, including ways to contribute, the
step-by-step process, file structure conventions, attribute usage, and style
guidelines.

## Usage, Structure & Features

This is a Lean 4 project managed with `lake` and a dependency `mathlib`. You
first need to
[install elan, lake, lean and if you want vscode](https://leanprover-community.github.io/get_started.html)
and then run

```bash
lake exe cache get
lake build
```

### Directory structure

The directory structure is organised by the type of sources of the conjectures.
There are two special directories:

-   `FormalConjecturesUtil` contains utilities like the
    [`category` attribute](./FormalConjecturesUtil/Attributes/Basic.lean), the
    [`question` attribute](./FormalConjecturesUtil/Attributes/Basic.lean) and some
    linters.
-   `FormalConjecturesForMathlib` contains code potentially suitable to be upstreamed to
    [mathlib](https://github.com/leanprover-community/mathlib4). Here we follow
    mathlib's directory structure.

For details on the `@[category]`, `@[formal_proof]`, `@[AMS]`, `@[question]` attributes
that statements in this repository use, see
[CONTRIBUTING.md](./CONTRIBUTING.md).

## Versioning

This repo will track the monthly tagged releases of mathlib (which correspond to
Lean releases), rather than tracking mathlib master.

To minimize friction when adding problem statements that need definitions that
are not yet in mathlib, such definitions can be added to the `FormalConjecturesForMathlib`
directory. This ensures that the addition of these problems to
formal-conjectures is not locked to the mathlib release cadence.

When `lean-toolchain` is updated on `main`, a GitHub Actions workflow
automatically adds a git tag of the form `v4.{X}.{Y}`, following mathlib's
tagging convention.

Stable benchmark snapshots are tagged using the format
`bench-v{N}-lean4.{X}.{Y}`, where:

-   **`v{N}` (Benchmark version):** Identifies the set of problems included in
    the benchmark. The benchmark version is bumped whenever problems are added,
    removed, or when misformalizations are corrected.
-   **`lean4.{X}.{Y}` (Lean version):** Identifies the Lean 4 toolchain
    version used for that snapshot.

Tags are immutable: fixes to misformalizations are never patched into an existing
benchmark version but instead go into `v{N+1}`.

## Citing formal-conjectures
If your work has used formal-conjectures, please consider citing it via
```
@misc{FormalConjectures,
  author       = {{The Formal Conjectures Authors}},
  title        = {{T}he {F}ormal {C}onjectures {R}epository},
  year         = {2025},
  url          = {https://github.com/google-deepmind/formal-conjectures},
}

@article{FormalConjecturesPaper,
  authors = {Firsching, Moritz and Lezeau, Paul and Mercuri, Salvatore
    and Horv{\'a}th, Mikl{\'o}s Z and Dillies, Ya{\"e}l and S{\"o}nne, Calle and Wieser, Eric and
    Zhang, Fred and Hubert, Thomas and Ag{\"u}era y Arcas, Blaise and Kohli, Pushmeet},
  title = {{F}ormal {C}onjectures: {A}n {O}pen and {E}volving {B}enchmark for {V}erified {D}iscovery in {M}athematics},
  year = {2026},
  url = {https://arxiv.org/abs/2605.13171v1},
}
```

## Licensing

Copyright 2025 The Formal Conjectures Authors. All software is licensed under the Apache License,
Version 2.0 (Apache 2.0); you may not use this file except in compliance with
the Apache 2.0 license. You may obtain a copy of the Apache 2.0 license at:
https://www.apache.org/licenses/LICENSE-2.0

All other materials are licensed under the Creative Commons Attribution 4.0
International License (CC-BY). You may obtain a copy of the CC-BY license at:
https://creativecommons.org/licenses/by/4.0/legalcode.

The content may be based on third party sources and may in some cases include
third party content. The original source for each conjecture is indicated by a
URL within the source file. Third party content may be subject to different
licensing requirements. In particular:

-   Material from Wikipedia articles, MathOverflow and the OEIS is released under the
    Creative Commons Attribution-Share-Alike License 4.0.
-   Material from bbchallenge.org is used under the Creative Commons Attribution
    4.0 International License.
-   Material from the Equational Theories Project is used under Apache-2.0.
-   Material from arXiv is used under the licence applicable to the relevant
    paper, as indicated at the URL within the source file.

Unless required by applicable law or agreed to in writing, all software and
materials distributed here under the Apache 2.0 or CC-BY license are distributed
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
express or implied. See the licenses for the specific language governing
permissions and limitations under those licenses.

This is not an official Google product.
