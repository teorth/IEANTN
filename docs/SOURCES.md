# The source library

Which papers the network's nodes rest on, and where to get them.

Nothing here is committed: these are other people's papers, and a repository is not a place to
redistribute them. What is committed is this list, so that anyone filling in a node's imports knows
what they need and what has already been found. A local copy lives outside the repository — on the
maintainer's machine at `../IEANTN-papers/` — and the filenames below are that copy's.

So the **identifier column is the record**: a DOI or arXiv id is a durable pointer anyone can
follow, where a filename is one machine's convenience. When a paper is held in both preprint
and published form, name both identifiers — the two are not always the same paper, and the
`Kadiri2005.v1` row below is the standing proof of it.

**Why this exists.** Tracing what a result assumes needs the paper, not a citation. Twice already a
secondary source has been wrong in a way only the paper settled: FKS2 and FKS both misattribute
Mossinghoff–Trudgian's title, and BKLNW's own proof contradicts its displayed statement. A node's
`imports_status` cannot honestly move to `identified` on the strength of a bibliography.

## Held

| Node | Paper | Identifier | Local file |
|---|---|---|---|
| `FKS2.v1`, `FKS2.v2`, `FKS2Numerics.v1` | Fiori–Kadiri–Swidinsky, *Sharper bounds for the error term in the prime number theorem* | [arXiv:2206.12557](https://arxiv.org/abs/2206.12557); published as [doi:10.1007/s40993-023-00454-w](https://doi.org/10.1007/s40993-023-00454-w), *Research in Number Theory* **9** (2023) | `FKS2-2023-published-ResNumberTheory.pdf` **and** `FKS2-2023-error-term-PNT.pdf`, with `source/FKS2-2023-error-term-PNT/FKS2.tex` as the transcription surface. The two agree on every constant — see below |
| `FKS.v1` | Fiori–Kadiri–Swidinsky, *Sharper bounds for the Chebyshev function ψ(x)* | [arXiv:2204.02588](https://arxiv.org/abs/2204.02588) | `FKS2023-chebyshev-psi.pdf`, and the published JMAA version |
| `BKLNW.v1` | Broadbent–Kadiri–Lumley–Ng–Wilk, *Sharper bounds for θ(x)* | [arXiv:2002.11068](https://arxiv.org/abs/2002.11068) | `BKLNW2021-chebyshev-theta.pdf`, and the published Math. Comp. version |
| `KLN.v1` | Kadiri–Lumley–Ng, *Explicit zero density for the Riemann zeta function* | [arXiv:2101.12263](https://arxiv.org/abs/2101.12263); published as [doi:10.1016/j.jmaa.2018.04.071](https://doi.org/10.1016/j.jmaa.2018.04.071), *J. Math. Anal. Appl.* **465** (2018) 22–46 | `KLN2018-published-JMAA.pdf` **and** `KLN2018-explicit-zero-density.pdf` |
| `Buthe.v1` | Büthe, *An analytic method for bounding ψ(x)* | [arXiv:1511.02032](https://arxiv.org/abs/1511.02032); published as [doi:10.1090/mcom/3264](https://doi.org/10.1090/mcom/3264), *Math. Comp.* **87** (2018) 1991–2009 | `Buthe2018-published-MathComp.pdf` **and** `Buthe2018-bounding-psi.pdf` |
| `MT.v1` | Mossinghoff–Trudgian, *Nonnegative trigonometric polynomials and a zero-free region* | [arXiv:1410.3926](https://arxiv.org/abs/1410.3926); published as [doi:10.1016/j.jnt.2015.05.010](https://doi.org/10.1016/j.jnt.2015.05.010), *J. Number Theory* **157** (2015) 329–349 | `MT2015-published-JNT.pdf` **and** `MT2015-zero-free-region.pdf` |
| `MTY.v1` | Mossinghoff–Trudgian–Yang, *Explicit zero-free regions* | [arXiv:2212.06867](https://arxiv.org/abs/2212.06867) | `MTY2024-explicit-zero-free.pdf` |
| `Kadiri2005.v1` | Kadiri, *Une région explicite sans zéros pour ζ* | Acta Arith. **117**.4 (2005) 303–339; [arXiv:math/0401238](https://arxiv.org/abs/math/0401238) | `Kadiri2005-published-ActaArith.pdf` **and** `Kadiri2005-region-sans-zeros.pdf`. The two are **not** interchangeable: the preprint gives `5.70176`, the published version `5.69693`, and only the latter supports MT's `R = 5.7` |
| `PlattTrudgian.v1` | Platt–Trudgian, *The Riemann hypothesis is true up to 3·10¹²* | [arXiv:2004.09765](https://arxiv.org/abs/2004.09765); published as [doi:10.1112/blms.12460](https://doi.org/10.1112/blms.12460), *Bull. London Math. Soc.* **53** (2021) 792–797 | `PlattTrudgian2021-RH-to-3e12-published-BLMS.pdf` **and** `PlattTrudgian2021-RH-to-3e12.pdf` |
| `Buthe2016.v1` | Büthe, *Estimating π(x) … under partial RH assumptions* | [arXiv:1410.7015](https://arxiv.org/abs/1410.7015) | `Buthe2016-pi-under-partial-RH.pdf` |
| `Hiary2016.v1` | Hiary, *An explicit van der Corput estimate for ζ(1/2+it)* | [arXiv:1507.01261](https://arxiv.org/abs/1507.01261) | `Hiary2016-van-der-Corput.pdf` |
| — | Hiary–Patel–Yang, *An improved explicit estimate for ζ(1/2+it)* | [arXiv:2207.02366](https://arxiv.org/abs/2207.02366) | `HiaryPatelYang2022-improved-zeta-half.pdf` |
| — | Johnston–Yang, *Some explicit estimates for the error term in the PNT* | [arXiv:2204.01980](https://arxiv.org/abs/2204.01980) | `JohnstonYang2023-error-term-PNT.pdf` |
| — | Johnston, *Improving bounds … by partial verification of RH* | [arXiv:2109.02249](https://arxiv.org/abs/2109.02249) | `Johnston2022-partial-verification.pdf` |
| `FKBJ.v1` | Franke–Kleinjung–Büthe–Jost, *A practical analytic method for calculating π(x)* | Math. Comp. **86** (2017) no. 308, 2889–2909 | `FKBJ-practical-analytic-pi.pdf` |
| `Platt2017.v1` | Platt, *Isolating some non-trivial zeros of zeta* | Math. Comp. **86** (2017) 2449–2467 | `Platt2017-isolating-zeros.pdf` |
| `PlattTrudgian2021.v1` | Platt–Trudgian, *The error term in the prime number theorem* | Math. Comp. **90** (2021) no. 328, 871–881 | `PlattTrudgian2021-error-term-PNT.pdf` |
| `Platt2015.v1` | Platt, *Computing π(x) Analytically* | [arXiv:1203.5712](https://arxiv.org/abs/1203.5712); Math. Comp. **84** (2015) 1521–1535 | LaTeX source only, under `source/` |
| `Trudgian2011.v1` | Trudgian, *Improvements to Turing's method* | Math. Comp. **80** (2011) no. 276, 2259–2279 | `Trudgian2011-improvements-turing.pdf` |
| `Brown1967.v1` | Brown, *On the error in reconstructing a non-bandlimited function…* | J. Math. Anal. Appl. **18** (1967) 75–84 | `Brown1967-bandpass-sampling-error.pdf` |
| — | Patel, *An Explicit Upper Bound for \|ζ(1+it)\|* | [arXiv:2009.00769](https://arxiv.org/abs/2009.00769); Indag. Math. (N.S.) **33** (2022) 1012–1032 | LaTeX source; Footnote 3 verifies `Hiary2016.v1`'s correction |
| — | Platt–Trudgian, *An improved explicit bound on \|ζ(1/2+it)\|* | J. Number Theory **147** (2015) 842–851 | `PlattTrudgian2015-improved-zeta-half.pdf` |
| — | Rosser, *Explicit bounds for some functions of prime numbers* | Amer. J. Math. **63** (1941) 211–232 | `Rosser1941-explicit-bounds.pdf` — FKBJ's Theorem 2.1 |
| `RosserSchoenfeld.v1` | Rosser–Schoenfeld, *Sharper bounds for θ(x) and ψ(x)* | Math. Comp. **29** (1975) 243–269 | `RosserSchoenfeld1975-sharper-bounds.pdf` |
| — | Dudek–Platt, *On solving a curious inequality of Ramanujan* | [doi:10.1080/10586458.2014.990118](https://doi.org/10.1080/10586458.2014.990118), *Exp. Math.* **24** (2015) no. 3, 289–294 | `DudekPlatt2015-ramanujan-inequality.pdf`. Held ahead of the node in [#54](https://github.com/teorth/IEANTN/issues/54). **Theorem 1.2 gives `x ≥ exp(9658)` unconditionally**, where `PrimeNumberTheoremAnd` proves `exp(3915)` — the paper is the authority for a `literature` conclusion, so a node citing it must state `exp(9658)` |
| `Dusart2018.v1` | Dusart, *Explicit estimates of some functions over primes* | [doi:10.1007/s11139-016-9839-4](https://doi.org/10.1007/s11139-016-9839-4) | `Dusart2018-explicit-estimates-published.pdf` |
| `ChengGraham2004.v1` | Cheng–Graham, *Explicit estimates for the Riemann zeta function* | Rocky Mt. J. Math. **34** (2004) 1261–1280 | `ChengGraham2004-explicit-zeta.pdf` |

Several of these have no node yet. They are held because they are the obvious next imports: Hiary
is where `KLN.v1`'s subconvexity constant comes from, Hiary–Patel–Yang is the improvement that
would sharpen it, and Büthe 2016 — *Estimating π(x) … under partial RH assumptions*, Math. Comp.
**85** (2016) 2483–2498 — is BKLNW's reference [3], the source of the `b ≤ 2000` half of its
Table 8, and is now `Buthe2016.v1`. Note that BKLNW's [3] and [4] are two different Büthe papers,
and only [4] is `Buthe.v1`; likewise its [37] and [38] are two different Platt–Trudgian papers, and
only [38] is `PlattTrudgian.v1`.

`Wedeniwski.v1` has no row above and never will: its source is the ZetaGrid project website,
`http://www.zetagrid.net`, which is no longer reachable. Everything that node records is at second
hand from `Kadiri2005` and from Platt–Trudgian's account of the project, and its justification is
`asserted` for exactly that reason.

### Cited but not held

**None.** This section listed five entries that named a published DOI in the node's
`sources[].id` while the library held only a preprint. All five are now held in both forms:
FKS2 (*Res. Number Theory* **9** (2023) Paper No. 63), KLN (*JMAA* **465** (2018) 22–46),
Büthe (*Math. Comp.* **87** (2018) 1991–2009), MT (*J. Number Theory* **157** (2015) 329–349)
and Platt–Trudgian (*Bull. LMS* **53** (2021) 792–797).

Keep it that way. The `Kadiri2005.v1` row is why this is not pedantry: its preprint gives
`5.70176` and its published version `5.69693`, and **only the latter supports the `R = 5.7` that
MT relies on**. A node whose constants came from a preprint while its citation points at the
published paper is making an unchecked claim, and the network cannot see the difference — a
fingerprint pins the statement, not the provenance of the numbers in it.

#### What the FKS2 comparison found

Six conclusions across `FKS2.v1` and `FKS2.v2` are `lean-comparator` verified, and every constant
in them was read from the arXiv LaTeX. Comparing the published version against the preprint:

- **Every decimal constant agrees, with matching multiplicities.** Extracting each number
  matching `[0-9]+\.[0-9]{2,}` in document order gives 692 distinct values in the preprint and
  693 in the published version; the only differences are the DOI `10.1007` and one fewer
  occurrence of the arXiv id `2206.12557`. The load-bearing constants — `121.0961`, `9.2211`,
  `0.84768363`, `0.826`, `5.5666305`, `6.3376`, `0.4298` — appear in both, the same number of
  times. Integer differences are all table-layout artifacts of the two typesettings.
- **Both recorded errata survive into the published version**, so the notes on them stand.
  Lemma 10's `a = 0` bullet reads "decreases with x for all `log(x) > -2b/c`" where its own proof
  derives "negative when `u < -2b/c`" — the inequality is reversed. And Corollary 11 states
  `B ≥ 1 + C²/(16R)`, where discharging it through Lemma 10's *first* bullet needs
  `b < -c²/(16a)`, i.e. the strict `B > 1 + C²/(16R)`; at equality one falls into the second
  bullet, which gives decrease only above a threshold.

So the six verified conclusions are verified against statements the published paper also makes.

## Wanted

Not on arXiv, or not found there. Each blocks a specific piece of work.

| Paper | Why it is needed | Blocks |
|---|---|---|
| Kadiri–Lumley–Ng, *Bounding ψ(x) with zero-density*, preprint | Cited by FKS as [19]. Appears not to be publicly available, and not listed on the authors' pages. **Not** an input — the lemma attributed to it is proved in FKS itself — so this is for completeness rather than to unblock anything. | nothing |

## LaTeX source, and why it is the primary surface

`../IEANTN-papers/source/<name>/` holds the arXiv **LaTeX source** for fourteen of these papers,
fetched from `https://arxiv.org/e-print/<id>`. **Read the source, not the PDF, whenever the paper is
on arXiv.**

PDF text extraction loses glyphs that carry meaning. The one that cost this project a wrong finding
across five conclusions is the absolute-value bar around a displayed fraction:
`|(ψ(x) − x)/x| ≤ ε` extracts as `ψ(x) −x x ≤ε`, which reads as a signed one-sided bound and is
indistinguishable from one. In source it is `\left|\frac{\psi(x) - x}{x}\right|` and there is
ight|` and there is
nothing to misread. Source also turns tables into `&`-separated rows rather than a coordinate
puzzle, and makes `\cite{}` keys resolve exactly — no more matching `[3]` against a bibliography
and hoping the author name is unique.

Two caveats. Source is the **arXiv** version, which is not always the published one: `Kadiri2005`
gives `5.70176` on arXiv and `5.69693` in Acta Arith., and `FKS`'s tables differ between preprint
and JMAA. Where a node cites the published version, the PDF is still the authority. And the papers
with no arXiv entry — Rosser–Schoenfeld, Dusart 2018, Cheng–Graham, FKBJ, Platt 2015, Kadiri's
published version — have no source to read.

## Adding to the library

Put the PDF in the local library directory, add a row above, and — if it settles what a node
assumes — record the edges and set that conclusion's `imports_status`: `identified` if every
input is now an edge, `traced` if the inputs are written down but at least one is not the sort of
thing an arrow can carry. See [NODES.md](NODES.md) for the four values.

The `housekeeping` queue lists conclusions that are still `undetermined`. It deliberately does not
list `traced` ones — some of their missing edges are waiting on a paper someone could make a node
of, and some on an algorithm nobody ever can, and nothing distinguishes those mechanically.
