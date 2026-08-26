# The source library

Which papers the network's nodes rest on, and where to get them.

Nothing here is committed: these are other people's papers, and a repository is not a place to
redistribute them. What is committed is this list, so that anyone filling in a node's imports knows
what they need and what has already been found. A local copy lives outside the repository — on the
maintainer's machine at `../IEANTN-papers/` — and the filenames below are that copy's.

**Why this exists.** Tracing what a result assumes needs the paper, not a citation. Twice already a
secondary source has been wrong in a way only the paper settled: FKS2 and FKS both misattribute
Mossinghoff–Trudgian's title, and BKLNW's own proof contradicts its displayed statement. A node's
`imports_status` cannot honestly move to `identified` on the strength of a bibliography.

## Held

| Node | Paper | Identifier | Local file |
|---|---|---|---|
| `FKS2.v1` | Fiori–Kadiri–Swidinsky, *Sharper bounds for the error term in the PNT* | [arXiv:2206.12557](https://arxiv.org/abs/2206.12557) | `FKS2-2023-error-term-PNT.pdf` |
| `FKS.v1` | Fiori–Kadiri–Swidinsky, *Sharper bounds for the Chebyshev function ψ(x)* | [arXiv:2204.02588](https://arxiv.org/abs/2204.02588) | `FKS2023-chebyshev-psi.pdf`, and the published JMAA version |
| `BKLNW.v1` | Broadbent–Kadiri–Lumley–Ng–Wilk, *Sharper bounds for θ(x)* | [arXiv:2002.11068](https://arxiv.org/abs/2002.11068) | `BKLNW2021-chebyshev-theta.pdf`, and the published Math. Comp. version |
| `KLN.v1` | Kadiri–Lumley–Ng, *Explicit zero density for the Riemann zeta function* | [arXiv:2101.12263](https://arxiv.org/abs/2101.12263) | `KLN2018-explicit-zero-density.pdf` |
| `Buthe.v1` | Büthe, *An analytic method for bounding ψ(x)* | [arXiv:1511.02032](https://arxiv.org/abs/1511.02032) | `Buthe2018-bounding-psi.pdf` |
| `MT.v1` | Mossinghoff–Trudgian, *Nonnegative trigonometric polynomials and a zero-free region* | [arXiv:1410.3926](https://arxiv.org/abs/1410.3926) | `MT2015-zero-free-region.pdf` |
| `MTY.v1` | Mossinghoff–Trudgian–Yang, *Explicit zero-free regions* | [arXiv:2212.06867](https://arxiv.org/abs/2212.06867) | `MTY2024-explicit-zero-free.pdf` |
| `Kadiri2005.v1` | Kadiri, *Une région explicite sans zéros pour ζ* | [arXiv:math/0401238](https://arxiv.org/abs/math/0401238) | `Kadiri2005-region-sans-zeros.pdf` |
| `PlattTrudgian.v1` | Platt–Trudgian, *The Riemann hypothesis is true up to 3·10¹²* | [arXiv:2004.09765](https://arxiv.org/abs/2004.09765) | `PlattTrudgian2021-RH-to-3e12.pdf` |
| — | Büthe, *Estimating π(x) … under partial RH assumptions* | [arXiv:1410.7015](https://arxiv.org/abs/1410.7015) | `Buthe2016-pi-under-partial-RH.pdf` |
| — | Hiary, *An explicit van der Corput estimate for ζ(1/2+it)* | [arXiv:1507.01261](https://arxiv.org/abs/1507.01261) | `Hiary2016-van-der-Corput.pdf` |
| — | Hiary–Patel–Yang, *An improved explicit estimate for ζ(1/2+it)* | [arXiv:2207.02366](https://arxiv.org/abs/2207.02366) | `HiaryPatelYang2022-improved-zeta-half.pdf` |
| — | Johnston–Yang, *Some explicit estimates for the error term in the PNT* | [arXiv:2204.01980](https://arxiv.org/abs/2204.01980) | `JohnstonYang2023-error-term-PNT.pdf` |
| — | Johnston, *Improving bounds … by partial verification of RH* | [arXiv:2109.02249](https://arxiv.org/abs/2109.02249) | `Johnston2022-partial-verification.pdf` |

The last five have no node yet. They are held because they are the obvious next imports: Hiary is
where `KLN.v1`'s subconvexity constant comes from, Hiary–Patel–Yang is the improvement that would
sharpen it, and Büthe 2016 is what `Buthe.v1`'s Theorem 2 rests on.

## Wanted

Not on arXiv, or not found there. Each blocks a specific piece of work.

| Paper | Why it is needed | Blocks |
|---|---|---|
| Rosser–Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x)*, Math. Comp. **29** (1975) 243–269 | The node states nothing, and its inequalities are still cited downstream. Predates arXiv. | `RosserSchoenfeld.v1` |
| Dusart, *Explicit estimates of some functions over primes*, Ramanujan J. **45** (2018) 227–251 | `Dusart2018.v1`'s Proposition 5.4 is transcribed from PNT+, not from the paper. arXiv:1002.0442 is an earlier Dusart paper with a similar title — **possibly** the same work, and that is exactly the kind of guess worth not making. | confirming `Dusart2018.v1`; its `imports_status` |
| Cheng–Graham, *Explicit estimates for the Riemann zeta function*, Rocky Mt. J. Math. **34** (2004) 1261–1280 | The erroneous second-derivative test behind `KLN.v1`'s corrected constant. Wanted to understand the correction rather than take FKS's word for it. | closing out the `KLN.v1` correction |
| Platt, *Isolating some non-trivial zeros of zeta*, Math. Comp. **86** (2017) 2449–2467 | FKS uses Platt's computed zeros, via LMFDB. A likely import of `PlattTrudgian.v1` or of `FKS.v1`. | `PlattTrudgian.v1`'s `imports_status` |
| Kadiri–Lumley–Ng, *Bounding ψ(x) with zero-density*, preprint | Cited by FKS as [19]. Appears not to be publicly available, and not listed on the authors' pages. **Not** an input — the lemma attributed to it is proved in FKS itself — so this is for completeness rather than to unblock anything. | nothing |

## Adding to the library

Put the PDF in the local library directory, add a row above, and — if it settles what a node
assumes — set that conclusion's `imports_status` to `identified` and record the edges. The
`housekeeping` queue lists every conclusion still `undetermined`.
