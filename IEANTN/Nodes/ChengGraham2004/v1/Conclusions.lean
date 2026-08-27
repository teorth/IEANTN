/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary

/-!
# Node `ChengGraham2004.v1`

Cheng and Graham, *Explicit estimates for the Riemann zeta function*,
Rocky Mountain J. Math. **34** (2004), no. 4, 1261-1280.

The exponential-sum machinery underneath `Hiary2016`, and so underneath `KLN` and the whole `FKS`
chain. `Hiary`'s proof of his van der Corput lemma applies three results from here: `[Lemma 5]`,
the Weyl-van der Corput lemma "in the more precise form presented at the bottom of page 1273";
`[Lemma 3]`, the van der Corput second-derivative test, at the step `Hiary`'s source labels
`corput second der`; and the summation estimates following `[Lemma 7]`.

**This node states nothing yet, and that is deliberate rather than merely pending.**

Its Lemma 3 is the erroneous one. `FKS` records that Hiary's constant "relies on an erroneous
explicit version of van der Corput second derivative test due to Cheng-Graham", and that correcting
it moves `a_1` from `0.63` to `0.77` -- which is why `Hiary2016.v1` and `KLN.v1` both state `0.77`.
Transcribing Lemma 3 as printed would put a knowably wrong statement into the network, which is
precisely what the network exists not to do.

## What to add first

The **corrected** second-derivative test, not the printed one. Where that is argued is
D. Patel, *An Explicit Upper Bound for `|zeta(1 + it)|`*, Indag. Math. (N.S.) **33** (2022), no. 5,
1012-1032, Footnote 3 -- which is not held and is not on arXiv. Until it is, this node cannot
honestly state its headline result, and `Hiary2016.v1` stays `traced` with the dependency named in
prose.

Lemmas 5 and 7 are not implicated and could be stated on their own. Nothing consumes them
directly, so there is no reason to yet.
-/
