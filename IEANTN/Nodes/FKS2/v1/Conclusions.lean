/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary

/-!
# Node `FKS2.v1`

Two conversion pipelines. The first turns an admissible classical bound on the error `E_psi(x) =
|psi(x) - x| / x` into one on `E_theta(x) = |theta(x) - x| / x`; the second turns a bound on
`E_theta` into one on `E_pi(x) = |pi(x) - li(x)| / (x / log x)`. Each stage carries admissible
classical bounds of one error to admissible classical bounds of the next, which is why the paper
is a natural `pipeline` as much as a `paper`: its content is a family of implications rather than
a single numerical claim.

**This node states nothing yet.** It records that the paper is in scope and carries its
citation, so that a conclusion can be added the moment a downstream node needs one.

What to add first:

The two pipeline theorems are the conclusions worth exporting first, since they are what
downstream nodes consume. The paper's own numerical corollaries follow from them together with
whichever input bounds are supplied.
-/
