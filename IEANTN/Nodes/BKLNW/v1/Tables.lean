/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms

/-!
# Tables: `BKLNW.v1`

Data from Broadbent, Kadiri, Lumley, Ng and Wilk, *Sharper bounds for the Chebyshev function
`theta(x)`*, Math. Comp. **90** (2021), 2281-2315. Data only -- what is claimed *about* it is in
`Conclusions.lean`.

Extracted from the typeset tables rather than retyped, so that a slip of the finger is not one of
the things that can go wrong; the per-table docstrings record what was cross-checked.
-/

namespace BKLNW.v1

/-- **Table 8**: the entries `(b, eps)` of the paper's Table 8, in the printed order.

What the table asserts is fixed by the paper's own Corollary 8.1: for `b` and `b'` **consecutive**
entries of column 1, `|psi x - x| <= eps b * x` for all `x` in `[e^b, e^b']`. The caption writes
`eps(b, b')` for the entry and lists only `b`, which is why the pairing has to be read off the
column rather than the row.

The paper also uses the entries in the unbounded form, and its own Theorem 2 states that form
outright: "Let `b > 0`. Then there exists a positive constant `eps(b)` such that
`|psi(x) - x| / x <= eps(b)` for all `x >= e^b`." Corollary 2.1 and Corollary 15.1 both apply it
that way. That is consistent with the piecewise reading
because the tabulated values are strictly decreasing (checked mechanically: all 57 consecutive pairs), so a
bound holding on each later interval holds on their union -- but only out to `e^25000`, the last
entry. Past that the table says nothing and the paper's Theorem 13 takes over.

Note also that `eps` is applied to arguments that are not tabulated: `eps(19 log 10)` with
`19 log 10 = 43.7...` is quoted as the `b = 40` entry, i.e. rounded down to the previous row,
which is the safe direction for a decreasing bound.

The first twenty-three rows (`b <= 2000`) are computed by the method of the paper's reference [3]
-- Buthe, *Estimating pi(x) and related functions under partial RH assumptions*, Math. Comp. **85**
(2016), 2483-2498, which is a *different* paper from the [4] that `Buthe.v1` records -- and the
rest (`b >= 2500`) as in the paper's Theorem 13 by the method of [37], Platt-Trudgian, *The error
term in the prime number theorem*, Math. Comp. **90** (2021), 871-881, itself distinct from the
[38] that `PlattTrudgian.v1` records. The paper notes [3] is the better of the two below
`b = 2400`. Theorem 2 is attributed to "Buthe, Platt-Trudgian" and drawn from [3], [4] and [37],
so `Buthe.v1` is one of the three inputs. See this node's `imports` notes.

Extracted from the typeset table rather than retyped. Checked at four points against the paper's
own prose: `eps(40) = 1.93378e-8` is the value Corollaries 2.1 and 5.1 quote, `eps(3000)` matches
the introduction's `4.60e-14`, and the first and last rows match the printed table. -/
def table8 : List (ℕ × ℝ) :=
  [
    (20, 4.26760e-5),
    (21, 2.58843e-5),
    (22, 1.56996e-5),
    (23, 9.52229e-6),
    (24, 5.77556e-6),
    (25, 3.50306e-6),
    (30, 2.87549e-7),
    (35, 2.36034e-8),
    (40, 1.93378e-8),
    (45, 1.09073e-8),
    (50, 1.11990e-9),
    (100, 2.45299e-12),
    (200, 2.18154e-12),
    (300, 2.09022e-12),
    (400, 2.03981e-12),
    (500, 1.99986e-12),
    (600, 1.98894e-12),
    (700, 1.97643e-12),
    (800, 1.96710e-12),
    (900, 1.95987e-12),
    (1000, 1.94751e-12),
    (1500, 1.93677e-12),
    (2000, 1.92279e-12),
    (2500, 9.06304e-13),
    (3000, 4.59972e-14),
    (3500, 2.48641e-15),
    (4000, 1.42633e-16),
    (4500, 8.68295e-18),
    (5000, 5.63030e-19),
    (5500, 3.91348e-20),
    (6000, 2.94288e-21),
    (6500, 2.38493e-22),
    (7000, 2.07655e-23),
    (7500, 1.96150e-24),
    (8000, 1.97611e-25),
    (8500, 2.12970e-26),
    (9000, 2.44532e-27),
    (9500, 2.97001e-28),
    (10000, 3.78493e-29),
    (10500, 5.10153e-30),
    (11000, 7.14264e-31),
    (11500, 1.04329e-31),
    (12000, 1.59755e-32),
    (12500, 2.53362e-33),
    (13000, 4.13554e-34),
    (13500, 7.21538e-35),
    (14000, 1.22655e-35),
    (15000, 4.10696e-37),
    (16000, 1.51402e-38),
    (17000, 6.20397e-40),
    (18000, 2.82833e-41),
    (19000, 1.36785e-42),
    (20000, 7.16209e-44),
    (21000, 4.11842e-45),
    (22000, 2.43916e-46),
    (23000, 1.56474e-47),
    (24000, 1.07022e-48),
    (25000, 7.57240e-50),
  ]

end BKLNW.v1
