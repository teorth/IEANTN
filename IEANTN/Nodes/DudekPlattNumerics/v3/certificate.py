#!/usr/bin/env python3
"""Exact-rational certificate for DudekPlattNumerics.v3's pi_two_sided_footnote.

Certifies, using only Fraction/int arithmetic (no floats), the derivation recorded in
README.md: that Mossinghoff-Trudgian's Corollary 1 theta bound, split at x^(99/100) and
carried through five integrations by parts, gives

    -2990.501 < (log x)^6 / x * (pi(x) - S_5(x)) < 3230.6      for every real x >= exp(9400),

which implies (with the slack shown below) the node's stated m = -3010.333, M = 3250.488.
This is not a Lean proof and does not certify Corollary 1 itself; see README.md.
"""
from fractions import Fraction as F
from math import factorial
import json

passed = []


def claim(name, ok):
    if not ok:
        raise AssertionError(name)
    passed.append(name)


def exp_lower(t, terms=128):
    """Sum of the first `terms` Taylor terms of e^t; every omitted term is positive, so
    this is a certified LOWER bound on e^t for t > 0."""
    assert t > 0
    return sum((t**n / factorial(n) for n in range(terms + 1)), F(0))


def log_enclosure(t, terms=64):
    """Certified (lower, upper) enclosure of log(t) for t >= 1, via range reduction to
    [1, 2] and the positive-term atanh series log(q) = 2*atanh((q-1)/(q+1))."""
    assert t >= 1
    def unit(q):
        z = (q - 1) / (q + 1)
        lo = 2 * sum((z**(2*k+1) / (2*k+1) for k in range(terms)), F(0))
        rem = 2 * z**(2*terms+1) / ((2*terms+1) * (1 - z*z))
        return lo, lo + rem
    n = 0
    while t > 2:
        t /= 2
        n += 1
    lo, hi = unit(t)
    lo2, hi2 = unit(F(2))
    return lo + n*lo2, hi + n*hi2


# ---- constants from the node's stated Prop and the literature input ----
R = F('6.315')          # Mossinghoff-Trudgian Cor. 1's R, footnote 1's (a, R) pairing
R0 = F('5.573412')      # MT Theorem 1's R, = MT.v1.zero_free_region
H = F(30600000000)      # 3.06e10, the height Theorem 1's own proof consumes: Platt2015.v1.rh_up_to
U = F(9400)              # log(xa), this node's chosen threshold
b = F(99, 100)           # integral split point x^b
M, neg_m = F('3250.488'), F('3010.333')   # the node's stated M, -m (unchanged by this repair)
a_footnote = F(3130)     # Dudek-Platt footnote 1's own a at this R
a_aux = F(3110)          # the certified, stronger theta coefficient this derivation earns

# ---- Part 0: elementary bounds the rest depends on ----
pi_lb = 16*(F(1, 5) - F(1, 3*5**3)) - 4*F(1, 239)   # Machin's identity, truncated from below
claim('pi > 3.14 (Machin, truncated below)', pi_lb > F('3.14'))
C_ub = F('0.388')
claim('C = sqrt(8/(17*pi)) < 0.388', F(8) / (17 * F('3.14')) < C_ub**2)

# ---- Part 1: f_R(u) = C (u/R)^(1/4) e^(-sqrt(u/R)) u^5 decreases past u* = 441R/4 ----
u_star = 441*R/4
claim('441R/4 = 696.22875 is the monotonicity cutoff', u_star == F('696.22875'))
claim('the integral split point b*U = 9306 lies past the cutoff', b*U > u_star)


def f_R_upper_bound(u, x_lo, x_hi, sqrtX_ub):
    """Upper-bounds f_R(u) via a rational bracket on X = sqrt(u/R) and a certified
    Taylor lower bound on e^X (reciprocated)."""
    claim(f'{x_lo}^2 < {u}/R < {x_hi}^2 (brackets X({u}))', x_lo**2 < u/R < x_hi**2)
    claim(f'sqrt(X({u})) < {sqrtX_ub}', x_hi < sqrtX_ub**2)
    return C_ub * sqrtX_ub * u**5 / exp_lower(x_lo)


f9400 = f_R_upper_bound(U, F('38.581'), F('38.582'), F('6.212'))
claim('f_R(9400) < 3110', f9400 < a_aux)
f9306 = f_R_upper_bound(b*U, F('38.387'), F('38.388'), F('6.196'))
claim('f_R(9306) < 3600', f9306 < F(3600))
claim('3110 < 3130: the derived coefficient beats the footnote value, not the reverse',
      a_aux < a_footnote)

# ---- Part 2: the WHOLE theta-error integral, split at x^(99/100), not just its tail ----
# For t >= 2, theta(t) <= t log t trivially, so |E(t)|/(t log^2 t) < 4 there; on [x^b, x],
# Corollary 1 and f_R's monotonicity give the bound.
lo2, _ = log_enclosure(F(2))
claim('log 2 > 2/3 (supports the elementary early-range bound)', lo2 > F(2, 3))
early = 4 * U**6 / F(2)**94          # 4 L^6 e^{-L/100} at L=9400, using e>2
late = F(3600) / (b**7 * U)          # L^6*f_R(bL)/(bL)^7 = f_R(bL)/(b^7*L); worst case over L>=9400 is at L=9400
D = early + late
claim('early part of the normalized integral < 1/1000', early < F(1, 1000))
claim('the whole normalized theta-error integral < 1/2, for every L >= 9400', D < F(1, 2))

# ---- Part 3: five integrations by parts of the main term; remainder and finite correction ----
J7 = 720 * (1/U + F(1792)/U**2 + 7 * U**6 * F(3, 2)**8 / F(2)**4700)
A_ub = sum((factorial(k) * F(3, 2)**(k+1) for k in range(1, 6)), F(0))
B = 2 * A_ub * U**6 / F(2)**9400
claim('A = sum_{k=1..5} k!/log^(k+1)(2), bounded above by 1600', A_ub < 1600)
claim('720 * I7 remainder, normalized, < 1/10', J7 < F(1, 10))
claim('2A finite-correction term, normalized, < 1/1000', B < F(1, 1000))

# ---- Combine: the certified enclosure, and that it implies the node's stated m, M ----
lower = 120 - a_aux - F(1, 2) - F(1, 1000)
upper = 120 + a_aux + F(1, 2) + F(1, 10)
claim('combined lower coefficient equals -2990.501', lower == F('-2990.501'))
claim('combined upper coefficient equals 3230.6', upper == F('3230.6'))
claim('-2990.501 implies the stated m = -3010.333, with slack', -neg_m < lower)
claim('3230.6 implies the stated M = 3250.488, with slack', upper < M)

# ---- R = 6.315's finite-height provenance: Corollary 1 rests on Theorem 1, which consumes ----
# ---- Platt2015.v1.rh_up_to (H = 3.06e10) in ITS OWN proof, not an absent or open input ----
lH, _ = log_enclosure(H)
_, u17 = log_enclosure(F(17))
lo2417, _ = log_enclosure(F(24, 17))
transition = (R - R0)*lH - R*u17
claim("the shifted region already sits inside Theorem 1's classical region above H",
      transition > 0)
claim('the shifted boundary is already right of 1/2 at the stated range t >= 24',
      R * lo2417 > 2)

print(json.dumps({
    'status': 'PASS: exact rational arithmetic only; MT Corollary 1 itself is literature, not proved here',
    'node': 'DudekPlattNumerics.v3.pi_two_sided_footnote',
    'check_count': len(passed),
    'checks': passed,
}, indent=2))
