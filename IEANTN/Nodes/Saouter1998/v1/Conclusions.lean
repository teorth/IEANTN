/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Hubbard
-/
import IEANTN.Vocabulary.Goldbach

/-!
# Node `Saouter1998.v1` — the odd Goldbach conjecture checked up to `10²⁰`

Y. Saouter, *Checking the odd Goldbach conjecture up to `10²⁰`*, Math. Comp. **67** (1998),
863–866.

## The argument, in one line

Build a ladder of primes from below the even verification height to above `10²⁰`, with every step
shorter than that height. An odd `n` in range lies just above some rung `p`, and `n − p` is even
and small enough for the even verification to write as a sum of two primes.

## What is stated

Two conclusions. `prime_ladder` is Saouter's computation: the ladder itself, with its first and last
rungs as printed on page 865. `odd_up_to_1e20` is the paper's result, imported against the
ladder and an even Goldbach verification.

Saouter's even input is Sinisalo's verification to `4·10¹¹` (Math. Comp. 61, 1993), which this
network has no node for. The main conclusion imports `Richstein2001.v1` to `4·10¹⁴` instead, which
contains that range; the ladder's step bound is still Sinisalo's `4·10¹¹`, as in the paper.

The ladder primes are `5·2²³·k + 12582913`. Page 865 prints the constant as `1258213`, one digit
short; the printed form is never `≡ 1 mod 2²²` and its value at the first `k` is composite. The
endpoints below are the corrected form's, which agree with the primes the paper names.
-/

namespace Saouter1998.v1

open IEANTN

/-- **Saouter's prime ladder.** There is a list of primes beginning with `138412033`, ending with
`100000000209366024193`, increasing, with each step shorter than `4·10¹¹`.

The computation the paper reports: about `2.5·10⁸` primes of the form `2²²·R + 1`, each proved
prime by the paper's Theorem 2, a Brillhart–Lehmer–Selfridge test with base `5`. The first and last
rungs are those printed on page 865; the last exceeds `10²⁰`, which is what lets the ladder cover
the whole range.

The step bound is strict and is Sinisalo's even verification height: a step shorter than `4·10¹¹`
between two odd primes is at most `4·10¹¹ − 2`, so an odd `n` lies between `4` and `4·10¹¹` above
the nearest rung below it, or above the rung before that when the nearest is only `2` below. -/
def prime_ladder : Prop :=
  ∃ l : List ℕ, (∀ p ∈ l, Nat.Prime p) ∧ l.head? = some 138412033 ∧
    l.getLast? = some 100000000209366024193 ∧
    l.IsChain (fun a b => a < b ∧ b - a < 4 * 10 ^ 11)

/-- **The odd Goldbach conjecture up to `10²⁰`.** Every odd `n` with `7 ≤ n ≤ 10²⁰` is a sum of
three primes.

The paper's result, stated in its title and abstract. -/
def odd_up_to_1e20 : Prop :=
  GoldbachOddUpTo (10 ^ 20)

end Saouter1998.v1
