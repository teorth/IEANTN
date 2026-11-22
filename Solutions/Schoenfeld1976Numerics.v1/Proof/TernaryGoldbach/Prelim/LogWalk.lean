import TernaryGoldbach.Prelim.RamareHarm

/-!
# Building blocks for kernel walks over `log n`

* `incrLo n ≤ 10³⁰ log(1 + 1/n) ≤ incrHi n` (`incr_bounds`), from 12 terms of the artanh series
  (`Real.hasSum_log_one_add_inv`) and a geometric tail;
* `isPr`: trial division by `2 ≤ d ≤ 147`, equivalent to primality below `147²` (`isPr_iff`);
* `floor_div_bounds`: `⌊a/b⌋ ≤ a/b ≤ ⌊a/b⌋ + 1`.

Used by `RamareWalk.lean` and `SmallMertensLower.lean`.
-/

open Finset Real

namespace TernaryGoldbach.Prelim.LogWalk

open TernaryGoldbach.Prelim.RamPf (log_one_add_inv_bounds)

/-- `∑_{j<k} ⌊2·10³⁰/((2j+1)(2n+1)^{2j+1})⌋`. -/
def incrAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => incrAux k n + 2 * 10 ^ 30 / ((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1))

def incrLo (n : ℕ) : ℕ := incrAux 12 n
def incrHi (n : ℕ) : ℕ := incrAux 12 n + 12 + 3 * 10 ^ 30 / (25 * (2 * n + 1) ^ 25) + 1

theorem incrAux_le (n : ℕ) : ∀ k, (incrAux k n : ℝ) ≤
    10 ^ 30 * ∑ j ∈ range k, (2 : ℝ) * (1 / (2 * j + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * j + 1)
  | 0 => by simp [incrAux]
  | k + 1 => by
    rw [incrAux, sum_range_succ, mul_add, Nat.cast_add]
    refine add_le_add (incrAux_le n k) ?_
    have := Nat.cast_div_le (α := ℝ) (m := 2 * 10 ^ 30) (n := (2 * k + 1) * (2 * n + 1) ^ (2 * k + 1))
    refine this.trans (le_of_eq ?_)
    rw [one_div_pow]
    push_cast
    field_simp
    norm_num

theorem le_incrAux (n : ℕ) : ∀ k, 10 ^ 30 * ∑ j ∈ range k,
    (2 : ℝ) * (1 / (2 * j + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * j + 1) ≤ (incrAux k n : ℝ) + k
  | 0 => by simp [incrAux]
  | k + 1 => by
    rw [incrAux, sum_range_succ, mul_add, Nat.cast_add, Nat.cast_succ]
    have h1 := le_incrAux n k
    have hpos : 0 < (2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) := by positivity
    have h2 := Nat.lt_div_mul_add (a := 2 * 10 ^ 30) hpos
    have h3 : ((2 * 10 ^ 30 : ℕ) : ℝ) < ((2 * 10 ^ 30 / ((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1)) : ℕ) : ℝ) *
        (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) + (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) := by
      exact_mod_cast h2
    have hq : (0 : ℝ) < (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) := by exact_mod_cast hpos
    have h4 : (10 : ℝ) ^ 30 * (2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * k + 1)) ≤
        ((2 * 10 ^ 30 / ((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1)) : ℕ) : ℝ) + 1 := by
      have e : (10 : ℝ) ^ 30 * (2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * k + 1)) =
          ((2 * 10 ^ 30 : ℕ) : ℝ) / (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) := by
        rw [one_div_pow]; push_cast; field_simp; norm_num
      rw [e, div_le_iff₀ hq]; linarith
    linarith

/-- **`incrLo/D ≤ log(1 + 1/n) ≤ incrHi/D`** for `n ≥ 1`. -/
theorem incr_bounds {n : ℕ} (hn : 1 ≤ n) :
    (incrLo n : ℝ) ≤ 10 ^ 30 * Real.log (1 + (n : ℝ)⁻¹) ∧
      10 ^ 30 * Real.log (1 + (n : ℝ)⁻¹) ≤ (incrHi n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := log_one_add_inv_bounds hn0 12
  refine ⟨(incrAux_le n 12).trans (by nlinarith), ?_⟩
  have h3 := le_incrAux n 12
  -- the tail `(2/25) y^{25}/(1 − y²) ≤ 3/(25 (2n+1)^{25})`
  set y : ℝ := 1 / (2 * (n : ℝ) + 1) with hy
  have hy0 : 0 < y := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy3 : y ≤ 1 / 3 := by
    rw [hy, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have htail : 2 / (2 * ((12 : ℕ) : ℝ) + 1) * y ^ (2 * 12 + 1) / (1 - y ^ 2) ≤ 3 / 25 * y ^ 25 := by
    have h1y : 8 / 9 ≤ 1 - y ^ 2 := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    push_cast
    have : 0 ≤ y ^ 25 := by positivity
    nlinarith
  have hfl : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) ≤ ((3 * 10 ^ 30 / (25 * (2 * n + 1) ^ 25) : ℕ) : ℝ) + 1 := by
    have hpos : 0 < 25 * (2 * n + 1) ^ 25 := by positivity
    have h2 := Nat.lt_div_mul_add (a := 3 * 10 ^ 30) hpos
    have hq : (0 : ℝ) < ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) := by exact_mod_cast hpos
    have h3' : ((3 * 10 ^ 30 : ℕ) : ℝ) < ((3 * 10 ^ 30 / (25 * (2 * n + 1) ^ 25) : ℕ) : ℝ) *
        ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) + ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) := by exact_mod_cast h2
    have e : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) = ((3 * 10 ^ 30 : ℕ) : ℝ) / ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) := by
      rw [hy, one_div_pow]; push_cast; field_simp; norm_num
    rw [e, div_le_iff₀ hq]; linarith
  unfold incrHi
  push_cast
  push_cast at h3
  nlinarith

/-- Trial division by `2 ≤ d ≤ 147` with `d² ≤ p`. -/
def isPr (p : ℕ) : Bool :=
  2 ≤ p && (List.range' 2 146).all (fun d => p < d * d || p % d != 0)

theorem isPr_iff {p : ℕ} (hp : p < 21609) : isPr p = true ↔ p.Prime := by
  unfold isPr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · intro h
    rw [Nat.prime_def_le_sqrt]
    refine ⟨h.1, fun m hm2 hms hdvd => ?_⟩
    have hmm : m * m ≤ p := Nat.le_sqrt.1 hms
    have hm : m ≤ 147 := by nlinarith
    rcases h.2 m ⟨hm2, by omega⟩ with h1 | h1
    · omega
    · exact h1 (Nat.mod_eq_zero_of_dvd hdvd)
  · intro h
    refine ⟨h.two_le, fun d hd => ?_⟩
    by_cases hdd : p < d * d
    · exact Or.inl hdd
    · right
      intro hmod
      have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hmod
      rcases h.eq_one_or_self_of_dvd d hdvd with h1 | h1
      · omega
      · subst h1; nlinarith

theorem floor_div_bounds (a b : ℕ) (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b ∧ (a : ℝ) / b ≤ ((a / b : ℕ) : ℝ) + 1 := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have h2 := Nat.lt_div_mul_add (a := a) hb
  have hq : (0 : ℝ) < b := by exact_mod_cast hb
  have : (a : ℝ) < ((a / b : ℕ) : ℝ) * b + b := by exact_mod_cast h2
  rw [div_le_iff₀ hq]; linarith

end TernaryGoldbach.Prelim.LogWalk
