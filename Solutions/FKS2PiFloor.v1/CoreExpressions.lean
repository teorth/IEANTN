/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import CertificateKernel
import RowBound

namespace FKS2PiFloor.Certificate

open LeanCert.Core

private def subE (e f : Expr) : Expr := .add e (.neg f)
private def xE : Expr := .var 0
private def logE : Expr := .log xE
private def rowE : Expr :=
  let scaledRoot := Expr.sqrt (.mul (.const 16) (.mul logE (.const (2000000 / 11133261))))
  .mul (.mul (.const (413 / 2000)) (.sqrt (.mul (.const 4) scaledRoot)))
    (.exp (.mul (.const (-1 / 4)) scaledRoot))

private theorem sqrt_sixteen_mul (y : ℝ) : Real.sqrt (16 * y) = 4 * Real.sqrt y := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  norm_num

private theorem scaled_row_eq (y : ℝ) :
    (413 / 2000 : ℝ) * Real.sqrt (4 * Real.sqrt (16 * y)) *
      Real.exp ((-1 / 4) * Real.sqrt (16 * y)) =
      0.826 * Real.sqrt (Real.sqrt y) * Real.exp (-Real.sqrt y) := by
  rw [sqrt_sixteen_mul, show 4 * (4 * Real.sqrt y) = 16 * Real.sqrt y by ring,
    sqrt_sixteen_mul]
  rw [show (-1 / 4 : ℝ) * (4 * Real.sqrt y) = -Real.sqrt y by ring]
  ring

private theorem eval_rowE (x : ℝ) : Expr.eval (fun _ ↦ x) rowE = row x := by
  simp only [rowE, logE, xE, Expr.eval]
  convert scaled_row_eq (Real.log x / 5.5666305) using 1 <;>
    norm_num [row, div_eq_mul_inv]

private def smallRhs (a : ℚ) : Expr := .mul (.mul rowE xE) (.log (.const a))
private def largeRhs : Expr := .mul (.mul rowE xE) logE

def smallPlusCore (a u c : ℚ) : Expr :=
  subE (.mul (.add (.mul (.const (u - c)) (.log (.const a)))
    (subE xE (.const a))) logE) (smallRhs a)

def smallMinusCore (a b l c : ℚ) : Expr :=
  subE (.mul (subE (.mul (.const (c - l)) (.log (.const b)))
    (subE xE (.const a))) logE) (smallRhs b)

def largePlusCore (c : ℚ) : Expr :=
  subE (subE (.add (.mul xE logE) (.mul (.const (5 / 2)) xE))
    (.mul (.const (c + 33 / 10)) (.mul logE logE))) largeRhs

def largeMinusCore (c : ℚ) : Expr :=
  subE (subE (subE (.mul (.const c) (.mul logE logE)) (.mul xE logE)) xE) largeRhs

private theorem supported_smallPlus (a u c : ℚ) : ExprSupportedCore (smallPlusCore a u c) := by
  unfold smallPlusCore subE smallRhs rowE xE logE
  repeat constructor

private theorem supported_smallMinus (a b l c : ℚ) : ExprSupportedCore (smallMinusCore a b l c) := by
  unfold smallMinusCore subE smallRhs rowE xE logE
  repeat constructor

private theorem supported_largePlus (c : ℚ) : ExprSupportedCore (largePlusCore c) := by
  unfold largePlusCore subE largeRhs rowE xE logE
  repeat constructor

private theorem supported_largeMinus (c : ℚ) : ExprSupportedCore (largeMinusCore c) := by
  unfold largeMinusCore subE largeRhs rowE xE logE
  repeat constructor

theorem eval_smallPlusCore (a u c : ℚ) {x : ℝ} (hx : 1 < x) (ha : (1 : ℝ) < a) :
    Expr.eval (fun _ ↦ x) (smallPlusCore a u c) =
      (((u : ℝ) + (x - a) / Real.log a - c) * Real.log x / x - row x) *
        (x * Real.log a) := by
  have hx0 : x ≠ 0 := (lt_trans zero_lt_one hx).ne'
  have ha0 : Real.log a ≠ 0 := (Real.log_pos ha).ne'
  norm_num [smallPlusCore, subE, smallRhs, eval_rowE, xE, logE, Expr.eval]
  field_simp
  ring

theorem eval_smallMinusCore (a b l c : ℚ) {x : ℝ} (hx : 1 < x) (hb : (1 : ℝ) < b) :
    Expr.eval (fun _ ↦ x) (smallMinusCore a b l c) =
      (((c : ℝ) - (l + (x - a) / Real.log b)) * Real.log x / x - row x) *
        (x * Real.log b) := by
  have hx0 : x ≠ 0 := (lt_trans zero_lt_one hx).ne'
  have hb0 : Real.log b ≠ 0 := (Real.log_pos hb).ne'
  norm_num [smallMinusCore, subE, smallRhs, eval_rowE, xE, logE, Expr.eval]
  field_simp
  ring

theorem eval_largePlusCore (c : ℚ) {x : ℝ} (hx : 1 < x) :
    Expr.eval (fun _ ↦ x) (largePlusCore c) =
      (1 + (5 / 2) / Real.log x - (c + 3.3) * Real.log x / x - row x) *
        (x * Real.log x) := by
  have hx0 : x ≠ 0 := (lt_trans zero_lt_one hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  norm_num [largePlusCore, subE, largeRhs, eval_rowE, xE, logE, Expr.eval]
  field_simp
  ring

theorem eval_largeMinusCore (c : ℚ) {x : ℝ} (hx : 1 < x) :
    Expr.eval (fun _ ↦ x) (largeMinusCore c) =
      (c * Real.log x / x - 1 - 1 / Real.log x - row x) * (x * Real.log x) := by
  have hx0 : x ≠ 0 := (lt_trans zero_lt_one hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  norm_num [largeMinusCore, subE, largeRhs, eval_rowE, xE, logE, Expr.eval]
  field_simp
  ring

theorem small_plus_core_of_check (a u c lo hi : ℚ) (ha : 1 < a) (hlo : 1 < lo)
    (hle : lo ≤ hi) (depth : ℕ)
    (hcheck : checkSplitCoreUpper (smallPlusCore a u c) lo hi hle depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi,
      ((u : ℝ) + (x - a) / Real.log a - c) * Real.log x / x ≤ row x := by
  intro x hx
  have hxa : (1 : ℝ) < a := by exact_mod_cast ha
  have hxl : (1 : ℝ) < lo := by exact_mod_cast hlo
  have hx1 := hxl.trans_le hx.1
  have h := upper_of_checkSplitCore _ (supported_smallPlus a u c) lo hi hle depth hcheck x hx
  rw [eval_smallPlusCore a u c hx1 hxa] at h
  have hd : 0 < x * Real.log a := mul_pos (lt_trans zero_lt_one hx1) (Real.log_pos hxa)
  have := nonpos_of_mul_nonpos_left h hd
  linarith

theorem small_minus_core_of_check (a b l c lo hi : ℚ) (hb : 1 < b) (hlo : 1 < lo)
    (hle : lo ≤ hi) (depth : ℕ)
    (hcheck : checkSplitCoreUpper (smallMinusCore a b l c) lo hi hle depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi,
      ((c : ℝ) - (l + (x - a) / Real.log b)) * Real.log x / x ≤ row x := by
  intro x hx
  have hxb : (1 : ℝ) < b := by exact_mod_cast hb
  have hxl : (1 : ℝ) < lo := by exact_mod_cast hlo
  have hx1 := hxl.trans_le hx.1
  have h := upper_of_checkSplitCore _ (supported_smallMinus a b l c) lo hi hle depth hcheck x hx
  rw [eval_smallMinusCore a b l c hx1 hxb] at h
  have hd : 0 < x * Real.log b := mul_pos (lt_trans zero_lt_one hx1) (Real.log_pos hxb)
  have := nonpos_of_mul_nonpos_left h hd
  linarith

theorem large_plus_core_of_check (c lo hi : ℚ) (hlo : 1 < lo) (hle : lo ≤ hi) (depth : ℕ)
    (hcheck : checkSplitCoreUpper (largePlusCore c) lo hi hle depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi,
      1 + (5 / 2) / Real.log x - (c + 3.3) * Real.log x / x ≤ row x := by
  intro x hx
  have hxl : (1 : ℝ) < lo := by exact_mod_cast hlo
  have hx1 := hxl.trans_le hx.1
  have h := upper_of_checkSplitCore _ (supported_largePlus c) lo hi hle depth hcheck x hx
  rw [eval_largePlusCore c hx1] at h
  have hd : 0 < x * Real.log x := mul_pos (lt_trans zero_lt_one hx1) (Real.log_pos hx1)
  have := nonpos_of_mul_nonpos_left h hd
  linarith

theorem large_minus_core_of_check (c lo hi : ℚ) (hlo : 1 < lo) (hle : lo ≤ hi) (depth : ℕ)
    (hcheck : checkSplitCoreUpper (largeMinusCore c) lo hi hle depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi,
      c * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  intro x hx
  have hxl : (1 : ℝ) < lo := by exact_mod_cast hlo
  have hx1 := hxl.trans_le hx.1
  have h := upper_of_checkSplitCore _ (supported_largeMinus c) lo hi hle depth hcheck x hx
  rw [eval_largeMinusCore c hx1] at h
  have hd : 0 < x * Real.log x := mul_pos (lt_trans zero_lt_one hx1) (Real.log_pos hx1)
  have := nonpos_of_mul_nonpos_left h hd
  linarith

end FKS2PiFloor.Certificate
