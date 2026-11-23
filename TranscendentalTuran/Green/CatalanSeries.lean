/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Analysis.Real.Pi.Wallis
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FunProp

@[expose] public section

/-!
# The scalar Catalan series in the quadrant Green calculation

The finite identities in this file do not presume the combinatorial interpretation of
the coefficients.  The walk-counting bridge is a separate theorem.
-/

noncomputable section

open scoped BigOperators Topology
open Filter Finset

namespace TranscendentalTuran.Green

/-- Catalan numbers normalized by the number of unrestricted two-step choices. -/
def scaledCatalan (n : ℕ) : ℝ := (catalan n : ℝ) / 4 ^ n

@[simp] theorem scaledCatalan_zero : scaledCatalan 0 = 1 := by
  norm_num [scaledCatalan]

@[simp] theorem scaledCatalan_one : scaledCatalan 1 = 1 / 4 := by
  norm_num [scaledCatalan]

theorem scaledCatalan_nonneg (n : ℕ) : 0 ≤ scaledCatalan n := by
  unfold scaledCatalan
  positivity

theorem catalan_real_recurrence (n : ℕ) :
    ((n : ℝ) + 2) * (catalan (n + 1) : ℝ) =
      2 * (2 * (n : ℝ) + 1) * (catalan n : ℝ) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n + 1),
    ← succ_mul_catalan_eq_centralBinom n] at h
  have h' : ((n : ℝ) + 1) * (((n : ℝ) + 2) * (catalan (n + 1) : ℝ)) =
      ((n : ℝ) + 1) * (2 * (2 * (n : ℝ) + 1) * (catalan n : ℝ)) := by
    have hc : ((n : ℝ) + 1) * (((n : ℝ) + 1 + 1) * (catalan (n + 1) : ℝ)) =
        2 * (2 * (n : ℝ) + 1) * (((n : ℝ) + 1) * (catalan n : ℝ)) := by
      exact_mod_cast h
    nlinarith [hc]
  exact mul_left_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0) h'

theorem scaledCatalan_succ (n : ℕ) :
    scaledCatalan (n + 1) =
      scaledCatalan n * (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 4) := by
  have h := catalan_real_recurrence n
  have hn : 2 * (n : ℝ) + 4 ≠ 0 := by positivity
  have hp : (4 : ℝ) ^ n ≠ 0 := by positivity
  unfold scaledCatalan
  rw [pow_succ]
  field_simp
  nlinarith [h]

/-- Consecutive normalized Catalan product. -/
def catalanProduct (n : ℕ) : ℝ := scaledCatalan n * scaledCatalan (n + 1)

theorem catalanProduct_nonneg (n : ℕ) : 0 ≤ catalanProduct n :=
  mul_nonneg (scaledCatalan_nonneg n) (scaledCatalan_nonneg (n + 1))

theorem catalanProduct_succ (n : ℕ) :
    catalanProduct (n + 1) = catalanProduct n *
      ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) /
        ((2 * (n : ℝ) + 4) * (2 * (n : ℝ) + 6))) := by
  unfold catalanProduct
  rw [scaledCatalan_succ (n + 1), scaledCatalan_succ n]
  push_cast
  field_simp
  ring

/-- The summand which will count even-length corner-return walks. -/
def greenTerm (n : ℕ) : ℝ :=
  4 * (scaledCatalan n * scaledCatalan (n + 2) - scaledCatalan (n + 1) ^ 2)

/-- The cubic polynomial giving an exact telescoping certificate. -/
def boundaryPolynomial (x : ℝ) : ℝ := (4 * x + 5) * (32 * x ^ 2 + 80 * x + 33)

/-- Boundary term in the finite telescoping sum. -/
def boundaryTerm (n : ℕ) : ℝ :=
  (8 / 15 : ℝ) * boundaryPolynomial n * catalanProduct n

@[simp] theorem boundaryTerm_zero : boundaryTerm 0 = 22 := by
  norm_num [boundaryTerm, boundaryPolynomial, catalanProduct]

theorem boundaryPolynomial_certificate (x : ℝ) :
    4 * (x + 2) * (x + 3) * boundaryPolynomial x -
      (2 * x + 1) * (2 * x + 3) * boundaryPolynomial (x + 1) = 45 := by
  unfold boundaryPolynomial
  ring

theorem greenTerm_eq_nonnegative (n : ℕ) :
    greenTerm n = 6 * catalanProduct n / (((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have h₂ : n + 2 = (n + 1) + 1 := by omega
  unfold greenTerm catalanProduct
  rw [h₂, scaledCatalan_succ (n + 1), scaledCatalan_succ n]
  push_cast
  field_simp
  ring

theorem greenTerm_nonneg (n : ℕ) : 0 ≤ greenTerm n := by
  rw [greenTerm_eq_nonnegative]
  exact div_nonneg (mul_nonneg (by norm_num) (catalanProduct_nonneg n)) (by positivity)

theorem greenTerm_eq_boundary_sub (n : ℕ) :
    greenTerm n = boundaryTerm n - boundaryTerm (n + 1) := by
  rw [greenTerm_eq_nonnegative]
  unfold boundaryTerm
  rw [catalanProduct_succ]
  push_cast
  unfold boundaryPolynomial
  field_simp
  ring

/-- The exact finite sum; no infinite-series theorem is used here. -/
theorem sum_greenTerm (n : ℕ) :
    ∑ k ∈ range n, greenTerm k = 22 - boundaryTerm n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ, ih, greenTerm_eq_boundary_sub]
      ring

/-- An exact relation to Mathlib's Wallis product. -/
theorem wallis_mul_catalanProduct (n : ℕ) :
    Real.Wallis.W n * catalanProduct n =
      1 / (2 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) := by
  induction n with
  | zero => norm_num [Real.Wallis.W, catalanProduct]
  | succ n ih =>
      rw [Real.Wallis.W_succ, catalanProduct_succ]
      have h₁ : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
      have h₂ : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
      have h₃ : 2 * (n : ℝ) + 4 ≠ 0 := by positivity
      have h₄ : 2 * (n : ℝ) + 6 ≠ 0 := by positivity
      have hn₁ : (n : ℝ) + 1 ≠ 0 := by positivity
      have hn₂ : (n : ℝ) + 2 ≠ 0 := by positivity
      have hn₃ : (n : ℝ) + 3 ≠ 0 := by positivity
      calc
        _ = (Real.Wallis.W n * catalanProduct n) *
            (((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1) *
                ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3))) *
              ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) /
                ((2 * (n : ℝ) + 4) * (2 * (n : ℝ) + 6)))) := by ring
        _ = _ := by
          rw [ih]
          push_cast
          field_simp
          ring

theorem catalanProduct_eq_wallis (n : ℕ) :
    catalanProduct n =
      1 / (2 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) * Real.Wallis.W n) := by
  have hw := (Real.Wallis.W_pos n).ne'
  have h := wallis_mul_catalanProduct n
  apply (mul_left_cancel₀ hw)
  rw [h]
  field_simp

theorem boundaryTerm_eq_wallis (n : ℕ) :
    boundaryTerm n =
      4 * boundaryPolynomial n /
        (15 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) * Real.Wallis.W n) := by
  unfold boundaryTerm
  rw [catalanProduct_eq_wallis]
  field_simp
  ring

theorem boundaryTerm_nonneg (n : ℕ) : 0 ≤ boundaryTerm n := by
  unfold boundaryTerm boundaryPolynomial
  exact mul_nonneg (by positivity) (catalanProduct_nonneg n)

/-- A reciprocal coordinate makes the boundary limit a continuity calculation. -/
def reciprocalSucc (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem tendsto_reciprocalSucc : Tendsto reciprocalSucc atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
  exact (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from
    tendsto_const_nhds).div_atTop hn

theorem boundaryTerm_reciprocal (n : ℕ) :
    boundaryTerm n =
      (4 * ((128 + 96 * reciprocalSucc n - 44 * reciprocalSucc n ^ 2 -
          15 * reciprocalSucc n ^ 3) / (1 + reciprocalSucc n))) /
        (15 * Real.Wallis.W n) := by
  rw [boundaryTerm_eq_wallis]
  unfold boundaryPolynomial reciprocalSucc
  have hn₁ : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn₂ : (n : ℝ) + 2 ≠ 0 := by positivity
  have hw : Real.Wallis.W n ≠ 0 := (Real.Wallis.W_pos n).ne'
  field_simp
  ring

theorem tendsto_boundaryTerm :
    Tendsto boundaryTerm atTop (𝓝 (1024 / (15 * Real.pi))) := by
  have ht := tendsto_reciprocalSucc
  have hp : Tendsto
      (fun n => (128 + 96 * reciprocalSucc n - 44 * reciprocalSucc n ^ 2 -
          15 * reciprocalSucc n ^ 3) / (1 + reciprocalSucc n))
      atTop (𝓝 (128 : ℝ)) := by
    have hc : ContinuousAt
        (fun x : ℝ => (128 + 96 * x - 44 * x ^ 2 - 15 * x ^ 3) / (1 + x)) 0 := by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num
    simpa [Function.comp_def] using hc.tendsto.comp ht
  have hw : (15 : ℝ) * (Real.pi / 2) ≠ 0 := by positivity
  have h4 : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4) := tendsto_const_nhds
  have h15 : Tendsto (fun _ : ℕ => (15 : ℝ)) atTop (𝓝 15) := tendsto_const_nhds
  have hl := (h4.mul hp).div
    (h15.mul Real.Wallis.tendsto_W_nhds_pi_div_two) hw
  have heq : (4 * (128 : ℝ)) / (15 * (Real.pi / 2)) = 1024 / (15 * Real.pi) := by
    field_simp
    ring
  have hl' := Filter.Tendsto.congr (fun n => (boundaryTerm_reciprocal n).symm) hl
  simpa only [heq] using hl'

theorem greenTerm_summable : Summable greenTerm := by
  apply summable_of_sum_range_le greenTerm_nonneg (c := 22)
  intro n
  rw [sum_greenTerm]
  linarith [boundaryTerm_nonneg n]

/-- The scalar series evaluates exactly, using finite telescoping and the Wallis limit. -/
theorem hasSum_greenTerm :
    HasSum greenTerm (22 - 1024 / (15 * Real.pi)) := by
  have hl : Tendsto (fun n => ∑ k ∈ range n, greenTerm k) atTop
      (𝓝 (22 - 1024 / (15 * Real.pi))) := by
    simpa only [sum_greenTerm] using
      (show Tendsto (fun _ : ℕ => (22 : ℝ)) atTop (𝓝 22) from
        tendsto_const_nhds).sub tendsto_boundaryTerm
  have hval : (∑' n, greenTerm n) = 22 - 1024 / (15 * Real.pi) :=
    tendsto_nhds_unique greenTerm_summable.hasSum.tendsto_sum_nat hl
  simpa only [hval] using greenTerm_summable.hasSum

theorem tsum_greenTerm : (∑' n, greenTerm n) = 22 - 1024 / (15 * Real.pi) :=
  hasSum_greenTerm.tsum_eq

end TranscendentalTuran.Green
