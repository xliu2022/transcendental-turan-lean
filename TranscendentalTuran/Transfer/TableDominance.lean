/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TranscendentalTuran.Transfer.TableCounting
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # A unique dominant direction in a table with few nonroot cells -/

@[expose] public section

namespace TranscendentalTuran.Transfer

theorem rectangle_lower_bound (n r c : ℝ) (hn : 0 ≤ n)
    (hsum : r + c ≤ 4 * n / 3) (hr : r ≤ 11 * n / 12) (hc : c ≤ 11 * n / 12) :
    n ^ 2 / 36 ≤ (n - r) * (n - c) := by
  rcases le_total r c with hrc | hcr
  · have hfirst : n / 3 ≤ n - r := by linarith
    have hsecond : n / 12 ≤ n - c := by linarith
    have hprod := mul_le_mul hfirst hsecond (by positivity : 0 ≤ n / 12)
      (by linarith : 0 ≤ n - r)
    nlinarith
  · have hfirst : n / 12 ≤ n - r := by linarith
    have hsecond : n / 3 ≤ n - c := by linarith
    have hprod := mul_le_mul hfirst hsecond (by positivity : 0 ≤ n / 3)
      (by linarith : 0 ≤ n - r)
    nlinarith

theorem two_directions_not_dominant (n r c : ℝ) (hn : 0 < n)
    (hsum : r + c ≤ 4 * n / 3) :
    ¬ (11 * n / 12 < r ∧ 11 * n / 12 < c) := by
  rintro ⟨hr, hc⟩
  linarith

theorem root_rectangle_budget_lt (n t q : ℝ) (hn : 128 ≤ n) (ht : 128 ≤ t)
    (hq : q ≤ 4 * n / 3) : 2 * n ^ 2 / t + q < n ^ 2 / 36 := by
  have hn0 : 0 ≤ n := by linarith
  have hfirst : 2 * n ^ 2 / t ≤ n ^ 2 / 64 := by
    calc
      2 * n ^ 2 / t ≤ 2 * n ^ 2 / 128 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) ht
      _ = n ^ 2 / 64 := by ring
  have hsecond : q ≤ n ^ 2 / 96 := by
    have hprod := mul_nonneg hn0 (show 0 ≤ n - 128 by linarith)
    nlinarith
  have hn2 : 0 < n ^ 2 := by positivity
  nlinarith

universe u v w
variable {A : Type u} {B : Type v} {C : Type w}

/-- This is the manuscript's two-dimensional dominance count, with actual
finite colour fibres. The only input not encoded by separation is the bound
on the number of nonroot cells; the product clique decomposition supplies it
in the graph application. -/
theorem unique_dominant_direction [Fintype A] [Fintype B]
    {f : A → B → C} (hf : SeparatedTable f) (roots : Finset C)
    (n t : ℕ) (hA : Fintype.card A = n) (hB : Fintype.card B = n)
    (hn : 128 ≤ n) (ht : 128 ≤ t)
    (hroots : (roots.card : ℝ) ≤ 4 * (n : ℝ) / 3)
    (hmissing : ((nonrootCells f roots).card : ℝ) ≤ 2 * (n : ℝ) ^ 2 / t) :
    ((11 * (n : ℝ) / 12 < (rowColours f roots).card) ∨
      (11 * (n : ℝ) / 12 < (columnColours f roots).card)) ∧
      ¬ ((11 * (n : ℝ) / 12 < (rowColours f roots).card) ∧
        (11 * (n : ℝ) / 12 < (columnColours f roots).card)) := by
  classical
  have hnR : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have htR : (128 : ℝ) ≤ t := by exact_mod_cast ht
  have hsum : ((rowColours f roots).card : ℝ) + (columnColours f roots).card ≤
      4 * (n : ℝ) / 3 := by
    have h : ((rowColours f roots).card : ℝ) + (columnColours f roots).card ≤ roots.card := by
      exact_mod_cast oriented_colours_card_le hf roots
    exact h.trans hroots
  refine ⟨?_, two_directions_not_dominant _ _ _ (by linarith) hsum⟩
  by_contra hdom
  have hr : ((rowColours f roots).card : ℝ) ≤ 11 * (n : ℝ) / 12 := by
    by_contra hr
    exact hdom (Or.inl (lt_of_not_ge hr))
  have hc : ((columnColours f roots).card : ℝ) ≤ 11 * (n : ℝ) / 12 := by
    by_contra hc
    exact hdom (Or.inr (lt_of_not_ge hc))
  have hrect := rectangle_lower_bound (n : ℝ) (rowColours f roots).card
    (columnColours f roots).card (by positivity) hsum hr hc
  have hrow : ((rowSupport f roots).card : ℝ) ≤ (rowColours f roots).card := by
    exact_mod_cast rowSupport_card_le hf roots
  have hcol : ((columnSupport f roots).card : ℝ) ≤ (columnColours f roots).card := by
    exact_mod_cast columnSupport_card_le hf roots
  have hrowN : (rowSupport f roots).card ≤ n := by
    simpa [hA] using Finset.card_le_univ (rowSupport f roots)
  have hcolN : (columnSupport f roots).card ≤ n := by
    simpa [hB] using Finset.card_le_univ (columnSupport f roots)
  have hout : ((outsideSupport f roots).card : ℝ) =
      ((n : ℝ) - (rowSupport f roots).card) *
        ((n : ℝ) - (columnSupport f roots).card) := by
    rw [outsideSupport_card, hA, hB, Nat.cast_mul, Nat.cast_sub hrowN, Nat.cast_sub hcolN]
  have hprod : ((n : ℝ) - (rowColours f roots).card) *
      ((n : ℝ) - (columnColours f roots).card) ≤ (outsideSupport f roots).card := by
    rw [hout]
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hcount : ((outsideSupport f roots).card : ℝ) ≤
      (nonrootCells f roots).card + roots.card := by
    exact_mod_cast outsideSupport_card_le hf roots
  have hbudget := root_rectangle_budget_lt (n : ℝ) t roots.card hnR htR hroots
  linarith

end TranscendentalTuran.Transfer
