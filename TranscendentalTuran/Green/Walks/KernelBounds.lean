/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Walks.Kernel

@[expose] public section

namespace TranscendentalTuran.Green.Walks

/-- A walk of length `n` cannot reach a first coordinate greater than `n`. -/
theorem count_eq_zero_of_lt_first (n i j : ℕ) (hi : n < i) : count n (i, j) = 0 := by
  induction n generalizing i j with
  | zero =>
      have hi0 : i ≠ 0 := by omega
      simp [count, Prod.mk.injEq, hi0]
  | succ n ih =>
      rw [count_succ]
      have hi0 : i ≠ 0 := by omega
      simp [hi0, ih (i + 1) j (by omega), ih (i - 1) j (by omega),
        ih (i - 1) (j + 1) (by omega), ih (i + 1) (j - 1) (by omega)]

/-- A walk of length `n` cannot reach a second coordinate greater than `n`. -/
theorem count_eq_zero_of_lt_second (n i j : ℕ) (hj : n < j) : count n (i, j) = 0 := by
  induction n generalizing i j with
  | zero =>
      have hj0 : j ≠ 0 := by omega
      simp [count, Prod.mk.injEq, hj0]
  | succ n ih =>
      rw [count_succ]
      have hj0 : j ≠ 0 := by omega
      simp [hj0, ih (i + 1) j (by omega), ih (i - 1) j (by omega),
        ih (i - 1) (j + 1) (by omega), ih (i + 1) (j - 1) (by omega)]

/-- Every nonzero kernel coefficient lies in the finite box `[0,n]²`. -/
theorem count_support_bound {n i j : ℕ} (h : count n (i, j) ≠ 0) : i ≤ n ∧ j ≤ n := by
  constructor
  · by_contra hi
    exact h (count_eq_zero_of_lt_first n i j (by omega))
  · by_contra hj
    exact h (count_eq_zero_of_lt_second n i j (by omega))

end TranscendentalTuran.Green.Walks
