/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Walks.Determinant

@[expose] public section

namespace TranscendentalTuran.Green.Walks

@[simp] theorem lineCount_zero_start (n b : ℕ) : lineCount n 0 b = 0 := by
  induction n generalizing b with
  | zero => simp [lineCount, eq_comm]
  | succ n ih => simp [lineCount, ih]

/-- The same nearest-neighbor recurrence can be applied at the initial endpoint. -/
theorem lineCount_succ_start_of_pos (n a b : ℕ) (ha : 0 < a) :
    lineCount (n + 1) a b = lineCount n (a - 1) b + lineCount n (a + 1) b := by
  induction n generalizing a b with
  | zero =>
      simp only [lineCount]
      split_ifs <;> simp_all <;> omega
  | succ n ih =>
      by_cases hb : b = 0
      · simp [hb]
      · have hb' : 0 < b := Nat.pos_of_ne_zero hb
        rw [lineCount_succ_of_pos (n + 1) a b hb', ih a (b - 1) ha, ih a (b + 1) ha,
          lineCount_succ_of_pos n (a - 1) b hb',
          lineCount_succ_of_pos n (a + 1) b hb']
        omega

/-- Reversing a positive walk exchanges its endpoints. -/
theorem lineCount_symm (n a b : ℕ) : lineCount n a b = lineCount n b a := by
  induction n generalizing a b with
  | zero =>
      simp only [lineCount]
      split_ifs <;> simp_all <;> omega
  | succ n ih =>
      by_cases hb : b = 0
      · simp [hb]
      · have hb' : 0 < b := Nat.pos_of_ne_zero hb
        rw [lineCount_succ_of_pos n a b hb', lineCount_succ_start_of_pos n b a hb',
          ih a (b - 1), ih a (b + 1)]

/-- Appending two steps at the boundary gives the `1`-to-`3` entry from returns. -/
theorem lineCount_add_two_one_one (n : ℕ) :
    lineCount (n + 2) 1 1 = lineCount n 1 1 + lineCount n 1 3 := by
  calc
    _ = lineCount (n + 1) 1 2 := by
      rw [lineCount_succ_of_pos (n + 1) 1 1 (by decide)]
      simp
    _ = _ := by simpa using lineCount_succ_of_pos n 1 2 (by decide)

/-- Applying the boundary recurrence at the other end gives the `3`-to-`3` entry. -/
theorem lineCount_add_two_one_three (n : ℕ) :
    lineCount (n + 2) 1 3 = lineCount n 1 3 + lineCount n 3 3 := by
  calc
    _ = lineCount (n + 1) 2 3 := by
      rw [lineCount_succ_start_of_pos (n + 1) 1 3 (by decide)]
      simp
    _ = _ := by simpa using lineCount_succ_start_of_pos n 2 3 (by decide)

end TranscendentalTuran.Green.Walks
