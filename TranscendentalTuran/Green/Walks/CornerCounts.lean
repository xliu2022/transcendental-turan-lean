/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Walks.HalfLineCatalan
public import TranscendentalTuran.Green.Walks.HalfLineRecurrence

@[expose] public section

open Finset DyckStep

namespace TranscendentalTuran.Green.Walks

theorem lineCount_even_one_three (n : ℕ) :
    (lineCount (2 * n) 1 3 : ℤ) = (catalan (n + 1) : ℤ) - catalan n := by
  have h := lineCount_add_two_one_one (2 * n)
  have hn : 2 * n + 2 = 2 * (n + 1) := by omega
  rw [hn, lineCount_even_one, lineCount_even_one] at h
  have hc : (catalan (n + 1) : ℤ) =
      (catalan n : ℤ) + (lineCount (2 * n) 1 3 : ℤ) := by exact_mod_cast h
  omega

theorem lineCount_even_three_three (n : ℕ) :
    (lineCount (2 * n) 3 3 : ℤ) =
      (catalan (n + 2) : ℤ) - 2 * (catalan (n + 1) : ℤ) + catalan n := by
  have h := lineCount_add_two_one_three (2 * n)
  have hn : 2 * n + 2 = 2 * (n + 1) := by omega
  rw [hn] at h
  have hc : (lineCount (2 * (n + 1)) 1 3 : ℤ) =
      (lineCount (2 * n) 1 3 : ℤ) + (lineCount (2 * n) 3 3 : ℤ) := by exact_mod_cast h
  rw [lineCount_even_one_three, lineCount_even_one_three] at hc
  have hn' : n + 1 + 1 = n + 2 := by omega
  rw [hn'] at hc
  omega

/-- The determinant simplifies to the Catalan return-count formula. -/
theorem corner_count_even (n : ℕ) :
    (count (2 * n) (0, 0) : ℤ) =
      (catalan n : ℤ) * catalan (n + 2) - (catalan (n + 1) : ℤ) ^ 2 := by
  rw [corner_count_eq_determinant, lineCount_symm (2 * n) 3 1,
    lineCount_even_one, lineCount_even_one_three, lineCount_even_three_three]
  ring

/-- A positive one-dimensional return has even length. -/
theorem lineCount_odd_one (n : ℕ) : lineCount (2 * n + 1) 1 1 = 0 := by
  rw [← card_lineWords, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hlen, hbal, hpos⟩ := (mem_lineWords (2 * n + 1) 1 1 w).1 hw
  let p : DyckWord :=
    { toList := w
      count_U_eq_count_D := by omega
      count_D_le_count_U := fun k => by have h := hpos k; omega }
  have h := p.two_mul_semilength_eq_length
  change 2 * p.semilength = w.length at h
  omega

theorem lineCount_odd_one_three (n : ℕ) : lineCount (2 * n + 1) 1 3 = 0 := by
  have h := lineCount_add_two_one_one (2 * n + 1)
  have hn : 2 * n + 1 + 2 = 2 * (n + 1) + 1 := by omega
  rw [hn, lineCount_odd_one, lineCount_odd_one] at h
  omega

/-- Odd-length corner returns are impossible. -/
theorem corner_count_odd (n : ℕ) : count (2 * n + 1) (0, 0) = 0 := by
  have h := corner_count_eq_determinant (2 * n + 1)
  rw [lineCount_odd_one, lineCount_odd_one_three] at h
  simp only [Nat.cast_zero, zero_mul, sub_zero] at h
  exact_mod_cast h

end TranscendentalTuran.Green.Walks
