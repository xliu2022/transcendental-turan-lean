/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Walks.Kernel
public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace TranscendentalTuran.Green.Walks

/-- The positive-half-line nearest-neighbor walk kernel.  Vertex zero is absorbing;
a walk is counted only if every vertex, including its initial vertex, is positive. -/
def lineCount : ℕ → ℕ → ℕ → ℕ
  | 0, a, b => if a = b ∧ b ≠ 0 then 1 else 0
  | n + 1, a, b => if b = 0 then 0 else
      lineCount n a (b - 1) + lineCount n a (b + 1)

@[simp] theorem lineCount_zero_end (n a : ℕ) : lineCount n a 0 = 0 := by
  cases n <;> simp [lineCount]

theorem lineCount_succ_of_pos (n a b : ℕ) (hb : 0 < b) :
    lineCount (n + 1) a b = lineCount n a (b - 1) + lineCount n a (b + 1) := by
  simp [lineCount, Nat.ne_of_gt hb]

/-- The antisymmetrized product of two half-line kernels started at `1` and `3`. -/
def pairDet (n a b : ℕ) : ℤ :=
  (lineCount n 1 a : ℤ) * lineCount n 3 b -
    (lineCount n 1 b : ℤ) * lineCount n 3 a

@[simp] theorem pairDet_zero_left (n b : ℕ) : pairDet n 0 b = 0 := by
  simp [pairDet]

@[simp] theorem pairDet_diagonal (n a : ℕ) : pairDet n a a = 0 := by
  simp [pairDet]

/-- Algebraic version of cancellation at a first meeting: the determinant obeys
simultaneous independent nearest-neighbor transitions. -/
theorem pairDet_succ (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    pairDet (n + 1) a b =
      pairDet n (a - 1) (b - 1) + pairDet n (a - 1) (b + 1) +
      pairDet n (a + 1) (b - 1) + pairDet n (a + 1) (b + 1) := by
  unfold pairDet
  rw [lineCount_succ_of_pos n 1 a ha, lineCount_succ_of_pos n 3 b hb,
    lineCount_succ_of_pos n 1 b hb, lineCount_succ_of_pos n 3 a ha]
  push_cast
  ring

/-- The coordinate map `(i,j) ↦ (i+1,i+2j+3)` separates the walkers by an even gap. -/
def quadrantDet (n i j : ℕ) : ℤ := pairDet n (i + 1) (i + 2 * j + 3)

@[simp] theorem quadrantDet_zero (i j : ℕ) :
    quadrantDet 0 i j = if i = 0 ∧ j = 0 then 1 else 0 := by
  unfold quadrantDet pairDet lineCount
  split_ifs <;> norm_num at * <;> omega

theorem quadrantDet_succ (n i j : ℕ) :
    quadrantDet (n + 1) i j =
      quadrantDet n (i + 1) j + (if i = 0 then 0 else quadrantDet n (i - 1) j) +
      (if i = 0 then 0 else quadrantDet n (i - 1) (j + 1)) +
      (if j = 0 then 0 else quadrantDet n (i + 1) (j - 1)) := by
  rw [quadrantDet, pairDet_succ n _ _ (by omega) (by omega)]
  have h₁ : pairDet n (i + 1 - 1) (i + 2 * j + 3 - 1) =
      if i = 0 then 0 else quadrantDet n (i - 1) j := by
    cases i with
    | zero => simp
    | succ i =>
        simp only [Nat.succ_ne_zero, ↓reduceIte]
        unfold quadrantDet
        congr 1 <;> omega
  have h₂ : pairDet n (i + 1 - 1) (i + 2 * j + 3 + 1) =
      if i = 0 then 0 else quadrantDet n (i - 1) (j + 1) := by
    cases i with
    | zero => simp
    | succ i =>
        simp only [Nat.succ_ne_zero, ↓reduceIte]
        unfold quadrantDet
        congr 1 <;> omega
  have h₃ : pairDet n (i + 1 + 1) (i + 2 * j + 3 - 1) =
      if j = 0 then 0 else quadrantDet n (i + 1) (j - 1) := by
    cases j with
    | zero => simpa using pairDet_diagonal n (i + 2)
    | succ j =>
        simp only [Nat.succ_ne_zero, ↓reduceIte]
        unfold quadrantDet
        congr 1 <;> omega
  have h₄ : pairDet n (i + 1 + 1) (i + 2 * j + 3 + 1) =
      quadrantDet n (i + 1) j := by
    unfold quadrantDet
    congr 1 <;> omega
  rw [h₁, h₂, h₃, h₄]
  ring

/-- A direct recurrence proof of the two-walker determinant formula for every endpoint.
The left side is the cardinality of the actual finite direction-word set. -/
theorem count_eq_determinant (n i j : ℕ) :
    (count n (i, j) : ℤ) = quadrantDet n i j := by
  induction n generalizing i j with
  | zero => simp only [count_zero, quadrantDet_zero]; split_ifs <;> rfl
  | succ n ih =>
      rw [count_succ, quadrantDet_succ]
      by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
        simp [hi, hj, Nat.cast_add, ih]

theorem card_words_eq_determinant (n i j : ℕ) :
    ((words n (i, j)).card : ℤ) = quadrantDet n i j := by
  rw [card_words, count_eq_determinant]

/-- The corner-return determinant, before evaluating its one-dimensional entries. -/
theorem corner_count_eq_determinant (n : ℕ) :
    (count n (0, 0) : ℤ) =
      (lineCount n 1 1 : ℤ) * lineCount n 3 3 -
        (lineCount n 1 3 : ℤ) * lineCount n 3 1 := by
  simpa only [quadrantDet, pairDet, Nat.zero_add, Nat.mul_zero] using
    count_eq_determinant n 0 0

end TranscendentalTuran.Green.Walks
