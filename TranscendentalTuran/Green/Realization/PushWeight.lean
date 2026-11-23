/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.PartialInverse
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

open scoped BigOperators

namespace TranscendentalTuran.Green.Realization

/-- Change variables in a weighted sum along a finite embedding. -/
theorem sum_pushWeight_mul {A B : Type*} [Fintype A] [Fintype B]
    (e : A ↪ B) (x : A → ℝ) (f : B → ℝ) :
    (∑ b, pushWeight e x b * f b) = ∑ a, x a * f (e a) := by
  classical
  simp_rw [pushWeight_eq_sum, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [eq_comm]

theorem pushWeight_sq {A B : Type*} (e : A ↪ B) (x : A → ℝ) (b : B) :
    pushWeight e x b ^ 2 = pushWeight e (fun a => x a ^ 2) b := by
  unfold pushWeight
  cases partialInverse e b <;> simp

theorem sum_pushWeight_sq {A B : Type*} [Fintype A] [Fintype B]
    (e : A ↪ B) (x : A → ℝ) :
    (∑ b, pushWeight e x b ^ 2) = ∑ a, x a ^ 2 := by
  simp_rw [pushWeight_sq]
  exact sum_pushWeight e _

/-- Expanding all chain endpoint squares accounts for both copies of the base mass. -/
theorem sum_endpoint_squares {A B : Type*} [Fintype A] [Fintype B]
    (e f : A ↪ B) (x : A → ℝ) :
    (∑ b, (pushWeight e x b - pushWeight f x b) ^ 2) =
      2 * (∑ a, x a ^ 2) - 2 * (∑ b, pushWeight e x b * pushWeight f x b) := by
  calc
    _ = (∑ b, pushWeight e x b ^ 2) + (∑ b, pushWeight f x b ^ 2) -
        2 * (∑ b, pushWeight e x b * pushWeight f x b) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [sum_pushWeight_sq, sum_pushWeight_sq]; ring

end TranscendentalTuran.Green.Realization
