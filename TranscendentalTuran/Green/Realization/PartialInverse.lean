/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Option.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section

open scoped BigOperators

namespace TranscendentalTuran.Green.Realization

/-- The partial inverse of an embedding, used to omit the outside endpoint of a
boundary chain without adding an additional base vertex. -/
def partialInverse {A B : Type*} (e : A ↪ B) (b : B) : Option A := by
  classical
  exact if h : ∃ a, e a = b then some h.choose else none

theorem partialInverse_some_iff {A B : Type*} (e : A ↪ B) (a : A) (b : B) :
    partialInverse e b = some a ↔ e a = b := by
  classical
  by_cases h : ∃ a, e a = b
  · rw [partialInverse, dite_eq_left h, Option.some.injEq]
    constructor
    · intro ha
      exact ha ▸ h.choose_spec
    · intro ha
      exact e.injective (h.choose_spec.trans ha.symm)
  · simp only [partialInverse, dite_eq_right h, reduceCtorEq, false_iff]
    exact fun ha => h ⟨a, ha⟩

@[simp] theorem partialInverse_apply {A B : Type*} (e : A ↪ B) (a : A) :
    partialInverse e (e a) = some a := (partialInverse_some_iff e a (e a)).mpr rfl

/-- Extend weights by zero along a finite embedding. -/
def pushWeight {A B : Type*} (e : A ↪ B) (x : A → ℝ) (b : B) : ℝ :=
  (partialInverse e b).elim 0 x

theorem pushWeight_nonneg {A B : Type*} (e : A ↪ B) {x : A → ℝ}
    (hx : ∀ a, 0 ≤ x a) (b : B) : 0 ≤ pushWeight e x b := by
  unfold pushWeight
  cases partialInverse e b with
  | none => simp
  | some a => exact hx a

@[simp] theorem pushWeight_apply {A B : Type*} (e : A ↪ B) (x : A → ℝ) (a : A) :
    pushWeight e x (e a) = x a := by simp [pushWeight]

theorem pushWeight_eq_sum {A B : Type*} [Fintype A] [DecidableEq B] (e : A ↪ B) (x : A → ℝ) (b : B) :
    pushWeight e x b = ∑ a, if e a = b then x a else 0 := by
  classical
  cases h : partialInverse e b with
  | none =>
      have hn : ∀ a, e a ≠ b := by
        intro a ha
        have hs := (partialInverse_some_iff e a b).mpr ha
        rw [h] at hs
        cases hs
      simp [pushWeight, h, hn]
  | some a =>
      have ha := (partialInverse_some_iff e a b).mp h
      rw [show pushWeight e x b = x a by simp [pushWeight, h]]
      symm
      rw [Finset.sum_eq_single a]
      · simp [ha]
      · intro a' _ hne
        have hn : e a' ≠ b := fun hb => hne (e.injective (hb.trans ha.symm))
        simp [hn]
      · simp

/-- Extending by zero preserves total mass. -/
theorem sum_pushWeight {A B : Type*} [Fintype A] [Fintype B]
    (e : A ↪ B) (x : A → ℝ) : (∑ b, pushWeight e x b) = ∑ a, x a := by
  classical
  simp_rw [pushWeight_eq_sum]
  rw [Finset.sum_comm]
  simp

end TranscendentalTuran.Green.Realization
