/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.FiniteNetwork.Basic

@[expose] public section

noncomputable section

open scoped BigOperators Matrix
open Finset

namespace TranscendentalTuran.Green.FiniteNetwork.DirectionalNetwork

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The normalized finite-host kernel from `v` to its mark `o`. -/
def kernel (N : DirectionalNetwork V) (o : V) (n : ℕ) (v : V) : ℝ :=
  (N.transitionMatrix ^ n) v o

@[simp] theorem kernel_zero (N : DirectionalNetwork V) (o v : V) :
    N.kernel o 0 v = if v = o then 1 else 0 := by
  simp [kernel, Matrix.one_apply]

theorem kernel_succ (N : DirectionalNetwork V) (o : V) (n : ℕ) (v : V) :
    N.kernel o (n + 1) v = (N.transitionMatrix *ᵥ N.kernel o n) v := by
  simp only [kernel, pow_succ', Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem kernel_nonneg (N : DirectionalNetwork V) (o : V) (n : ℕ) (v : V) :
    0 ≤ N.kernel o n v := by
  induction n generalizing v with
  | zero => simp only [kernel_zero]; split_ifs <;> norm_num
  | succ n ih =>
      rw [kernel_succ]
      exact N.transition_mulVec_nonneg ih v

/-- Direction-word comparison is expressed directly by the endpoint recurrences.
The coordinate map may identify distinct vertices. -/
theorem kernel_le_quadrant (N : DirectionalNetwork V) {o : V} (φ : Projection N o)
    (n : ℕ) (v : V) : N.kernel o n v ≤ Walks.kernelProbability n (φ.coord v) := by
  induction n generalizing v with
  | zero =>
      by_cases hv : v = o
      · subst v
        simp [φ.root]
      · simp only [kernel_zero, hv, ↓reduceIte]
        exact Walks.kernelProbability_nonneg 0 (φ.coord v)
  | succ n ih =>
      rw [kernel_succ, Walks.kernelProbability_succ]
      exact (N.transition_mulVec_mono ih v).trans
        (N.transition_project_le φ (Walks.kernelProbability_nonneg n) v)

/-- Total normalized mass of finite-host walks from a vertex. -/
def survival (N : DirectionalNetwork V) (n : ℕ) (v : V) : ℝ :=
  ∑ w, (N.transitionMatrix ^ n) v w

@[simp] theorem survival_zero (N : DirectionalNetwork V) (v : V) : N.survival 0 v = 1 := by
  simp [survival, Matrix.one_apply]

theorem survival_succ (N : DirectionalNetwork V) (n : ℕ) (v : V) :
    N.survival (n + 1) v = (N.transitionMatrix *ᵥ N.survival n) v := by
  simp only [survival, pow_succ', Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_comm

theorem survival_nonneg (N : DirectionalNetwork V) (n : ℕ) (v : V) : 0 ≤ N.survival n v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [survival_succ]
      exact N.transition_mulVec_nonneg ih v

theorem survival_le_quadrant (N : DirectionalNetwork V) {o : V} (φ : Projection N o)
    (n : ℕ) (v : V) : N.survival n v ≤ Walks.survival n (φ.coord v) := by
  induction n generalizing v with
  | zero => simp [Walks.survival]
  | succ n ih =>
      rw [survival_succ]
      exact (N.transition_mulVec_mono ih v).trans
        (N.transition_project_le φ (Walks.survival_nonneg n) v)

theorem power_symm (N : DirectionalNetwork V) (n : ℕ) (v w : V) :
    (N.transitionMatrix ^ n) v w = (N.transitionMatrix ^ n) w v := by
  have hT : N.transitionMatrix.transpose = N.transitionMatrix := by
    ext a b
    exact N.transition_symm b a
  have hn : (N.transitionMatrix ^ n).transpose = N.transitionMatrix ^ n := by
    rw [Matrix.transpose_pow, hT]
  exact congrArg (fun A : Matrix V V ℝ => A w v) hn

/-- Symmetry equates the marked column mass and the survival row mass. -/
theorem sum_kernel_eq_survival (N : DirectionalNetwork V) (o : V) (n : ℕ) :
    (∑ v, N.kernel o n v) = N.survival n o := by
  unfold kernel survival
  apply Finset.sum_congr rfl
  intro v _
  exact N.power_symm n v o

theorem kernel_le_survival (N : DirectionalNetwork V) (o : V) (n : ℕ) (v : V) :
    N.kernel o n v ≤ N.survival n o := by
  calc
    _ ≤ ∑ w, N.kernel o n w :=
      Finset.single_le_sum (fun w _ => N.kernel_nonneg o n w) (Finset.mem_univ v)
    _ = _ := N.sum_kernel_eq_survival o n

theorem survival_summable (N : DirectionalNetwork V) {o : V} (φ : Projection N o) (v : V) :
    Summable (fun n => N.survival n v) :=
  Summable.of_nonneg_of_le (fun n => N.survival_nonneg n v)
    (fun n => N.survival_le_quadrant φ n v) (Walks.survival_summable (φ.coord v))

theorem kernel_summable (N : DirectionalNetwork V) {o : V} (φ : Projection N o) (v : V) :
    Summable (fun n => N.kernel o n v) :=
  Summable.of_nonneg_of_le (fun n => N.kernel_nonneg o n v)
    (fun n => N.kernel_le_survival o n v) (N.survival_summable φ o)

end TranscendentalTuran.Green.FiniteNetwork.DirectionalNetwork
