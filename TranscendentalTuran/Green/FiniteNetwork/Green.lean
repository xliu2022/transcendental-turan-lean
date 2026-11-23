/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.FiniteNetwork.Kernel
public import TranscendentalTuran.Green.CornerEvaluation
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

@[expose] public section

noncomputable section

open scoped BigOperators Matrix
open Finset

namespace TranscendentalTuran.Green.FiniteNetwork.DirectionalNetwork

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite marked Green vector, defined by its actual summable walk kernel. -/
def green (N : DirectionalNetwork V) (o v : V) : ℝ :=
  (1 / 4 : ℝ) * ∑' n, N.kernel o n v

theorem green_nonneg (N : DirectionalNetwork V) (o v : V) : 0 ≤ N.green o v := by
  apply mul_nonneg (by norm_num)
  exact tsum_nonneg fun n => N.kernel_nonneg o n v

theorem laplacian_mulVec (N : DirectionalNetwork V) (f : V → ℝ) (v : V) :
    (N.laplacian *ᵥ f) v = 4 * (f v - (N.transitionMatrix *ᵥ f) v) := by
  rw [laplacian, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [N.adjacency_mulVec, N.transition_mulVec]
  ring

theorem transition_tsum_kernel (N : DirectionalNetwork V) {o : V}
    (φ : Projection N o) (v : V) :
    (N.transitionMatrix *ᵥ (fun w => ∑' n, N.kernel o n w)) v =
      ∑' n, N.kernel o (n + 1) v := by
  unfold Matrix.mulVec dotProduct
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum
    (fun w _ => (N.kernel_summable φ w).mul_left (N.transitionMatrix v w))]
  apply tsum_congr
  intro n
  exact (N.kernel_succ o n v).symm

/-- The Green series solves the grounded finite linear system. -/
theorem laplacian_green (N : DirectionalNetwork V) {o : V} (φ : Projection N o) (v : V) :
    (N.laplacian *ᵥ N.green o) v = if v = o then 1 else 0 := by
  rw [N.laplacian_mulVec]
  have hT : (N.transitionMatrix *ᵥ N.green o) v =
      (1 / 4 : ℝ) * ∑' n, N.kernel o (n + 1) v := by
    change (N.transitionMatrix *ᵥ
      ((1 / 4 : ℝ) • (fun w => ∑' n, N.kernel o n w))) v = _
    rw [Matrix.mulVec_smul]
    change (1 / 4 : ℝ) *
      (N.transitionMatrix *ᵥ (fun w => ∑' n, N.kernel o n w)) v = _
    rw [N.transition_tsum_kernel φ v]
  rw [hT]
  unfold green
  have hs := (N.kernel_summable φ v).tsum_eq_zero_add
  rw [N.kernel_zero] at hs
  linarith

theorem sum_green_eq_survival (N : DirectionalNetwork V) {o : V} (φ : Projection N o) :
    (∑ v, N.green o v) = (1 / 4 : ℝ) * ∑' n, N.survival n o := by
  unfold green
  rw [← Finset.mul_sum]
  congr 1
  rw [← Summable.tsum_finsetSum (fun v _ => N.kernel_summable φ v)]
  exact tsum_congr fun n => N.sum_kernel_eq_survival o n

/-- A finite projected host has total Green mass at most `1/2`. -/
theorem sum_green_le_half (N : DirectionalNetwork V) {o : V} (φ : Projection N o) :
    (∑ v, N.green o v) ≤ 1 / 2 := by
  have hcmp : ∀ n, N.survival n o ≤ Walks.survival n (0, 0) := by
    intro n
    simpa only [φ.root] using N.survival_le_quadrant φ n o
  have hs := Summable.tsum_le_tsum hcmp (N.survival_summable φ o)
    (Walks.survival_summable (0, 0))
  rw [N.sum_green_eq_survival φ]
  exact (mul_le_mul_of_nonneg_left hs (by norm_num)).trans
    Walks.quarter_tsum_survival_corner_le

/-- Unique directional lifts bound the marked Green entry by the actual quadrant
corner value, even when different host vertices share coordinates. -/
theorem green_root_le_corner (N : DirectionalNetwork V) {o : V} (φ : Projection N o) :
    N.green o o ≤ cornerGreen := by
  have hcmp : ∀ n, (1 / 4 : ℝ) * N.kernel o n o ≤ cornerReturn n := by
    intro n
    calc
      _ ≤ (1 / 4 : ℝ) * Walks.kernelProbability n (φ.coord o) :=
        mul_le_mul_of_nonneg_left (N.kernel_le_quadrant φ n o) (by norm_num)
      _ = cornerReturn n := by
        rw [φ.root]
        unfold Walks.kernelProbability cornerReturn
        rw [pow_succ]
        field_simp
  calc
    _ = ∑' n, (1 / 4 : ℝ) * N.kernel o n o := tsum_mul_left.symm
    _ ≤ ∑' n, cornerReturn n :=
      Summable.tsum_le_tsum hcmp ((N.kernel_summable φ o).mul_left (1 / 4))
        hasSum_cornerReturn.summable
    _ = cornerGreen := rfl

end TranscendentalTuran.Green.FiniteNetwork.DirectionalNetwork
