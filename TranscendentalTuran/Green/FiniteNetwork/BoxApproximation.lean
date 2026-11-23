/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.FiniteNetwork.Box
public import TranscendentalTuran.Green.FiniteNetwork.Green

@[expose] public section

noncomputable section

open scoped BigOperators Topology
open Finset Filter

namespace TranscendentalTuran.Green.FiniteNetwork

/-- Marked value of the actual finite-box Green vector. -/
def boxGreenValue (N : ℕ) : ℝ :=
  (boxNetwork N).green (boxRoot N) (boxRoot N)

theorem boxGreen_nonneg (N : ℕ) (v : Box N) :
    0 ≤ (boxNetwork N).green (boxRoot N) v :=
  (boxNetwork N).green_nonneg (boxRoot N) v

theorem boxGreen_mass_le_half (N : ℕ) :
    (∑ v, (boxNetwork N).green (boxRoot N) v) ≤ 1 / 2 :=
  (boxNetwork N).sum_green_le_half (boxProjection N)

theorem boxGreenValue_le_corner (N : ℕ) : boxGreenValue N ≤ cornerGreen :=
  (boxNetwork N).green_root_le_corner (boxProjection N)

/-- Every return of length at most the box size appears in its Green vector. -/
theorem partial_corner_le_boxGreenValue (N : ℕ) :
    (∑ k ∈ range (N + 1), cornerReturn k) ≤ boxGreenValue N := by
  have hsum := ((boxNetwork N).kernel_summable (boxProjection N) (boxRoot N)).mul_left
    (1 / 4 : ℝ)
  calc
    _ = ∑ k ∈ range (N + 1),
        (1 / 4 : ℝ) * (boxNetwork N).kernel (boxRoot N) k (boxRoot N) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [box_kernel_eq_quadrant (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
      unfold Walks.kernelProbability cornerReturn
      simp only [boxCoord, boxRoot, Fin.val_zero]
      rw [pow_succ]
      field_simp
    _ ≤ ∑' k, (1 / 4 : ℝ) * (boxNetwork N).kernel (boxRoot N) k (boxRoot N) :=
      Summable.sum_le_tsum (range (N + 1))
        (fun k _ => mul_nonneg (by norm_num)
          ((boxNetwork N).kernel_nonneg (boxRoot N) k (boxRoot N))) hsum
    _ = boxGreenValue N := tsum_mul_left

/-- The finite-box Green values approach the exact infinite quadrant value. -/
theorem tendsto_boxGreenValue : Tendsto boxGreenValue atTop (𝓝 cornerGreen) := by
  have hpartial : Tendsto
      (fun N => ∑ k ∈ range (N + 1), cornerReturn k) atTop (𝓝 cornerGreen) := by
    simpa only [Function.comp_def] using
      tendsto_partial_cornerReturn.comp (tendsto_add_atTop_nat 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hpartial tendsto_const_nhds
    partial_corner_le_boxGreenValue boxGreenValue_le_corner

end TranscendentalTuran.Green.FiniteNetwork
