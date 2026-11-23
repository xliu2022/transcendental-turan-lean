/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.CatalanSeries
public import TranscendentalTuran.Green.Walks.CornerCounts
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

@[expose] public section

noncomputable section

open scoped BigOperators Topology
open Filter

namespace TranscendentalTuran.Green

/-- The actual normalized length-`k` corner-return count. -/
def cornerReturn (k : ℕ) : ℝ := (Walks.count k (0, 0) : ℝ) / 4 ^ (k + 1)

/-- The Green value of the concrete killed quadrant walk. -/
def cornerGreen : ℝ := ∑' k, cornerReturn k

theorem cornerReturn_nonneg (k : ℕ) : 0 ≤ cornerReturn k := by
  unfold cornerReturn
  positivity

@[simp] theorem cornerReturn_zero : cornerReturn 0 = 1 / 4 := by
  norm_num [cornerReturn, Walks.count]

theorem cornerReturn_even (n : ℕ) : cornerReturn (2 * n) = greenTerm n := by
  have h : (Walks.count (2 * n) (0, 0) : ℝ) =
      (catalan n : ℝ) * (catalan (n + 2) : ℝ) - (catalan (n + 1) : ℝ) ^ 2 := by
    exact_mod_cast Walks.corner_count_even n
  unfold cornerReturn greenTerm scaledCatalan
  rw [h]
  rw [show 2 * n + 1 = n + n + 1 by omega]
  simp only [pow_add]
  field_simp

@[simp] theorem cornerReturn_odd (n : ℕ) : cornerReturn (2 * n + 1) = 0 := by
  simp [cornerReturn, Walks.corner_count_odd]

/-- The complete quadrant corner Green evaluation, with all coefficients interpreted
as actual finite sets of legal direction words. -/
theorem hasSum_cornerReturn : HasSum cornerReturn (22 - 1024 / (15 * Real.pi)) := by
  have he : HasSum (fun n => cornerReturn (2 * n)) (22 - 1024 / (15 * Real.pi)) := by
    simpa only [cornerReturn_even] using hasSum_greenTerm
  have ho : HasSum (fun n => cornerReturn (2 * n + 1)) (0 : ℝ) := by
    simpa only [cornerReturn_odd] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  simpa only [add_zero] using he.even_add_odd ho

theorem cornerGreen_eq : cornerGreen = 22 - 1024 / (15 * Real.pi) :=
  hasSum_cornerReturn.tsum_eq

theorem quarter_le_cornerGreen : (1 / 4 : ℝ) ≤ cornerGreen := by
  simpa only [cornerReturn_zero, cornerGreen] using
    hasSum_cornerReturn.summable.le_tsum 0 (fun k _ => cornerReturn_nonneg k)

theorem tendsto_partial_cornerReturn :
    Tendsto (fun n => ∑ k ∈ Finset.range n, cornerReturn k) atTop (𝓝 cornerGreen) :=
  hasSum_cornerReturn.summable.hasSum.tendsto_sum_nat

end TranscendentalTuran.Green
