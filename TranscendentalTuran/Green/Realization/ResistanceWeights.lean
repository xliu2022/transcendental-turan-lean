/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.BoxWeights
public import TranscendentalTuran.Network.Series

@[expose] public section

noncomputable section

open scoped BigOperators

namespace TranscendentalTuran.Green.Realization

open Network

/-- Series resistance of the four matching-block conductances. -/
def totalResistance (W : Fin 4 → ℝ) : ℝ := ∑ b, (W b)⁻¹

theorem totalResistance_eq (W : Fin 4 → ℝ) :
    totalResistance W = (W 0)⁻¹ + (W 1)⁻¹ + (W 2)⁻¹ + (W 3)⁻¹ := by
  simp [totalResistance, Fin.sum_univ_succ]
  ring

theorem totalResistance_pos {W : Fin 4 → ℝ} (hW : ∀ b, 0 < W b) : 0 < totalResistance W := by
  apply Finset.sum_pos
  · intro b _
    exact inv_pos.mpr (hW b)
  · exact Finset.univ_nonempty

/-- Resistance-coordinate interpolation, in the color orders `0,1,3,2` and
`1,0,2,3` prescribed for horizontal and diagonal chains. -/
def resistanceInterpolation (W : Fin 4 → ℝ) : Interpolation :=
  ![![(W 0)⁻¹ / totalResistance W,
      ((W 0)⁻¹ + (W 1)⁻¹) / totalResistance W,
      ((W 0)⁻¹ + (W 1)⁻¹ + (W 3)⁻¹) / totalResistance W],
    ![(W 1)⁻¹ / totalResistance W,
      ((W 1)⁻¹ + (W 0)⁻¹) / totalResistance W,
      ((W 1)⁻¹ + (W 0)⁻¹ + (W 2)⁻¹) / totalResistance W]]

theorem resistanceInterpolation_bounds {W : Fin 4 → ℝ} (hW : ∀ b, 0 < W b)
    (a : Fin 2) (k : Fin 3) :
    0 ≤ resistanceInterpolation W a k ∧ resistanceInterpolation W a k ≤ 1 := by
  have hR := totalResistance_pos hW
  have h0 := inv_pos.mpr (hW 0)
  have h1 := inv_pos.mpr (hW 1)
  have h2 := inv_pos.mpr (hW 2)
  have h3 := inv_pos.mpr (hW 3)
  fin_cases a <;> fin_cases k <;> dsimp [resistanceInterpolation]
  all_goals constructor
  all_goals first
    | (apply div_nonneg <;> linarith)
    | (apply (div_le_one hR).mpr; rw [totalResistance_eq]; linarith)

private theorem left_blend (t a b : ℝ) : a - blend t a b = t * (a - b) := by
  unfold blend
  ring

private theorem blend_difference (s t a b : ℝ) :
    blend s a b - blend t a b = (t - s) * (a - b) := by
  unfold blend
  ring

private theorem right_blend (t a b : ℝ) : blend t a b - b = (1 - t) * (a - b) := by
  unfold blend
  ring

private theorem last_fraction {R r s : ℝ} (hR : R ≠ 0) (h : r + s = R) :
    1 - r / R = s / R := by
  apply (eq_div_iff hR).mpr
  field_simp
  linarith

private theorem drop_fraction (w R a b : ℝ) : w⁻¹ / R * (a - b) = (a - b) / (R * w) := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The four resistor squares of one horizontal chain, including an omitted
endpoint represented by weight zero. -/
def eChainEnergy (W : Fin 4 → ℝ) (a b : ℝ) : ℝ :=
  let θ := resistanceInterpolation W
  W 0 * (a - blend (θ 0 0) a b) ^ 2 +
  W 1 * (blend (θ 0 0) a b - blend (θ 0 1) a b) ^ 2 +
  W 3 * (blend (θ 0 1) a b - blend (θ 0 2) a b) ^ 2 +
  W 2 * (blend (θ 0 2) a b - b) ^ 2

def dChainEnergy (W : Fin 4 → ℝ) (a b : ℝ) : ℝ :=
  let θ := resistanceInterpolation W
  W 1 * (a - blend (θ 1 0) a b) ^ 2 +
  W 0 * (blend (θ 1 0) a b - blend (θ 1 1) a b) ^ 2 +
  W 2 * (blend (θ 1 1) a b - blend (θ 1 2) a b) ^ 2 +
  W 3 * (blend (θ 1 2) a b - b) ^ 2

/-- Equality in the four-resistor series reduction at the chosen interpolation. -/
theorem eChainEnergy_eq {W : Fin 4 → ℝ} (hW : ∀ b, 0 < W b) (a b : ℝ) :
    eChainEnergy W a b = (a - b) ^ 2 / totalResistance W := by
  have hR := (totalResistance_pos hW).ne'
  have hlast : 1 - ((W 0)⁻¹ + (W 1)⁻¹ + (W 3)⁻¹) / totalResistance W =
      (W 2)⁻¹ / totalResistance W := by
    apply last_fraction hR
    rw [totalResistance_eq]
    ring
  have hs := series_energy_eq Finset.univ W (fun i _ => (hW i).ne') (a - b)
    (totalResistance W) hR (by simp only [one_div, totalResistance])
  calc
    _ = ∑ i : Fin 4, W i * ((a - b) / (totalResistance W * W i)) ^ 2 := by
      dsimp [eChainEnergy, resistanceInterpolation]
      rw [left_blend, blend_difference, blend_difference, right_blend, hlast]
      have h1 : ((W 0)⁻¹ + (W 1)⁻¹) / totalResistance W - (W 0)⁻¹ / totalResistance W =
          (W 1)⁻¹ / totalResistance W := by ring
      have h3 : ((W 0)⁻¹ + (W 1)⁻¹ + (W 3)⁻¹) / totalResistance W -
          ((W 0)⁻¹ + (W 1)⁻¹) / totalResistance W = (W 3)⁻¹ / totalResistance W := by ring
      rw [h1, h3]
      simp [drop_fraction, Fin.sum_univ_succ]
      ring
    _ = _ := hs

theorem dChainEnergy_eq {W : Fin 4 → ℝ} (hW : ∀ b, 0 < W b) (a b : ℝ) :
    dChainEnergy W a b = (a - b) ^ 2 / totalResistance W := by
  have hR := (totalResistance_pos hW).ne'
  have hlast : 1 - ((W 1)⁻¹ + (W 0)⁻¹ + (W 2)⁻¹) / totalResistance W =
      (W 3)⁻¹ / totalResistance W := by
    apply last_fraction hR
    rw [totalResistance_eq]
    ring
  have hs := series_energy_eq Finset.univ W (fun i _ => (hW i).ne') (a - b)
    (totalResistance W) hR (by simp only [one_div, totalResistance])
  calc
    _ = ∑ i : Fin 4, W i * ((a - b) / (totalResistance W * W i)) ^ 2 := by
      dsimp [dChainEnergy, resistanceInterpolation]
      rw [left_blend, blend_difference, blend_difference, right_blend, hlast]
      have h0 : ((W 1)⁻¹ + (W 0)⁻¹) / totalResistance W - (W 1)⁻¹ / totalResistance W =
          (W 0)⁻¹ / totalResistance W := by ring
      have h2 : ((W 1)⁻¹ + (W 0)⁻¹ + (W 2)⁻¹) / totalResistance W -
          ((W 1)⁻¹ + (W 0)⁻¹) / totalResistance W = (W 2)⁻¹ / totalResistance W := by ring
      rw [h0, h2]
      simp [drop_fraction, Fin.sum_univ_succ]
      ring
    _ = _ := hs

end TranscendentalTuran.Green.Realization
