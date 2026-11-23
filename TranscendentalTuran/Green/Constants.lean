/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.External.Pi.PiTranscendental
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! # The exact constant in the quadrant Green function -/

noncomputable section

namespace TranscendentalTuran.Green

/-- The arithmetic value computed by the corner-return series. -/
def value : ℝ := 22 - 1024 / (15 * Real.pi)

theorem pi_eq_rational_value : Real.pi = 1024 / (15 * (22 - value)) := by
  unfold value
  field_simp [Real.pi_ne_zero]
  ring

/-- Its transcendence is inherited from the checked external proof of π transcendence. -/
theorem value_transcendental : Transcendental ℚ value := by
  intro hv
  apply LeanFormalizations.Transcendence.transcendental_pi_axiomClean
  rw [pi_eq_rational_value]
  have hden : IsAlgebraic ℚ ((15 : ℝ) * (22 - value)) :=
    (isAlgebraic_natCast 15).mul ((isAlgebraic_natCast 22).sub hv)
  simpa only [Nat.cast_ofNat, div_eq_mul_inv] using (isAlgebraic_natCast 1024).mul hden.inv

/-- Elementary certified decimal bounds for π also locate the exact Green constant. -/
theorem quarter_lt_value : (1 / 4 : ℝ) < value := by
  have hpi : 0 < 15 * Real.pi := by positivity
  have hdiv : (1024 : ℝ) / (15 * Real.pi) < 87 / 4 := by
    apply (div_lt_iff₀ hpi).2
    nlinarith [Real.pi_gt_d2]
  unfold value
  linarith

theorem value_lt_half : value < (1 / 2 : ℝ) := by
  have hpi : 0 < 15 * Real.pi := by positivity
  have hdiv : (43 / 2 : ℝ) < 1024 / (15 * Real.pi) := by
    apply (lt_div_iff₀ hpi).2
    nlinarith [Real.pi_lt_d2]
  unfold value
  linarith

theorem value_pos : 0 < value := lt_trans (by norm_num) quarter_lt_value

theorem quarter_le_value : (1 / 4 : ℝ) ≤ value := quarter_lt_value.le

theorem value_le_half : value ≤ (1 / 2 : ℝ) := value_lt_half.le

end TranscendentalTuran.Green
