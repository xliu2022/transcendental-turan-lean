/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! # Elementary energy bounds used by the network construction -/

namespace TranscendentalTuran.Green

/-- The final scalar completion of squares in the source-gain upper bound. -/
theorem source_gain_bound {a E J c g : ℝ} (hc : 0 < c) (hg : 0 < g)
    (hE : c * a ^ 2 ≤ g * E) :
    J * a - E / 2 ≤ J ^ 2 * g / (2 * c) := by
  apply (le_div_iff₀ (by positivity : 0 < 2 * c)).2
  have hmul := mul_le_mul_of_nonneg_left hE hc.le
  have hsq := sq_nonneg (c * a - g * J)
  have h : g * ((J * a - E / 2) * (2 * c)) ≤ g * (J ^ 2 * g) := by
    nlinarith
  exact le_of_mul_le_mul_left h hg

/-- The lower construction's finite Green identity gives its exact gain. -/
theorem truncated_source_gain {J R g₁ g₂ : ℝ} (hR : R ≠ 0) :
    J * (J * R * g₁) - ((1 / R) * (J * R) ^ 2 * (2 * g₁ - g₂)) / 2 =
      (J ^ 2 * R / 2) * g₂ := by
  field_simp
  ring

end TranscendentalTuran.Green
