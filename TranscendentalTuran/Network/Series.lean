module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Series reduction and the scalar source bound

Formalization author and responsible maintainer: Xizhi Liu.
These are finite weighted inequalities, with no inverse-operator assumption.
-/

open scoped BigOperators

namespace TranscendentalTuran.Network

theorem series_reduction {I : Type*} (s : Finset I) (w d : I → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, d i) ^ 2 / (∑ i ∈ s, 1 / w i) ≤ ∑ i ∈ s, w i * d i ^ 2 := by
  have h := Finset.sq_sum_div_le_sum_sq_div s d
    (g := fun i => 1 / w i) (fun i hi => one_div_pos.mpr (hw i hi))
  simpa only [div_div_eq_mul_div, div_one, mul_comm] using h

theorem series_energy_eq {I : Type*} (s : Finset I) (w : I → ℝ)
    (_hw : ∀ i ∈ s, w i ≠ 0) (a R : ℝ) (hR : R ≠ 0)
    (hres : ∑ i ∈ s, 1 / w i = R) :
    (∑ i ∈ s, w i * (a / (R * w i)) ^ 2) = a ^ 2 / R := by
  calc
    _ = ∑ i ∈ s, (a ^ 2 / R ^ 2) * (1 / w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      field_simp
    _ = (a ^ 2 / R ^ 2) * (∑ i ∈ s, 1 / w i) := by rw [Finset.mul_sum]
    _ = a ^ 2 / R := by rw [hres]; field_simp

theorem series_total_drop {I : Type*} (s : Finset I) (w : I → ℝ)
    (a R : ℝ) (hR : R ≠ 0) (hres : ∑ i ∈ s, 1 / w i = R) :
    (∑ i ∈ s, a / (R * w i)) = a := by
  calc
    _ = ∑ i ∈ s, (a / R) * (1 / w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (a / R) * (∑ i ∈ s, 1 / w i) := by rw [Finset.mul_sum]
    _ = a := by rw [hres]; exact div_mul_cancel₀ a hR

/-- Adding an incidence replaces two singleton squares by a difference square. -/
theorem completing_edge_decreases_energy {x y w : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) :
    w * (x - y) ^ 2 ≤ w * (x ^ 2 + y ^ 2) := by
  have hxy := mul_nonneg hx hy
  exact mul_le_mul_of_nonneg_left (by nlinarith) hw

/-- The one-variable maximization used after the network energy bound. -/
theorem source_gain_bound {J a E g c : ℝ} (hg : 0 < g) (hc : 0 < c)
    (henergy : c * a ^ 2 ≤ g * E) :
    J * a - E / 2 ≤ J ^ 2 * g / (2 * c) := by
  have hs : 0 ≤ (c * a - J * g) ^ 2 := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left henergy (le_of_lt hc)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * c)).mpr
  have hgscaled : 0 ≤ g * (J ^ 2 * g - (J * a - E / 2) * (2 * c)) := by
    nlinarith
  have hnonneg := nonneg_of_mul_nonneg_right hgscaled hg
  linarith

end TranscendentalTuran.Network
