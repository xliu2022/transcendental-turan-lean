/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.FiniteNetwork.Energy
public import TranscendentalTuran.Green.FiniteNetwork.Green
public import TranscendentalTuran.Green.ScalarGain

@[expose] public section

noncomputable section

open scoped BigOperators Matrix
open Finset

namespace TranscendentalTuran.Green.FiniteNetwork.DirectionalNetwork

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pairing_green (N : DirectionalNetwork V) {o : V} (φ : Projection N o) (x : V → ℝ) :
    N.pairing x (N.green o) = x o := by
  simp [pairing, N.laplacian_green φ]

theorem energy_green (N : DirectionalNetwork V) {o : V} (φ : Projection N o) :
    N.energy (N.green o) = N.green o o := by
  rw [energy_eq_pairing, N.pairing_green φ]

/-- Green's identity and Cauchy--Schwarz in the actual finite grounded energy. -/
theorem marked_sq_le_energy (N : DirectionalNetwork V) {o : V} (φ : Projection N o)
    (x : V → ℝ) : (x o) ^ 2 ≤ N.energy x * cornerGreen := by
  have h := N.pairing_sq_le_energy_mul x (N.green o)
  rw [N.pairing_green φ, N.energy_green φ] at h
  exact h.trans (mul_le_mul_of_nonneg_left (N.green_root_le_corner φ) (N.energy_nonneg x))

/-- The full finite-network source-gain upper bound.  The external energy may include
additional nonnegative squares beyond this projected component. -/
theorem source_gain_of_energy (N : DirectionalNetwork V) {o : V} (φ : Projection N o)
    (x : V → ℝ) {J c E : ℝ} (hc : 0 < c) (hE : c * N.energy x ≤ E) :
    J * x o - E / 2 ≤ J ^ 2 * cornerGreen / (2 * c) := by
  have hg : 0 < cornerGreen := lt_of_lt_of_le (by norm_num) quarter_le_cornerGreen
  have hm := mul_le_mul_of_nonneg_left (N.marked_sq_le_energy φ x) hc.le
  have he := mul_le_mul_of_nonneg_left hE hg.le
  have hscalar : c * (x o) ^ 2 ≤ cornerGreen * E := by nlinarith
  exact TranscendentalTuran.Green.source_gain_bound hc hg hscalar

/-- Scaling the finite Green vector gives its exact source gain. -/
theorem scaled_green_gain (N : DirectionalNetwork V) {o : V} (φ : Projection N o)
    (J R : ℝ) (hR : R ≠ 0) :
    J * ((J * R) * N.green o o) -
      ((1 / R) * N.energy (fun v => (J * R) * N.green o v)) / 2 =
      (J ^ 2 * R / 2) * N.green o o := by
  rw [N.energy_const_mul, N.energy_green φ]
  field_simp <;> ring

theorem scaled_green_nonneg (N : DirectionalNetwork V) (o : V) {J R : ℝ}
    (hJ : 0 ≤ J) (hR : 0 ≤ R) (v : V) : 0 ≤ (J * R) * N.green o v :=
  mul_nonneg (mul_nonneg hJ hR) (N.green_nonneg o v)

/-- The base mass is at most `JR/2`, giving the paper's `JR` budget for a type
containing two copies of a chain position. -/
theorem scaled_green_mass_le_half (N : DirectionalNetwork V) {o : V} (φ : Projection N o)
    {J R : ℝ} (hJ : 0 ≤ J) (hR : 0 ≤ R) :
    (∑ v, (J * R) * N.green o v) ≤ J * R / 2 := by
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (N.sum_green_le_half φ) (mul_nonneg hJ hR)
  linarith

theorem twice_scaled_green_mass_le (N : DirectionalNetwork V) {o : V} (φ : Projection N o)
    {J R : ℝ} (hJ : 0 ≤ J) (hR : 0 ≤ R) :
    2 * (∑ v, (J * R) * N.green o v) ≤ J * R := by
  linarith [N.scaled_green_mass_le_half φ hJ hR]

end TranscendentalTuran.Green.FiniteNetwork.DirectionalNetwork
