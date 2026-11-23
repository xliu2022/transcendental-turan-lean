module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Grounded finite-network energy and Cauchy--Schwarz

Formalization author and responsible maintainer: Xizhi Liu.

All statements are finite real matrix identities. In particular the
Cauchy--Schwarz inequality allows a degenerate Laplacian and assumes no
inverse or unproved positive-definiteness assertion.
-/

namespace TranscendentalTuran.Optimization.MatrixEnergy

open Finset Matrix
open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def pairing (L : Matrix V V ℝ) (x y : V → ℝ) : ℝ :=
  ∑ v, x v * (L *ᵥ y) v

noncomputable def energy (L : Matrix V V ℝ) (x : V → ℝ) : ℝ := pairing L x x

noncomputable def laplacian (d : ℝ) (A : Matrix V V ℝ) : Matrix V V ℝ :=
  d • (1 : Matrix V V ℝ) - A

theorem pairing_symm (L : Matrix V V ℝ) (hL : ∀ v w, L v w = L w v)
    (x y : V → ℝ) : pairing L x y = pairing L y x := by
  simp only [pairing, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  rw [hL w v]
  ring

theorem pairing_add_left (L : Matrix V V ℝ) (x y z : V → ℝ) :
    pairing L (x + y) z = pairing L x z + pairing L y z := by
  simp only [pairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairing_add_right (L : Matrix V V ℝ) (x y z : V → ℝ) :
    pairing L x (y + z) = pairing L x y + pairing L x z := by
  simp only [pairing, Matrix.mulVec_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairing_smul_left (L : Matrix V V ℝ) (c : ℝ) (x y : V → ℝ) :
    pairing L (c • x) y = c * pairing L x y := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem pairing_smul_right (L : Matrix V V ℝ) (c : ℝ) (x y : V → ℝ) :
    pairing L x (c • y) = c * pairing L x y := by
  simp only [pairing, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem energy_line (L : Matrix V V ℝ) (hL : ∀ v w, L v w = L w v)
    (x y : V → ℝ) (t : ℝ) :
    energy L (x + t • y) = energy L x + 2 * t * pairing L x y + t ^ 2 * energy L y := by
  unfold energy
  rw [pairing_add_left, pairing_add_right, pairing_add_right,
    pairing_smul_left, pairing_smul_left, pairing_smul_right, pairing_smul_right,
    pairing_symm L hL y x]
  ring

theorem energy_const_mul (L : Matrix V V ℝ) (c : ℝ) (x : V → ℝ) :
    energy L (fun v => c * x v) = c ^ 2 * energy L x := by
  change energy L (c • x) = _
  unfold energy
  rw [pairing_smul_left, pairing_smul_right]
  ring

theorem pairing_sq_le_energy_mul (L : Matrix V V ℝ)
    (hL : ∀ v w, L v w = L w v) (hpos : ∀ x : V → ℝ, 0 ≤ energy L x)
    (x y : V → ℝ) : pairing L x y ^ 2 ≤ energy L x * energy L y := by
  have hp : ∀ t : ℝ, 0 ≤ energy L y * (t * t) + (2 * pairing L x y) * t + energy L x := by
    intro t
    have h := hpos (x + t • y)
    rw [energy_line L hL] at h
    nlinarith
  have hd := discrim_le_zero hp
  unfold discrim at hd
  nlinarith

theorem laplacian_symm (d : ℝ) (A : Matrix V V ℝ)
    (hA : ∀ v w, A v w = A w v) (v w : V) :
    laplacian d A v w = laplacian d A w v := by
  simp only [laplacian, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [hA v w]
  simp only [eq_comm]

theorem laplacian_energy_eq (d : ℝ) (A : Matrix V V ℝ) (x : V → ℝ) :
    energy (laplacian d A) x = d * (∑ v, x v ^ 2) - ∑ v, x v * (A *ᵥ x) v := by
  simp only [energy, pairing, laplacian, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Exact decomposition into edge-difference energy and grounded mass. -/
theorem laplacian_energy_identity (d : ℝ) (A : Matrix V V ℝ)
    (hA : ∀ v w, A v w = A w v) (x : V → ℝ) :
    energy (laplacian d A) x =
      (1 / 2 : ℝ) * (∑ v, ∑ w, A v w * (x v - x w) ^ 2) +
        ∑ v, (d - ∑ w, A v w) * x v ^ 2 := by
  have hsym : (∑ v, ∑ w, A v w * x w ^ 2) = ∑ v, ∑ w, A v w * x v ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    rw [hA w v]
  have hfirst : (∑ v, ∑ w, A v w * x v ^ 2) = ∑ v, (∑ w, A v w) * x v ^ 2 := by
    simp only [Finset.sum_mul]
  have hcross : (∑ v, ∑ w, x v * (A v w * x w)) = ∑ v, x v * (A *ᵥ x) v := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  have hsquare : (∑ v, ∑ w, A v w * (x v - x w) ^ 2) =
      2 * (∑ v, (∑ w, A v w) * x v ^ 2) - 2 * (∑ v, x v * (A *ᵥ x) v) := by
    have hterm (v w : V) : A v w * (x v - x w) ^ 2 =
        A v w * x v ^ 2 + A v w * x w ^ 2 - 2 * (x v * (A v w * x w)) := by ring
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsym, hfirst]
    change _ - 2 * (∑ v, x v * (A *ᵥ x) v) = _
    ring
  have hground : (∑ v, (d - ∑ w, A v w) * x v ^ 2) =
      d * (∑ v, x v ^ 2) - ∑ v, (∑ w, A v w) * x v ^ 2 := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsquare, hground, laplacian_energy_eq]
  ring

theorem laplacian_energy_nonneg (d : ℝ) (A : Matrix V V ℝ)
    (hA : ∀ v w, A v w = A w v) (hApos : ∀ v w, 0 ≤ A v w)
    (hrow : ∀ v, (∑ w, A v w) ≤ d) (x : V → ℝ) :
    0 ≤ energy (laplacian d A) x := by
  rw [laplacian_energy_identity d A hA]
  apply add_nonneg
  · apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun v _ => Finset.sum_nonneg (fun w _ =>
      mul_nonneg (hApos v w) (sq_nonneg _)))
  · exact Finset.sum_nonneg (fun v _ => mul_nonneg (sub_nonneg.mpr (hrow v)) (sq_nonneg _))

theorem laplacian_pairing_sq_le (d : ℝ) (A : Matrix V V ℝ)
    (hA : ∀ v w, A v w = A w v) (hApos : ∀ v w, 0 ≤ A v w)
    (hrow : ∀ v, (∑ w, A v w) ≤ d) (x y : V → ℝ) :
    pairing (laplacian d A) x y ^ 2 ≤
      energy (laplacian d A) x * energy (laplacian d A) y :=
  pairing_sq_le_energy_mul _ (laplacian_symm d A hA)
    (laplacian_energy_nonneg d A hA hApos hrow) x y

end TranscendentalTuran.Optimization.MatrixEnergy
