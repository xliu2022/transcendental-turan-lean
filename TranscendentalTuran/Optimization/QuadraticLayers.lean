module

public import TranscendentalTuran.Optimization.QuadraticMatrix
public import TranscendentalTuran.Optimization.ElementaryIdentities

@[expose] public section

/-!
# Quadratic forms for individual layers

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Optimization.QuadraticBudget

open Finset

noncomputable def outerMatrix (s : Finset (Fin 7)) : Matrix (Fin 7) (Fin 7) ℝ :=
  fun i j => if i ∈ s ∧ j ∈ s then 1 else 0

noncomputable def layerMatrix (s t : Finset (Fin 7)) : Matrix (Fin 7) (Fin 7) ℝ :=
  outerMatrix s + outerMatrix t

theorem outerMatrix_symmetric (s : Finset (Fin 7)) (i j : Fin 7) :
    outerMatrix s i j = outerMatrix s j i := by simp only [outerMatrix, and_comm]

theorem layerMatrix_symmetric (s t : Finset (Fin 7)) (i j : Fin 7) :
    layerMatrix s t i j = layerMatrix s t j i := by
  simp only [layerMatrix, Matrix.add_apply, outerMatrix_symmetric s i j,
    outerMatrix_symmetric t i j]

theorem layerMatrix_bounds (s t : Finset (Fin 7)) (hst : Disjoint s t)
    (i j : Fin 7) : 0 ≤ layerMatrix s t i j ∧ layerMatrix s t i j ≤ 1 := by
  simp only [layerMatrix, Matrix.add_apply, outerMatrix]
  split_ifs with hs ht ht
  · exact False.elim (Finset.disjoint_left.mp hst hs.1 ht.1)
  · norm_num
  · norm_num
  · norm_num

private theorem sum_if_mem (s : Finset (Fin 7)) (f : Fin 7 → ℝ) :
    (∑ i : Fin 7, if i ∈ s then f i else 0) = ∑ i ∈ s, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

theorem outerMatrix_eval (s : Finset (Fin 7)) (y d : Fin 7 → ℝ) :
    (outerMatrix s).toBilin' y d = (∑ i ∈ s, y i) * ∑ j ∈ s, d j := by
  rw [Matrix.toBilin'_apply]
  calc
    _ = ∑ i : Fin 7, if i ∈ s then y i * (∑ j ∈ s, d j) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ s
      · simp only [outerMatrix, hi, true_and, mul_ite, mul_one, mul_zero,
          ite_mul, zero_mul, if_true]
        rw [sum_if_mem, ← Finset.mul_sum]
      · simp [outerMatrix, hi]
    _ = _ := by rw [sum_if_mem, Finset.sum_mul]

theorem layerMatrix_eval (s t : Finset (Fin 7)) (y : Fin 7 → ℝ) :
    (layerMatrix s t).toBilin' y y =
      (∑ i ∈ s, y i) ^ 2 + (∑ i ∈ t, y i) ^ 2 := by
  simp only [layerMatrix, map_add, LinearMap.add_apply, outerMatrix_eval, pow_two]

theorem bilinear_sum_coordinates (H : Matrix (Fin 7) (Fin 7) ℝ) (y : Fin 7 → ℝ) :
    H.toBilin' y y = ∑ j, H.toBilin' y (coordinateVector j) * y j := by
  simp only [Matrix.toBilin'_apply, coordinateVector, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem offDiagonal_eval (ω : ℝ) (y : Fin 7 → ℝ) :
    interactionForm ω 0 y y =
      ω * ((mass y) ^ 2 - ∑ i : Fin 7, y i ^ 2) := by
  rw [interactionForm, bilinear_sum_coordinates]
  change (∑ j : Fin 7, interactionForm ω 0 y (coordinateVector j) * y j) = _
  simp only [interactionForm_coordinate, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]
  calc
    _ = ∑ j : Fin 7, (ω * mass y * y j - ω * (y j) ^ 2) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, mass]
      ring

theorem interactionForm_eval (ω : ℝ) (Q : Matrix (Fin 7) (Fin 7) ℝ)
    (y : Fin 7 → ℝ) :
    quad (interactionForm ω Q) y =
      ω * elementary y 2 + Q.toBilin' y y / 2 := by
  have he : interactionMatrix ω Q = interactionMatrix ω 0 + Q := by
    ext i j
    simp [interactionMatrix]
  have h2 := two_mul_elementary_two y
  change 2 * elementary y 2 = (mass y) ^ 2 - ∑ i, y i ^ 2 at h2
  unfold quad interactionForm
  rw [he, map_add, LinearMap.add_apply, LinearMap.add_apply]
  change (interactionForm ω 0 y y + Q.toBilin' y y) / 2 = _
  rw [offDiagonal_eval, ← h2]
  ring

end TranscendentalTuran.Optimization.QuadraticBudget
