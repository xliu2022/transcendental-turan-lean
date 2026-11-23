module

public import TranscendentalTuran.Optimization.SevenTypeBudget

@[expose] public section

/-!
# Nonnegative layer matrices

Formalization author and responsible maintainer: Xizhi Liu.

A generic complete multipartite layer contributes `ω` off the diagonal.
The remaining nonnegative layer matrix has every coefficient at most the
total special-root weight `Z`.
-/

namespace TranscendentalTuran.Optimization.QuadraticBudget

open Finset

noncomputable def interactionMatrix (ω : ℝ) (Q : Matrix (Fin 7) (Fin 7) ℝ) :
    Matrix (Fin 7) (Fin 7) ℝ := fun i j => (if i = j then 0 else ω) + Q i j

noncomputable def interactionForm (ω : ℝ) (Q : Matrix (Fin 7) (Fin 7) ℝ) :
    LinearMap.BilinForm ℝ (Fin 7 → ℝ) := (interactionMatrix ω Q).toBilin'

theorem interactionForm_symmetric (ω : ℝ) (Q : Matrix (Fin 7) (Fin 7) ℝ)
    (hQ : ∀ i j, Q i j = Q j i) :
    ∀ y d, interactionForm ω Q y d = interactionForm ω Q d y := by
  apply LinearMap.BilinForm.IsSymm.eq
  apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
  ext i j
  simp only [Matrix.transpose_apply, interactionMatrix]
  rw [hQ j i]
  simp only [eq_comm]

theorem interactionForm_coordinate (ω : ℝ) (Q : Matrix (Fin 7) (Fin 7) ℝ)
    (y : Fin 7 → ℝ) (j : Fin 7) :
    interactionForm ω Q y (coordinateVector j) =
      ω * (mass y - y j) + ∑ i, y i * Q i j := by
  simp only [interactionForm, Matrix.toBilin'_apply, coordinateVector,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [interactionMatrix, mul_add, Finset.sum_add_distrib]
  congr 1
  have he : ∀ i : Fin 7, y i * (if i = j then 0 else ω) =
      ω * y i - (if i = j then ω * y j else 0) := by
    intro i
    split_ifs with hij
    · subst i; ring
    · ring
  simp only [he, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ← Finset.mul_sum, mass]
  ring

theorem interactionForm_gradient_bounds (ω Z : ℝ)
    (Q : Matrix (Fin 7) (Fin 7) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j ∧ Q i j ≤ Z)
    (y : Fin 7 → ℝ) (hy : ∀ i, 0 ≤ y i) (j : Fin 7) :
    ω * (mass y - y j) ≤ interactionForm ω Q y (coordinateVector j) ∧
      interactionForm ω Q y (coordinateVector j) ≤
        ω * (mass y - y j) + Z * mass y := by
  rw [interactionForm_coordinate]
  have hlo : 0 ≤ ∑ i : Fin 7, y i * Q i j :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hy i) (hQ i j).1)
  have hhi : (∑ i : Fin 7, y i * Q i j) ≤ Z * mass y := by
    calc
      _ ≤ ∑ i : Fin 7, y i * Z :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hQ i j).2 (hy i))
      _ = Z * mass y := by rw [← Finset.sum_mul]; unfold mass; ring
  constructor <;> linarith

theorem interactionForm_quadratic_bounds (ω Z : ℝ)
    (hω : 0 ≤ ω) (Q : Matrix (Fin 7) (Fin 7) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j ∧ Q i j ≤ Z)
    (y : Fin 7 → ℝ) (hy : ∀ i, 0 ≤ y i) :
    0 ≤ quad (interactionForm ω Q) y ∧
      quad (interactionForm ω Q) y ≤ (ω + Z) * (mass y) ^ 2 / 2 := by
  have hH : ∀ i j, 0 ≤ interactionMatrix ω Q i j ∧
      interactionMatrix ω Q i j ≤ ω + Z := by
    intro i j
    simp only [interactionMatrix]
    split_ifs <;> constructor <;> linarith [(hQ i j).1, (hQ i j).2]
  have hlo : 0 ≤ interactionForm ω Q y y := by
    simp only [interactionForm, Matrix.toBilin'_apply]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (hy i) (hH i j).1) (hy j)))
  have hhi : interactionForm ω Q y y ≤ (ω + Z) * (mass y) ^ 2 := by
    calc
      interactionForm ω Q y y ≤
          ∑ i : Fin 7, ∑ j : Fin 7, y i * (ω + Z) * y j := by
        simp only [interactionForm, Matrix.toBilin'_apply]
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hH i j).2 (hy i)) (hy j)
      _ = (ω + Z) * (mass y) ^ 2 := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul, mass]
        ring
  constructor <;> unfold quad <;> linarith

end TranscendentalTuran.Optimization.QuadraticBudget
