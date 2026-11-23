module

public import TranscendentalTuran.Optimization.PaperRootBounds
public import TranscendentalTuran.Optimization.QuadraticLayers
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# The actual layer Hessian and its bounds

Formalization author and responsible maintainer: Xizhi Liu.

The six layer partitions below are precisely the positive/negative sets
used by the manuscript's four matching and two ownership layers.
-/

namespace TranscendentalTuran.Optimization.Paper

open Finset MvPolynomial Parameters Encoding
open TuranUniversality.Algebraicity
open QuadraticBudget

def matchingPositiveTypes : Fin 4 → Finset (Fin 7) :=
  ![{0, 4}, {0, 3}, {0, 4}, {0, 3}]
def matchingNegativeTypes : Fin 4 → Finset (Fin 7) := ![{1}, {1}, {2}, {2}]
def ownershipPositiveTypes : Fin 2 → Finset (Fin 7) := ![{5}, {6}]

theorem matchingTypes_disjoint (b : Fin 4) :
    Disjoint (matchingPositiveTypes b) (matchingNegativeTypes b) := by
  fin_cases b <;> decide

theorem ownershipTypes_disjoint (b : Fin 2) :
    Disjoint (ownershipPositiveTypes b) {0} := by
  fin_cases b <;> decide

theorem matchingPositive_eval (z : Coord → ℝ) (b : Fin 4) :
    qeval (matchingPositive b) z = ∑ i ∈ matchingPositiveTypes b, z (Sum.inr i) := by
  fin_cases b <;> simp [matchingPositive, matchingPositiveTypes, typeVar,
    qeval_add, qeval_X]

theorem matchingNegative_eval (z : Coord → ℝ) (b : Fin 4) :
    qeval (matchingNegative b) z = ∑ i ∈ matchingNegativeTypes b, z (Sum.inr i) := by
  fin_cases b <;> simp [matchingNegative, matchingNegativeTypes, typeVar, qeval_X]

theorem ownershipPositive_eval (z : Coord → ℝ) (b : Fin 2) :
    qeval (ownershipPositive b) z = ∑ i ∈ ownershipPositiveTypes b, z (Sum.inr i) := by
  fin_cases b <;> simp [ownershipPositive, ownershipPositiveTypes, typeVar, qeval_X]

theorem typeElementary_eval (z : Coord → ℝ) (k : ℕ) :
    qeval (typeElementary k) z = elementary (fun i : Fin 7 => z (Sum.inr i)) k := by
  rw [elementary_eq_sum]
  simp only [typeElementary, qeval_sum, qeval_prod, typeVar, qeval_X]

noncomputable def specialMatrix (z : Coord → ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  (∑ b : Fin 4, qeval (matchingWeight b) z •
    layerMatrix (matchingPositiveTypes b) (matchingNegativeTypes b)) +
  ∑ b : Fin 2, qeval (ownershipWeight b) z • layerMatrix (ownershipPositiveTypes b) {0}

theorem specialMatrix_symmetric (z : Coord → ℝ) (i j : Fin 7) :
    specialMatrix z i j = specialMatrix z j i := by
  simp only [specialMatrix, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro b _ <;>
    rw [layerMatrix_symmetric _ _ i j]

theorem specialMatrix_bounds {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (i j : Fin 7) :
    0 ≤ specialMatrix z i j ∧ specialMatrix z i j ≤ specialWeight z := by
  simp only [specialMatrix, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hm (b : Fin 4) := layerMatrix_bounds (matchingPositiveTypes b)
    (matchingNegativeTypes b) (matchingTypes_disjoint b) i j
  have ho (b : Fin 2) := layerMatrix_bounds (ownershipPositiveTypes b)
    {0} (ownershipTypes_disjoint b) i j
  constructor
  · exact add_nonneg
      (Finset.sum_nonneg (fun b _ => mul_nonneg (matchingWeight_pos hz b).le (hm b).1))
      (Finset.sum_nonneg (fun b _ => mul_nonneg (ownershipWeight_pos hz b).le (ho b).1))
  · apply add_le_add
    · apply Finset.sum_le_sum
      intro b _
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hm b).2 (matchingWeight_pos hz b).le
    · apply Finset.sum_le_sum
      intro b _
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (ho b).2 (ownershipWeight_pos hz b).le

theorem specialMatrix_eval (z : Coord → ℝ) (y : Fin 7 → ℝ) :
    (specialMatrix z).toBilin' y y =
      (∑ b : Fin 4, qeval (matchingWeight b) z *
        ((∑ i ∈ matchingPositiveTypes b, y i) ^ 2 +
          (∑ i ∈ matchingNegativeTypes b, y i) ^ 2)) +
      ∑ b : Fin 2, qeval (ownershipWeight b) z *
        ((∑ i ∈ ownershipPositiveTypes b, y i) ^ 2 + (y 0) ^ 2) := by
  simp only [specialMatrix, map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, layerMatrix_eval,
    Finset.sum_singleton]

noncomputable def layerForm (z : Coord → ℝ) : LinearMap.BilinForm ℝ (Fin 7 → ℝ) :=
  interactionForm (qeval genericWeight z) (specialMatrix z)

theorem layerForm_symmetric (z : Coord → ℝ) :
    ∀ y d, layerForm z y d = layerForm z d y :=
  interactionForm_symmetric _ _ (specialMatrix_symmetric z)

theorem quadraticWeight_eval (z : Coord → ℝ) :
    qeval quadraticWeight z = quad (layerForm z) (fun i => z (Sum.inr i)) := by
  rw [layerForm, interactionForm_eval, specialMatrix_eval]
  simp only [quadraticWeight, qeval_add, qeval_mul, qeval_sum, qeval_pow,
    qeval_C, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, typeElementary_eval,
    matchingPositive_eval, matchingNegative_eval, ownershipPositive_eval, typeVar, qeval_X]
  ring

theorem layerForm_gradient_bounds {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (y : Fin 7 → ℝ) (hy : ∀ i, 0 ≤ y i) (j : Fin 7) :
    qeval genericWeight z * (mass y - y j) ≤ layerForm z y (coordinateVector j) ∧
      layerForm z y (coordinateVector j) ≤
        qeval genericWeight z * (mass y - y j) + specialWeight z * mass y :=
  interactionForm_gradient_bounds _ _ _ (specialMatrix_bounds hz) y hy j

theorem layerForm_quadratic_bounds {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (y : Fin 7 → ℝ) (hy : ∀ i, 0 ≤ y i) :
    0 ≤ quad (layerForm z) y ∧ quad (layerForm z) y ≤ (mass y) ^ 2 / 2 := by
  have hw : 0 ≤ qeval genericWeight z := by linarith [(genericWeight_bounds hz).1]
  have h := interactionForm_quadratic_bounds _ _ hw _ (specialMatrix_bounds hz) y hy
  refine ⟨h.1, h.2.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_right (generic_add_special_le_one hz)
    (sq_nonneg (mass y))
  linarith

end TranscendentalTuran.Optimization.Paper
