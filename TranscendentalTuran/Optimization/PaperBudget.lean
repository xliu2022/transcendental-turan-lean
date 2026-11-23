module

public import TranscendentalTuran.Optimization.PaperQuadratic

@[expose] public section

/-!
# Every maximizer of the actual objective has all seven budgets

Formalization author and responsible maintainer: Xizhi Liu.

The coefficient estimates and first-order argument are instantiated here
for the paper's precise rational objective. The Green input is allowed
to be any real number at most one half; the manuscript's value has this
bound independently in `Green.Constants`.
-/

namespace TranscendentalTuran.Optimization.Paper

open Set Finset MvPolynomial Parameters Encoding
open TuranUniversality.Algebraicity
open QuadraticBudget

def withTypes (z : Coord → ℝ) (y : Fin 7 → ℝ) : Coord → ℝ :=
  Sum.elim (fun r => z (Sum.inl r)) y

@[simp] theorem withTypes_root (z : Coord → ℝ) (y : Fin 7 → ℝ) (r : Root) :
    withTypes z y (Sum.inl r) = z (Sum.inl r) := rfl

@[simp] theorem withTypes_type (z : Coord → ℝ) (y : Fin 7 → ℝ) (i : Fin 7) :
    withTypes z y (Sum.inr i) = y i := rfl

theorem withTypes_original (z : Coord → ℝ) :
    withTypes z (fun i => z (Sum.inr i)) = z := by
  funext c
  cases c <;> rfl

theorem withTypes_mem {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    {y : Fin 7 → ℝ} (hy : y ∈ feasible (q : ℝ)) : withTypes z y ∈ rootTypeDomain q :=
  ⟨hz.1, hz.2.1, hy.1, hy.2⟩

@[simp] theorem rootElementary_withTypes (z : Coord → ℝ) (y : Fin 7 → ℝ) (k : ℕ) :
    qeval (rootElementary k) (withTypes z y) = qeval (rootElementary k) z := by
  simp only [rootElementary, qeval_sum, qeval_prod, rootVar, qeval_X, withTypes_root]

@[simp] theorem markerWeight_withTypes (z : Coord → ℝ) (y : Fin 7 → ℝ) :
    qeval markerWeight (withTypes z y) = qeval markerWeight z := by
  simp only [markerWeight, qeval_mul, rootVar, qeval_X, withTypes_root]

@[simp] theorem declaringWeight_withTypes (z : Coord → ℝ) (y : Fin 7 → ℝ) (i : Fin 7) :
    qeval (declaringWeight i) (withTypes z y) = qeval (declaringWeight i) z := by
  simp only [declaringWeight, qeval_sum, qeval_mul, rootVar, qeval_X, withTypes_root]

@[simp] theorem linearWeight_withTypes (z : Coord → ℝ) (y : Fin 7 → ℝ) (i : Fin 7) :
    qeval (linearWeight i) (withTypes z y) = qeval (linearWeight i) z := by
  simp only [linearWeight, qeval_sub, qeval_sum, rootElementary_withTypes,
    markerWeight_withTypes, declaringWeight_withTypes]

@[simp] theorem genericWeight_withTypes (z : Coord → ℝ) (y : Fin 7 → ℝ) :
    qeval genericWeight (withTypes z y) = qeval genericWeight z := by
  simp only [genericWeight, qeval_sum, rootVar, qeval_X, withTypes_root]

@[simp] theorem matchingWeight_withTypes (z : Coord → ℝ) (y : Fin 7 → ℝ) (b : Fin 4) :
    qeval (matchingWeight b) (withTypes z y) = qeval (matchingWeight b) z := by
  simp only [matchingWeight, qeval_sum, rootVar, qeval_X, withTypes_root]

@[simp] theorem ownershipWeight_withTypes (z : Coord → ℝ) (y : Fin 7 → ℝ) (b : Fin 2) :
    qeval (ownershipWeight b) (withTypes z y) = qeval (ownershipWeight b) z := by
  simp only [ownershipWeight, qeval_sum, rootVar, qeval_X, withTypes_root]

@[simp] theorem resistance_withTypes (z : Coord → ℝ) (y : Fin 7 → ℝ) :
    resistance (withTypes z y) = resistance z := by
  simp only [resistance, matchingWeight_withTypes]

@[simp] theorem specialMatrix_withTypes (z : Coord → ℝ) (y : Fin 7 → ℝ) :
    specialMatrix (withTypes z y) = specialMatrix z := by
  simp only [specialMatrix, matchingWeight_withTypes, ownershipWeight_withTypes]

@[simp] theorem layerForm_withTypes (z : Coord → ℝ) (y : Fin 7 → ℝ) :
    layerForm (withTypes z y) = layerForm z := by
  simp only [layerForm, genericWeight_withTypes, specialMatrix_withTypes]

theorem A_eval_eq (z : Coord → ℝ) :
    A.eval z = (qeval (rootElementary 3) z +
      (∑ i : Fin 7, qeval (linearWeight i) z * z (Sum.inr i)) + qeval quadraticWeight z) /
        (1 + ∑ i : Fin 7, z (Sum.inr i)) ^ 3 := by
  simp only [QRationalFunction.eval, A, numeratorA, normalization, dataMass,
    qeval_add, qeval_mul, qeval_pow, qeval_sum, qeval_one, typeVar, qeval_X]

theorem affine_eval_withTypes (g : ℝ) {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    {y : Fin 7 → ℝ} (hy : y ∈ feasible (q : ℝ)) :
    A.eval (withTypes z y) + g * B.eval (withTypes z y) =
      objective (qeval (rootElementary 3) z + sourceConstant g z)
        (fun i => qeval (linearWeight i) z) (layerForm z) y := by
  rw [A_eval_eq, B_eval_eq_source_coefficient (withTypes_mem hz hy), quadraticWeight_eval]
  simp only [rootElementary_withTypes, linearWeight_withTypes, withTypes_type,
    markerWeight_withTypes, resistance_withTypes, layerForm_withTypes]
  have hx : 0 ≤ ∑ i : Fin 7, y i := mass_nonneg hy.1
  have hd : (1 + ∑ i : Fin 7, y i) ≠ 0 := by linarith
  unfold objective linear mass sourceConstant
  field_simp [hd] <;> ring

/-- The manuscript's type-budget lemma for an actual global maximizer of
the exact rational objective, with every coefficient estimate discharged. -/
theorem maximizer_type_budget {g : ℝ} (hg : g ≤ 1 / 2)
    {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (hmax : ∀ w ∈ rootTypeDomain q,
      A.eval w + g * B.eval w ≤ A.eval z + g * B.eval z) :
    ∀ i : Fin 7, 1 / (32 * (q : ℝ)) < z (Sum.inr i) := by
  let y : Fin 7 → ℝ := fun i => z (Sum.inr i)
  have hy : y ∈ feasible (q : ℝ) := ⟨hz.2.2.1, hz.2.2.2⟩
  have hslice : ∀ v ∈ feasible (q : ℝ),
      objective (qeval (rootElementary 3) z + sourceConstant g z)
          (fun i => qeval (linearWeight i) z) (layerForm z) v ≤
        objective (qeval (rootElementary 3) z + sourceConstant g z)
          (fun i => qeval (linearWeight i) z) (layerForm z) y := by
    intro v hv
    have hh := hmax (withTypes z v) (withTypes_mem hz hv)
    rw [affine_eval_withTypes g hz hv] at hh
    have he := affine_eval_withTypes g hz hy
    rw [show withTypes z y = z from withTypes_original z] at he
    rwa [he] at hh
  have hω : 0 ≤ qeval genericWeight z := by linarith [(genericWeight_bounds hz).1]
  exact seven_type_budget (q : ℝ)
    (qeval (rootElementary 3) z + sourceConstant g z)
    (qeval genericWeight z) (specialWeight z)
    (fun i => qeval (linearWeight i) z) (layerForm z) (layerForm_symmetric z)
    (by exact_mod_cast (le_trans (by decide : 7 ≤ 64) q_ge_64)) hω (specialWeight_bounds hz).1
    (linearWeight_bounds hz) (linearWeight_difference_bound hz)
    (linearWeight_gap hg hz) (type_separation_bound hz) hy
    (layerForm_gradient_bounds hz y hy.1) (layerForm_quadratic_bounds hz y hy.1).2 hslice

theorem Ψ_maximizer_exists (g : ℝ) :
    ∃ z ∈ rootTypeDomain q, A.eval z + g * B.eval z = Ψ g :=
  (isGreatest_rationalAffineMaximum (rootTypeDomain_isCompact q_ge_64)
    (rootTypeDomain_nonempty q_pos) A B A_regular B_regular g).1

theorem Ψ_maximizer_type_budget {g : ℝ} (hg : g ≤ 1 / 2)
    {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (heq : A.eval z + g * B.eval z = Ψ g) :
    ∀ i : Fin 7, 1 / (32 * (q : ℝ)) < z (Sum.inr i) := by
  apply maximizer_type_budget hg hz
  intro w hw
  rw [heq]
  exact (isGreatest_rationalAffineMaximum (rootTypeDomain_isCompact q_ge_64)
    (rootTypeDomain_nonempty q_pos) A B A_regular B_regular g).2
      (Set.mem_image_of_mem _ hw)

end TranscendentalTuran.Optimization.Paper
