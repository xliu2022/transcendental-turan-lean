module

public import TranscendentalTuran.Optimization.SourceCoefficients
public import TranscendentalTuran.Construction.TypedPolynomial

@[expose] public section

/-!
# The ordinary source upper expression is the finite rational objective

Formalization author and responsible maintainer: Xizhi Liu.

These identities connect actual physical-type masses and actual root-link
coefficients to the finite rational functions A and B. The final comparison
uses the genuine compact-domain supremum Ψ.
-/

namespace TranscendentalTuran.Optimization.Paper

open Finset MvPolynomial Parameters Encoding Network
open TuranUniversality.Algebraicity
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

theorem quadraticWeight_eq_typedQuadratic (z : Root → ℝ) (y : PhysicalType → ℝ) :
    qeval quadraticWeight (sourceCoordinates z y) = Source.RootData.typedQuadratic z y := by
  rw [quadraticWeight_source_eval]
  rfl

theorem numeratorA_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) :
    qeval numeratorA (sourceCoordinates z y) =
      TuranUniversality.Weighted.elementary Finset.univ z 3 +
      (∑ ν : PhysicalType, y ν * pairWeight (allowedPairs ν) z) +
      Source.RootData.typedQuadratic z y := by
  simp only [numeratorA, qeval_add, rootElementary_source_eval, linearSum_source_eval,
    quadraticWeight_eq_typedQuadratic]

theorem A_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) :
    A.eval (sourceCoordinates z y) =
      (TuranUniversality.Weighted.elementary Finset.univ z 3 +
        (∑ ν : PhysicalType, y ν * pairWeight (allowedPairs ν) z) +
        Source.RootData.typedQuadratic z y) / (1 + ∑ ν, y ν) ^ 3 := by
  change qeval numeratorA (sourceCoordinates z y) / qeval normalization (sourceCoordinates z y) = _
  rw [numeratorA_source_eval, normalization_source_eval]

theorem B_source_eval {z : Root → ℝ} {y : PhysicalType → ℝ}
    (hz : sourceCoordinates z y ∈ rootTypeDomain q) :
    B.eval (sourceCoordinates z y) = Encoding.markerWeight z ^ 2 *
      (∑ b : Fin 4, (∑ j : Fin M, z (Encoding.matchingRoot b j))⁻¹) /
        (2 * (1 + ∑ ν, y ν) ^ 3) := by
  rw [B_eval_eq_source_coefficient hz, markerWeight_source_eval, resistance_source_eval]
  simp only [sourceCoordinates, Sum.elim_inr, sum_physical_index]

theorem affine_source_eval (g : ℝ) {z : Root → ℝ} {y : PhysicalType → ℝ}
    (hz : sourceCoordinates z y ∈ rootTypeDomain q) :
    A.eval (sourceCoordinates z y) + g * B.eval (sourceCoordinates z y) =
      (TuranUniversality.Weighted.elementary Finset.univ z 3 +
        (∑ ν : PhysicalType, y ν * pairWeight (allowedPairs ν) z) +
        Source.RootData.typedQuadratic z y +
        Encoding.markerWeight z ^ 2 * g *
          (∑ b : Fin 4, (∑ j : Fin M, z (Encoding.matchingRoot b j))⁻¹) / 2) /
          (1 + ∑ ν, y ν) ^ 3 := by
  have hd : (1 + ∑ ν, y ν) ^ 3 ≠ 0 := by
    rw [← normalization_source_eval z y]
    exact ne_of_gt (normalization_pos hz)
  rw [A_source_eval, B_source_eval hz]
  field_simp [hd]
  <;> ring

/-- The actual normalized source polynomial is bounded by Ψ as soon as the
combinatorial energy estimate gives its explicit unnormalized upper bound. -/
theorem source_expression_le_Ψ (g : ℝ) {z : Root → ℝ} {y : PhysicalType → ℝ} {F : ℝ}
    (hz : sourceCoordinates z y ∈ rootTypeDomain q)
    (hF : F ≤ TuranUniversality.Weighted.elementary Finset.univ z 3 +
      (∑ ν : PhysicalType, y ν * pairWeight (allowedPairs ν) z) +
      Source.RootData.typedQuadratic z y + Encoding.markerWeight z ^ 2 * g *
        (∑ b : Fin 4, (∑ j : Fin M, z (Encoding.matchingRoot b j))⁻¹) / 2) :
    F / (1 + ∑ ν, y ν) ^ 3 ≤ Ψ g := by
  have hd : 0 < (1 + ∑ ν, y ν) ^ 3 := by
    rw [← normalization_source_eval z y]
    exact normalization_pos hz
  have hsup := affine_source_le_Ψ g hz
  rw [affine_source_eval g hz] at hsup
  exact (div_le_div_of_nonneg_right hF hd.le).trans hsup

end TranscendentalTuran.Optimization.Paper
