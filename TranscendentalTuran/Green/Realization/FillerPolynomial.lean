module

public import TranscendentalTuran.Green.Realization.FillerWeights
public import TranscendentalTuran.Green.Realization.TemplatePolynomial
public import TranscendentalTuran.Green.Realization.TemplateLegal

@[expose] public section

/-!
# Exact target-budget polynomial after adding fillers

Formalization author and responsible maintainer: Xizhi Liu.

For a fixed finite legal template, all seven target masses are attained
exactly. The only error in the ordinary edge polynomial is the explicit
filler energy coefficient divided by twice the filler count.
-/

namespace TranscendentalTuran.Green.Realization.TypedData

open Network Encoding Parameters TuranUniversality TuranUniversality.Weighted Source
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D] (H : TypedData D)

noncomputable def residualMass (w : D → ℝ) (y : PhysicalType → ℝ) : PhysicalType → ℝ :=
  fun ν => y ν - RootData.typeMass H.type w ν

theorem uniformFiller_rootedLegal (hL : H.Legal) (n : ℕ) :
    RootedLegal (H.withUniformFillers n).graph (sumRooting (D ⊕ UniformFiller n)) :=
  (H.withUniformFillers n).graph_rootedLegal (H.withFillers_legal Prod.fst hL)

theorem residualMass_nonneg {w : D → ℝ} {y : PhysicalType → ℝ}
    (hy : ∀ ν, RootData.typeMass H.type w ν ≤ y ν) : ∀ ν, 0 ≤ H.residualMass w y ν :=
  fun ν => sub_nonneg.mpr (hy ν)

theorem targetFillerWeight_nonneg (n : ℕ) {w : D → ℝ} {y : PhysicalType → ℝ}
    (hw : ∀ d, 0 ≤ w d) (hy : ∀ ν, RootData.typeMass H.type w ν ≤ y ν)
    (d : D ⊕ UniformFiller n) :
    0 ≤ H.uniformFillerWeight n w (H.residualMass w y) d :=
  H.uniformFillerWeight_nonneg n hw (H.residualMass_nonneg hy) d

theorem targetFiller_typeMass {n : ℕ} (hn : 0 < n) (w : D → ℝ) (y : PhysicalType → ℝ) :
    RootData.typeMass (H.withUniformFillers n).type
      (H.uniformFillerWeight n w (H.residualMass w y)) = y := by
  funext ν
  exact H.uniformFiller_typeMass_target hn w y ν

theorem targetFiller_mass {n : ℕ} (hn : 0 < n) (w : D → ℝ) (y : PhysicalType → ℝ) :
    (∑ d, H.uniformFillerWeight n w (H.residualMass w y) d) = ∑ ν, y ν := by
  rw [← RootData.sum_typeMass (H.withUniformFillers n).type
    (H.uniformFillerWeight n w (H.residualMass w y)), H.targetFiller_typeMass hn]

theorem uniformFiller_graph_polynomial (hL : H.Legal) {n : ℕ} (hn : 0 < n)
    (z : Root → ℝ) (w : D → ℝ) (y : PhysicalType → ℝ) :
    (H.withUniformFillers n).graph.edgePolynomial
      (Sum.elim z (H.uniformFillerWeight n w (H.residualMass w y))) =
      elementary Finset.univ z 3 +
        (∑ ν : PhysicalType, y ν * pairWeight (allowedPairs ν) z) +
        RootData.typedQuadratic z y + markerWeight z * w H.mark -
        (∑ r : Layer, z (layerRoot r) * H.layerEnergy r.1 w) / 2 -
        fillerEnergyCost z (H.residualMass w y) / (2 * (n : ℝ)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [(H.withUniformFillers n).graph_edgePolynomial_eq_layerEnergy
    (H.uniformFiller_rootedLegal hL n), H.targetFiller_typeMass hn]
  have hm : H.uniformFillerWeight n w (H.residualMass w y) (H.withUniformFillers n).mark =
      w H.mark := rfl
  rw [hm, H.uniformFiller_energy_sum hn]
  field_simp [hn']
  <;> ring

end TranscendentalTuran.Green.Realization.TypedData
