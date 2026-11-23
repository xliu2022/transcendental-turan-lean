module

public import TranscendentalTuran.Construction.SourceBasis
public import TranscendentalTuran.Encoding.RootGraphs
public import TranscendentalTuran.Core.Basic

@[expose] public section

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Parameters

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

/-- The root clique gives the strict separation required by the guard
argument, with the manuscript's exact finite root count. -/
theorem root_clique_classLambda_gap :
    1 - 3 / (q : ℝ) < 6 * classLambda finiteClass := by
  let K := RGraph.clique Root 3
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr q_pos
  have hx : ProbabilityWeights (fun _ : Root => (q : ℝ)⁻¹) := by
    refine ⟨fun _ => inv_nonneg.mpr hq.le, ?_⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt hq)
  have hbound := edgePolynomial_le_classLambda finiteClass K
    (rootGraph_admissible K) _ hx
  have hpoly : K.edgePolynomial (fun _ : Root => (q : ℝ)⁻¹) =
      (q.choose 3 : ℝ) * ((q : ℝ)⁻¹) ^ 3 := by
    rw [K.edgePolynomial_uniform]
    simp only [K, RGraph.clique, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hstrict : 1 - 3 / (q : ℝ) < 6 * K.edgePolynomial (fun _ : Root => (q : ℝ)⁻¹) := by
    rw [hpoly, q_value, Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  linarith

end TranscendentalTuran.Source
