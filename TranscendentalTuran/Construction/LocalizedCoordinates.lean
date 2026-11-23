module

public import TranscendentalTuran.Construction.MaximizerLocalization
public import TranscendentalTuran.Optimization.SourceCoefficients

@[expose] public section

/-!
# Normalized actual maximizers and the declaration gain

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Source.RootData

open TuranUniversality Encoding Network Parameters
open scoped BigOperators
attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable def normalizedRoots (z : Root → ℝ) : Root → ℝ :=
  fun r => z r / (∑ i, z i)
noncomputable def normalizedData (z : Root → ℝ) (w : D → ℝ) : D → ℝ :=
  fun d => w d / (∑ i, z i)

theorem sum_normalizedRoots (z : Root → ℝ) (hs : (∑ i, z i) ≠ 0) :
    (∑ r, normalizedRoots z r) = 1 := by
  unfold normalizedRoots
  rw [← Finset.sum_div, div_self hs]

theorem sum_normalizedData (z : Root → ℝ) (w : D → ℝ) :
    (∑ d, normalizedData z w d) = (∑ d, w d) / (∑ r, z r) := by
  unfold normalizedData
  rw [← Finset.sum_div]

theorem normalizedData_nonneg (z : Root → ℝ) (w : D → ℝ)
    (hs : 0 ≤ ∑ r, z r) (hw : ∀ d, 0 ≤ w d) (d : D) : 0 ≤ normalizedData z w d :=
  div_nonneg (hw d) hs

theorem normalizedRoots_nonneg (z : Root → ℝ) (hz : ∀ r, 0 ≤ z r) (r : Root) :
    0 ≤ normalizedRoots z r := div_nonneg (hz r) (Finset.sum_nonneg fun r _ => hz r)

theorem maximizer_normalized_domain (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (z : Root → ℝ) (w : D → ℝ) (hx : ProbabilityWeights (Sum.elim z w))
    (hmax : ∀ v, ProbabilityWeights v → G.edgePolynomial v ≤ G.edgePolynomial (Sum.elim z w))
    (y : PhysicalType → ℝ) (hy : ∀ ν, 0 ≤ y ν)
    (hmass : (∑ ν, y ν) ≤ ∑ d, normalizedData z w d) :
    Optimization.Paper.sourceCoordinates (normalizedRoots z) y ∈ Optimization.rootTypeDomain q := by
  obtain ⟨hs, hratio, hbox⟩ := maximizer_localized G hG z w hx hmax
  apply Optimization.Paper.sourceCoordinates_mem hbox
    (sum_normalizedRoots z (ne_of_gt hs)) hy
  apply hmass.trans
  rwa [sum_normalizedData]

theorem specialWeight_source_layers (z : Root → ℝ) (y : PhysicalType → ℝ) :
    Optimization.Paper.specialWeight (Optimization.Paper.sourceCoordinates z y) =
      ∑ r : Layer, z (layerRoot r) := by
  unfold Optimization.Paper.specialWeight
  simp only [Optimization.Paper.matchingWeight_source_eval,
    Optimization.Paper.ownershipWeight_source_eval]
  have h := Optimization.Paper.layer_sum_eq_blocks z (fun _ => 1)
  simp only [mul_one] at h
  exact h.symm

theorem maximizer_declaration_gain (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (z : Root → ℝ) (w : D → ℝ) (hx : ProbabilityWeights (Sum.elim z w))
    (hmax : ∀ v, ProbabilityWeights v → G.edgePolynomial v ≤ G.edgePolynomial (Sum.elim z w))
    (ν : Fin 7) :
    (((∑ j : Fin N, normalizedRoots z (genericRoot j)) / 7 +
      ∑ r : Layer, normalizedRoots z (layerRoot r)) *
        (∑ d, normalizedData z w d)) ≤ declaringWeight (normalizedRoots z) ν := by
  have hloc := maximizer_localized G hG z w hx hmax
  have hw : ∀ d, 0 ≤ normalizedData z w d :=
    normalizedData_nonneg z w hloc.1.le (fun d => hx.1 (Sum.inr d))
  have ht : 0 ≤ ∑ d, normalizedData z w d := Finset.sum_nonneg fun d _ => hw d
  have hdom := maximizer_normalized_domain G hG z w hx hmax (fun _ => 0)
    (fun _ => le_rfl) (by simpa only [Finset.sum_const_zero] using ht)
  have htq : (∑ d, normalizedData z w d) ≤ 2 / (q : ℝ) := by
    rw [sum_normalizedData]
    exact hloc.2.1
  have hh := Optimization.Paper.declaring_gain_nonneg hdom ν ht htq
  rw [Optimization.Paper.declaringWeight_source_eval,
    Optimization.Paper.genericWeight_source_eval, specialWeight_source_layers] at hh
  linarith

theorem probability_root_normalization (G : RGraph (Root ⊕ D) 3)
    (z : Root → ℝ) (w : D → ℝ) (hx : ProbabilityWeights (Sum.elim z w))
    (hs : 0 < ∑ r, z r) :
    G.edgePolynomial (Sum.elim (normalizedRoots z) (normalizedData z w)) /
      (1 + ∑ d, normalizedData z w d) ^ 3 = G.edgePolynomial (Sum.elim z w) := by
  have htotal : (∑ r, z r) + (∑ d, w d) = 1 := by
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using hx.2
  have hden : 1 + (∑ d, normalizedData z w d) = 1 / (∑ r, z r) := by
    rw [sum_normalizedData]
    apply (eq_div_iff (ne_of_gt hs)).mpr
    field_simp
    exact htotal
  have hweights : (fun v : Root ⊕ D => (Sum.elim z w) v / (∑ r, z r)) =
      Sum.elim (normalizedRoots z) (normalizedData z w) := by
    funext v
    cases v <;> rfl
  have hscale := Optimization.GraphCalculus.edgePolynomial_root_normalization G (Sum.elim z w)
    (ne_of_gt hs)
  rw [hweights] at hscale
  calc
    _ = (∑ r, z r) ^ 3 * G.edgePolynomial
        (Sum.elim (normalizedRoots z) (normalizedData z w)) := by
      rw [hden]
      field_simp
    _ = _ := hscale.symm

end TranscendentalTuran.Source.RootData
