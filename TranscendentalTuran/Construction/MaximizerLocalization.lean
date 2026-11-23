module

public import TranscendentalTuran.Construction.DataBounds
public import TranscendentalTuran.Optimization.Normalization
public import TuranUniversality.Hypergraph.Clique

@[expose] public section

/-!
# Localization at an actual completed-host maximum

Formalization author and responsible maintainer: Xizhi Liu.

The root clique gives the lower value bound. The actual data-direction Euler
identity and actual missing-pair matrix then verify every hypothesis of the
numerical localization theorem. No root-weight regularity is assumed.
-/

namespace TranscendentalTuran.Source.RootData

open TuranUniversality TuranUniversality.Weighted Encoding Network Parameters
open Optimization.GraphCalculus Optimization.RootLocalization
open scoped BigOperators
attribute [local irreducible] Parameters.q Parameters.N
attribute [local instance] Classical.propDecidable
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem q_ge_sixty_four : 64 ≤ q := by rw [q_value]; norm_num
theorem q_ge_sixty_four_real : (64 : ℝ) ≤ q := by exact_mod_cast q_ge_sixty_four

theorem completed_clique_baseline (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (x : Root ⊕ D → ℝ)
    (hmax : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ G.edgePolynomial x) :
    cliqueProbability (q : ℝ) ≤ 6 * G.edgePolynomial x := by
  let F := RGraph.clique Root 3
  let u : Root → ℝ := fun _ => 1 / (q : ℝ)
  have hq : (0 : ℝ) < q := by exact_mod_cast q_pos
  have hu : ProbabilityWeights u := by
    refine ⟨fun _ => (one_div_pos.mpr hq).le, ?_⟩
    simp only [u, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hF : F.IsEmbedding G (Sum.inl : Root → Root ⊕ D) := by
    refine ⟨Sum.inl_injective, ?_⟩
    intro p hp
    exact hG.root_clique p (F.uniform p hp)
  have hpush := F.edgePolynomial_le_pushforward G (Sum.inl : Root → Root ⊕ D) hF.isHom u hu.1
  have hprob := Density.pushforwardWeight_probability (Sum.inl : Root → Root ⊕ D) u hu
  have hb := hpush.trans (hmax _ hprob)
  have he : 6 * F.edgePolynomial u = cliqueProbability (q : ℝ) := by
    simpa only [Optimization.elementary_eq_sum, F, RGraph.edgePolynomial, RGraph.clique, u]
      using Optimization.uniform_root_clique_value q_pos
  linarith

theorem polynomial_zero_of_root_mass_zero (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (z : Root → ℝ) (w : D → ℝ)
    (hz : ∀ r, 0 ≤ z r) (hs : (∑ r, z r) = 0) :
    G.edgePolynomial (Sum.elim z w) = 0 := by
  have hz0 (r : Root) : z r = 0 := by
    have hh := Finset.single_le_sum (s := Finset.univ) (a := r)
      (fun k _ => hz k) (Finset.mem_univ r)
    rw [hs] at hh
    exact le_antisymm hh (hz r)
  unfold RGraph.edgePolynomial
  apply Finset.sum_eq_zero
  intro e he
  obtain ⟨v, hv, hr⟩ := hG.covers_edges e he
  cases v with
  | inl r => exact Finset.prod_eq_zero hv (hz0 r)
  | inr d => exact False.elim (sumRooting_inr_data d hr)

theorem maximizer_root_mass_pos (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (z : Root → ℝ) (w : D → ℝ) (hx : ProbabilityWeights (Sum.elim z w))
    (hmax : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ G.edgePolynomial (Sum.elim z w)) :
    0 < ∑ r, z r := by
  have hz : ∀ r, 0 ≤ z r := fun r => hx.1 (Sum.inl r)
  have hs := Finset.sum_nonneg (fun r (_ : r ∈ Finset.univ) => hz r)
  have hbase := completed_clique_baseline G hG (Sum.elim z w) hmax
  have hp := cliqueProbability_gt_seven_eighths q_ge_sixty_four_real
  by_contra hh
  have hs0 : (∑ r, z r) = 0 := le_antisymm (le_of_not_gt hh) hs
  rw [polynomial_zero_of_root_mass_zero G hG.legal z w hz hs0] at hbase
  linarith

theorem fixed_root_maximality (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (z : Root → ℝ) (w : D → ℝ) (hx : ProbabilityWeights (Sum.elim z w))
    (hmax : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ G.edgePolynomial (Sum.elim z w))
    (z' : Root → ℝ) (hz' : ∀ r, 0 ≤ z' r) (hs : (∑ r, z' r) = ∑ r, z r) :
    Optimization.RootTransfer.completePolynomial (∑ d, w d) (missingMatrix G w) (linkVector G w) z' ≤
      Optimization.RootTransfer.completePolynomial (∑ d, w d) (missingMatrix G w) (linkVector G w) z := by
  rw [← completed_polynomial_eq G hG w z', ← completed_polynomial_eq G hG w z]
  apply hmax
  refine ⟨?_, ?_⟩
  · intro v
    cases v with
    | inl r => exact hz' r
    | inr d => exact hx.1 (Sum.inr d)
  · have hsum := hx.2
    rw [Fintype.sum_sum_type] at hsum ⊢
    simpa only [Sum.elim_inl, Sum.elim_inr, hs] using hsum

/-- Every completed ordinary host has exactly the localized root and data
ratios required by the manuscript's finite objective at its actual maximum. -/
theorem maximizer_localized (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (z : Root → ℝ) (w : D → ℝ) (hx : ProbabilityWeights (Sum.elim z w))
    (hmax : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ G.edgePolynomial (Sum.elim z w)) :
    (0 < ∑ r, z r) ∧
      (∑ d, w d) / (∑ r, z r) ≤ 2 / (q : ℝ) ∧
      ∀ r, 1 / (q : ℝ) - 16 / (q : ℝ) ^ 2 ≤ z r / (∑ i, z i) ∧
        z r / (∑ i, z i) ≤ 1 / (q : ℝ) + 16 / (q : ℝ) ^ 2 := by
  have hz : ∀ r, 0 ≤ z r := fun r => hx.1 (Sum.inl r)
  have hw : ∀ d, 0 ≤ w d := fun d => hx.1 (Sum.inr d)
  have hs := maximizer_root_mass_pos G hG z w hx hmax
  have ht : 0 ≤ ∑ d, w d := Finset.sum_nonneg (fun d _ => hw d)
  have htotal : (∑ r, z r) + (∑ d, w d) = 1 := by
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using hx.2
  have hbase := completed_clique_baseline G hG (Sum.elim z w) hmax
  have hb (r : Root) : z r < 2 / (q : ℝ) :=
    maximizer_coordinate_lt_two_div G hx hmax q_ge_sixty_four_real hbase (Sum.inl r)
  refine ⟨hs, localized_root_box q_ge_sixty_four z hz rfl hs ht htotal hb activeRootBudget_lt
    (data_mass_constraint G hG z w hx hmax hbase (fun r => (hb r).le)) ?_⟩
  intro i j _hmin hmaxroot
  have hj : 0 < z j := by
    obtain ⟨k, _, hk⟩ := (Finset.sum_pos_iff_of_nonneg (fun k (_ : k ∈ Finset.univ) => hz k)).mp hs
    exact hk.trans_le (hmaxroot k)
  exact Optimization.RootTransfer.root_transfer_bound (∑ d, w d)
    (missingMatrix G w) (linkVector G w) z ht hz htotal
    (missingMatrix_symmetric G w) (missingMatrix_nonneg G w hw)
    (missingMatrix_row_bound G hG w hw) (linkVector_bounds G w hw)
    (fixed_root_maximality G hG z w hx hmax) i j hj hmaxroot

end TranscendentalTuran.Source.RootData
