module

public import TranscendentalTuran.Construction.DataEuler

@[expose] public section

/-!
# Data-direction bounds before declaring every vertex

Formalization author and responsible maintainer: Xizhi Liu.

Only rooted legality and completion are used here. In particular all data
vertices, including undeclared vertices, are included in the total mass.
-/

namespace TranscendentalTuran.Source.RootData

open TuranUniversality TuranUniversality.Weighted Encoding Network Parameters
open Optimization.GraphCalculus
open scoped BigOperators
attribute [local irreducible] Parameters.q Parameters.N
attribute [local instance] Classical.propDecidable
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D]

def activeRootWeight (z : Root → ℝ) : ℝ :=
  (∑ r : Layer, z (layerRoot r)) + ∑ j : Fin N, z (genericRoot j)

noncomputable def activeRootBudget : ℝ := ((K : ℝ) + N) * (2 / (q : ℝ))

theorem activeRootBudget_lt : activeRootBudget < 1 / 8 := by
  unfold activeRootBudget
  rw [q_value, N_value, K_value]
  norm_num

theorem activeRootWeight_bound (z : Root → ℝ) (hz : ∀ r, z r ≤ 2 / (q : ℝ)) :
    activeRootWeight z ≤ activeRootBudget := by
  have hs : (∑ r : Layer, z (layerRoot r)) ≤ (K : ℝ) * (2 / (q : ℝ)) := by
    calc
      _ ≤ ∑ _r : Layer, (2 / (q : ℝ)) := Finset.sum_le_sum fun r _ => hz (layerRoot r)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, layer_card, nsmul_eq_mul]
  have hg : (∑ j : Fin N, z (genericRoot j)) ≤ (N : ℝ) * (2 / (q : ℝ)) := by
    calc
      _ ≤ ∑ _j : Fin N, (2 / (q : ℝ)) := Finset.sum_le_sum fun j _ => hz (genericRoot j)
      _ = _ := by simp
  unfold activeRootWeight activeRootBudget
  nlinarith only [hs, hg]

theorem twoRootContribution_bound (G : RGraph (Root ⊕ D) 3)
    (z : Root → ℝ) (w : D → ℝ) (hz : ∀ r, 0 ≤ z r) (hw : ∀ d, 0 ≤ w d) :
    twoRootContribution G z w ≤ (∑ d, w d) * elementary Finset.univ z 2 := by
  unfold twoRootContribution
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (hw d)
  have hh := rootLink_missing_sum G d z
  have hn := (missingPairGraph G d).edgePolynomial_nonneg hz
  linarith

theorem oneRootContribution_bound (G : RGraph (Root ⊕ D) 3) (hG : RootedLegal G (sumRooting D))
    (z : Root → ℝ) (w : D → ℝ) (hz : ∀ r, 0 ≤ z r) (hw : ∀ d, 0 ≤ w d) :
    oneRootContribution G z w ≤ activeRootWeight z * (∑ d, w d) ^ 2 / 2 := by
  unfold oneRootContribution
  rw [sum_roots_of_passive_zero (fun r => z r * (dataLinkGraph G r).edgePolynomial w)
    (fun r hr => by rw [dataLink_passive_zero G hG r hr, mul_zero])]
  have hbound (r : Root) : z r * (dataLinkGraph G r).edgePolynomial w ≤
      z r * ((∑ d, w d) ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left (linkVector_bounds G w hw r).2 (hz r)
  calc
    _ ≤ (∑ r : Layer, z (layerRoot r) * ((∑ d, w d) ^ 2 / 2)) +
        ∑ j : Fin N, z (genericRoot j) * ((∑ d, w d) ^ 2 / 2) :=
      add_le_add (Finset.sum_le_sum fun r _ => hbound (layerRoot r))
        (Finset.sum_le_sum fun j _ => hbound (genericRoot j))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; unfold activeRootWeight; ring

theorem oneRootContribution_budget (G : RGraph (Root ⊕ D) 3) (hG : RootedLegal G (sumRooting D))
    (z : Root → ℝ) (w : D → ℝ) (hz : ∀ r, 0 ≤ z r) (hw : ∀ d, 0 ≤ w d)
    (hb : ∀ r, z r ≤ 2 / (q : ℝ)) :
    oneRootContribution G z w ≤ activeRootBudget * (∑ d, w d) ^ 2 / 2 := by
  apply (oneRootContribution_bound G hG z w hz hw).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (activeRootWeight_bound z hb) (sq_nonneg _)) (by norm_num)

theorem data_mass_constraint (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (z : Root → ℝ) (w : D → ℝ) (hx : ProbabilityWeights (Sum.elim z w))
    (hmax : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ G.edgePolynomial (Sum.elim z w))
    (hclique : Optimization.RootLocalization.cliqueProbability (q : ℝ) ≤
      6 * G.edgePolynomial (Sum.elim z w))
    (hb : ∀ r, z r ≤ 2 / (q : ℝ)) (ht : 0 < ∑ d, w d) :
    Optimization.RootLocalization.cliqueProbability (q : ℝ) ≤
      (1 - 1 / (q : ℝ)) * (∑ r, z r) ^ 2 + 2 * activeRootBudget * (∑ d, w d) := by
  have hz : ∀ r, 0 ≤ z r := fun r => hx.1 (Sum.inl r)
  have hw : ∀ d, 0 ≤ w d := fun d => hx.1 (Sum.inr d)
  have he := data_euler_identity G hG z w hx hmax
  have htwo := twoRootContribution_bound G z w hz hw
  have hone := oneRootContribution_budget G hG.legal z w hz hw hb
  have hp : 6 * G.edgePolynomial (Sum.elim z w) ≤
      2 * elementary Finset.univ z 2 + 2 * activeRootBudget * (∑ d, w d) := by
    apply le_of_mul_le_mul_right (a := ∑ d, w d) _ ht
    nlinarith only [he, htwo, hone]
  have hroot := Optimization.two_elementary_le_clique_factor q_pos z
  rw [Optimization.elementary_eq_sum] at hroot
  change 2 * elementary Finset.univ z 2 ≤
    (1 - 1 / (q : ℝ)) * (∑ r, z r) ^ 2 at hroot
  linarith

end TranscendentalTuran.Source.RootData
