module

public import TranscendentalTuran.Construction.CompletedPolynomial
public import TranscendentalTuran.Construction.RootPartition
public import TranscendentalTuran.Optimization.GraphDerivatives
public import TranscendentalTuran.Optimization.ElementaryBounds

@[expose] public section

/-!
# The actual data-direction Euler identity

Formalization author and responsible maintainer: Xizhi Liu.

Scaling all data weights differentiates the actual finite edge polynomial.
At a probability maximum its derivative is three times the value times the
data mass. The root/link decomposition bounds it without a typing hypothesis.
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

def twoRootContribution (G : RGraph (Root ⊕ D) 3) (z : Root → ℝ) (w : D → ℝ) : ℝ :=
  ∑ d, w d * (rootLinkGraph G d).edgePolynomial z

def oneRootContribution (G : RGraph (Root ⊕ D) 3) (z : Root → ℝ) (w : D → ℝ) : ℝ :=
  ∑ r, z r * (dataLinkGraph G r).edgePolynomial w

theorem data_direction_polynomial (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (z : Root → ℝ) (w : D → ℝ) (a : ℝ) :
    G.edgePolynomial ((Sum.elim z w) + a • dataWeights w) =
      elementary Finset.univ z 3 + (1 + a) * twoRootContribution G z w +
        (1 + a) ^ 2 * oneRootContribution G z w := by
  have hx : (Sum.elim z w) + a • dataWeights w =
      Sum.elim z (fun d => (1 + a) * w d) := by
    funext v
    cases v <;> simp [dataWeights, mul_add, add_mul]
  rw [hx, complete_polynomial_links G hG.legal hG.root_clique]
  simp only [edgePolynomial_const_mul, twoRootContribution, oneRootContribution,
    Finset.mul_sum]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro d _
    ring
  · apply Finset.sum_congr rfl
    intro r _
    ring

theorem data_direction_coefficients (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (z : Root → ℝ) (w : D → ℝ) :
    edgeDirection G (Sum.elim z w) (dataWeights w) =
      twoRootContribution G z w + 2 * oneRootContribution G z w := by
  have hd := edgePolynomial_hasDerivAt_line G (Sum.elim z w) (dataWeights w)
  have he : (fun a : ℝ => G.edgePolynomial ((Sum.elim z w) + a • dataWeights w)) =
      (fun a => elementary Finset.univ z 3 + (1 + a) * twoRootContribution G z w +
        (1 + a) ^ 2 * oneRootContribution G z w) :=
    funext (data_direction_polynomial G hG z w)
  rw [he] at hd
  have hlin : HasDerivAt (fun a : ℝ => 1 + a) 1 0 := by
    convert (hasDerivAt_id (0 : ℝ)).const_add (1 : ℝ) using 1
    rfl
  have hp : HasDerivAt
      (fun a : ℝ => elementary Finset.univ z 3 + (1 + a) * twoRootContribution G z w +
        (1 + a) ^ 2 * oneRootContribution G z w)
      (twoRootContribution G z w + 2 * oneRootContribution G z w) 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (elementary Finset.univ z 3)).add
      (hlin.mul_const (twoRootContribution G z w))).add
      ((hlin.pow 2).mul_const (oneRootContribution G z w)) using 1 <;> norm_num
  exact hd.unique hp

theorem data_direction_at_maximum (G : RGraph (Root ⊕ D) 3)
    (z : Root → ℝ) (w : D → ℝ) (hx : ProbabilityWeights (Sum.elim z w))
    (hmax : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ G.edgePolynomial (Sum.elim z w)) :
    edgeDirection G (Sum.elim z w) (dataWeights w) =
      3 * G.edgePolynomial (Sum.elim z w) * (∑ d, w d) := by
  rw [edgeDirection_eq_sum_partials, Fintype.sum_sum_type]
  simp only [dataWeights, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, zero_add]
  calc
    _ = ∑ d, w d * (3 * G.edgePolynomial (Sum.elim z w)) := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : w d = 0
      · simp [hd]
      · have hp : 0 < (Sum.elim z w) (Sum.inr d) :=
          lt_of_le_of_ne (hx.1 (Sum.inr d)) (Ne.symm hd)
        rw [edgePartial_eq_degree_mul G hx hmax hp]
        norm_num
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem data_euler_identity (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (z : Root → ℝ) (w : D → ℝ) (hx : ProbabilityWeights (Sum.elim z w))
    (hmax : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ G.edgePolynomial (Sum.elim z w)) :
    3 * G.edgePolynomial (Sum.elim z w) * (∑ d, w d) =
      twoRootContribution G z w + 2 * oneRootContribution G z w := by
  rw [← data_direction_at_maximum G z w hx hmax, data_direction_coefficients G hG]

end TranscendentalTuran.Source.RootData
