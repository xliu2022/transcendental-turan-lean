module

public import TuranUniversality.Hypergraph.Lagrangian
public import TranscendentalTuran.Optimization.QuadraticDirections
public import TranscendentalTuran.Optimization.RootLocalization
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-!
# First-order conditions for the actual edge polynomial

Formalization author and responsible maintainer: Xizhi Liu.

The derivatives below are finite sums of products over the genuine edges
of `RGraph`. No formal derivative or optimality condition is assumed.
-/

namespace TranscendentalTuran.Optimization.GraphCalculus

open Set Finset TuranUniversality

variable {V : Type*} [DecidableEq V] [Fintype V] {r : ℕ}

noncomputable def edgePartial (G : RGraph V r) (x : V → ℝ) (v : V) : ℝ :=
  ∑ e ∈ G.edges with v ∈ e, ∏ u ∈ e.erase v, x u

noncomputable def edgeDirection (G : RGraph V r) (x d : V → ℝ) : ℝ :=
  ∑ e ∈ G.edges, ∑ v ∈ e, d v * ∏ u ∈ e.erase v, x u

private theorem sum_univ_if_mem (s : Finset V) (f : V → ℝ) :
    (∑ v : V, if v ∈ s then f v else 0) = ∑ v ∈ s, f v := by
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

theorem edgeDirection_eq_sum_partials (G : RGraph V r) (x d : V → ℝ) :
    edgeDirection G x d = ∑ v : V, d v * edgePartial G x v := by
  unfold edgeDirection edgePartial
  simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  exact (sum_univ_if_mem e _).symm

theorem edgeDirection_single (G : RGraph V r) (x : V → ℝ) (v : V) :
    edgeDirection G x (Pi.single v 1) = edgePartial G x v := by
  rw [edgeDirection_eq_sum_partials]
  simp [Pi.single_apply]

theorem edgeDirection_sub (G : RGraph V r) (x d e : V → ℝ) :
    edgeDirection G x (d - e) = edgeDirection G x d - edgeDirection G x e := by
  simp only [edgeDirection, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem edgeDirection_self (G : RGraph V r) (x : V → ℝ) :
    edgeDirection G x x = (r : ℝ) * G.edgePolynomial x := by
  unfold edgeDirection RGraph.edgePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  calc
    (∑ v ∈ e, x v * ∏ u ∈ e.erase v, x u) = ∑ _v ∈ e, ∏ u ∈ e, x u :=
      Finset.sum_congr rfl (fun v hv => Finset.mul_prod_erase e x hv)
    _ = (r : ℝ) * ∏ u ∈ e, x u := by simp only [Finset.sum_const, nsmul_eq_mul, G.uniform e he]

theorem edgePolynomial_const_mul (G : RGraph V r) (c : ℝ) (x : V → ℝ) :
    G.edgePolynomial (fun v => c * x v) = c ^ r * G.edgePolynomial x := by
  unfold RGraph.edgePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [Finset.prod_mul_distrib, Finset.prod_const, G.uniform e he]

theorem edgePolynomial_root_normalization (G : RGraph V 3) (x : V → ℝ)
    {s : ℝ} (hs : s ≠ 0) :
    G.edgePolynomial x = s ^ 3 * G.edgePolynomial (fun v => x v / s) := by
  rw [← edgePolynomial_const_mul]
  congr 1
  funext v
  field_simp [hs]

theorem edgePolynomial_hasDerivAt_line (G : RGraph V r) (x d : V → ℝ) :
    HasDerivAt (fun t : ℝ => G.edgePolynomial (x + t • d)) (edgeDirection G x d) 0 := by
  unfold RGraph.edgePolynomial edgeDirection
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply HasDerivAt.fun_sum
  intro e _
  have hv (v : V) : HasDerivAt (fun t : ℝ => x v + t * d v) (d v) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (x v)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (d v)) using 1 <;>
        try simp only [zero_add, one_mul]
    all_goals first | rfl | (funext t; rfl)
  convert HasDerivAt.fun_finsetProd (fun v (_ : v ∈ e) => hv v) using 1
  simp only [zero_mul, mul_zero, add_zero, smul_eq_mul, mul_comm]

theorem probability_transfer {x : V → ℝ} (hx : ProbabilityWeights x)
    (i j : V) (hij : i ≠ j) {t : ℝ} (ht : 0 ≤ t) (hti : t ≤ x i) :
    ProbabilityWeights (x + t • (Pi.single j 1 - Pi.single i 1)) := by
  constructor
  · intro k
    change 0 ≤ x k + t * ((Pi.single j 1 : V → ℝ) k - (Pi.single i 1 : V → ℝ) k)
    by_cases hki : k = i
    · subst k
      simp [Pi.single_apply, hij, Ne.symm hij]
      linarith
    · by_cases hkj : k = j
      · subst k
        simp [Pi.single_apply, hij, Ne.symm hij]
        exact add_nonneg (hx.1 j) ht
      · simpa [Pi.single_apply, hki, hkj, Ne.symm hki, Ne.symm hkj] using hx.1 k
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Pi.sub_apply, Finset.sum_sub_distrib]
    simp [Pi.single_apply, hx.2]

/-- At a global maximum, transferring mass away from a positive-weight
vertex cannot increase the edge polynomial, even when the receiver has
weight zero. -/
theorem edgePartial_le_of_maximum (G : RGraph V r) {x : V → ℝ}
    (hx : ProbabilityWeights x)
    (hmax : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ G.edgePolynomial x)
    {i : V} (hi : 0 < x i) (j : V) : edgePartial G x j ≤ edgePartial G x i := by
  by_cases hij : i = j
  · subst j; exact le_rfl
  have hd := edgePolynomial_hasDerivAt_line G x (Pi.single j 1 - Pi.single i 1)
  have hder := deriv_nonpos_of_right_max hd hi (by
    intro t ht
    simpa using hmax _ (probability_transfer hx i j hij ht.1 ht.2))
  rw [edgeDirection_sub, edgeDirection_single, edgeDirection_single] at hder
  linarith

theorem edgePartial_eq_on_positive_support (G : RGraph V r) {x : V → ℝ}
    (hx : ProbabilityWeights x)
    (hmax : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ G.edgePolynomial x)
    {i j : V} (hi : 0 < x i) (hj : 0 < x j) :
    edgePartial G x i = edgePartial G x j :=
  le_antisymm (edgePartial_le_of_maximum G hx hmax hj i)
    (edgePartial_le_of_maximum G hx hmax hi j)

/-- Euler's identity and the feasible transfer inequalities identify the
common partial derivative on the positive support. -/
theorem edgePartial_eq_degree_mul (G : RGraph V r) {x : V → ℝ}
    (hx : ProbabilityWeights x)
    (hmax : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ G.edgePolynomial x)
    {i : V} (hi : 0 < x i) : edgePartial G x i = (r : ℝ) * G.edgePolynomial x := by
  calc
    edgePartial G x i = ∑ v : V, x v * edgePartial G x i := by
      rw [← Finset.sum_mul, hx.2, one_mul]
    _ = ∑ v : V, x v * edgePartial G x v := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : x v = 0
      · simp only [hv, zero_mul]
      · rw [edgePartial_eq_on_positive_support G hx hmax hi
          (lt_of_le_of_ne (hx.1 v) (Ne.symm hv))]
    _ = edgeDirection G x x := (edgeDirection_eq_sum_partials G x x).symm
    _ = _ := edgeDirection_self G x

def withoutCoordinate (x : V → ℝ) (v : V) : V → ℝ := fun u => if u = v then 0 else x u

theorem withoutCoordinate_nonneg {x : V → ℝ} (hx : ∀ u, 0 ≤ x u) (v u : V) :
    0 ≤ withoutCoordinate x v u := by
  unfold withoutCoordinate
  split_ifs
  · exact le_rfl
  · exact hx u

theorem sum_withoutCoordinate (x : V → ℝ) (v : V) :
    (∑ u : V, withoutCoordinate x v u) = (∑ u : V, x u) - x v := by
  have he (u : V) : withoutCoordinate x v u = x u - (if u = v then x v else 0) := by
    by_cases huv : u = v
    · subst u; simp [withoutCoordinate]
    · simp [withoutCoordinate, huv]
  simp only [he, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem edgePartial_le_elementary_two (G : RGraph V 3) {x : V → ℝ}
    (hx : ∀ u, 0 ≤ x u) (v : V) :
    edgePartial G x v ≤ elementary (withoutCoordinate x v) 2 := by
  unfold edgePartial
  rw [elementary_eq_sum]
  apply Finset.sum_le_sum_of_injOn (fun e : Finset V => e.erase v)
  · intro e he f hf hef
    exact Finset.erase_injOn' v (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2 hef
  · intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_powersetCard_univ.mpr
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mp hf).2,
      G.uniform f (Finset.mem_filter.mp hf).1]
  · intro e he
    apply le_of_eq
    apply Finset.prod_congr rfl
    intro u hu
    simp [withoutCoordinate, (Finset.mem_erase.mp hu).1]
  · intro e _ _
    exact Finset.prod_nonneg (fun u _ => withoutCoordinate_nonneg hx v u)

/-- The square-free link at a vertex has at most half the square of the
remaining total weight. -/
theorem twice_edgePartial_le_remaining_square (G : RGraph V 3) {x : V → ℝ}
    (hx : ProbabilityWeights x) (v : V) :
    2 * edgePartial G x v ≤ (1 - x v) ^ 2 := by
  have hl := edgePartial_le_elementary_two G hx.1 v
  have he := two_mul_elementary_two (withoutCoordinate x v)
  rw [sum_withoutCoordinate, hx.2] at he
  have hn : 0 ≤ ∑ u : V, (withoutCoordinate x v u) ^ 2 :=
    Finset.sum_nonneg (fun u _ => sq_nonneg _)
  linarith

/-- Every coordinate at an actual maximum is below `2/q` as soon as the
root clique supplies the manuscript's lower bound for its value. -/
theorem maximizer_coordinate_lt_two_div (G : RGraph V 3) {x : V → ℝ}
    (hx : ProbabilityWeights x)
    (hmax : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ G.edgePolynomial x)
    {q : ℝ} (hq : 64 ≤ q)
    (hclique : RootLocalization.cliqueProbability q ≤ 6 * G.edgePolynomial x)
    (v : V) : x v < 2 / q := by
  by_cases hv : x v = 0
  · rw [hv]
    have hq0 : 0 < q := by linarith
    positivity
  have hp := edgePartial_eq_degree_mul G hx hmax (lt_of_le_of_ne (hx.1 v) (Ne.symm hv))
  have hl := twice_edgePartial_le_remaining_square G hx v
  apply RootLocalization.coordinate_lt_two_div hq (hx.apply_le_one v)
  norm_num at hp
  linarith

end TranscendentalTuran.Optimization.GraphCalculus
