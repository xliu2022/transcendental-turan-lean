module

public import TranscendentalTuran.Construction.RootCompletion
public import TranscendentalTuran.Construction.RootDataPolynomial
public import TranscendentalTuran.Construction.RootPairWeights
public import TranscendentalTuran.Optimization.RootTransfer

@[expose] public section

namespace TranscendentalTuran.Source.RootData

open TuranUniversality TuranUniversality.Weighted Encoding Network
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The graph-side meaning of completion, independent of the original
partial-rooted host used to construct it. -/
structure Completed (G : RGraph (Root ⊕ D) 3) : Prop where
  legal : RootedLegal G (sumRooting D)
  root_clique : ∀ p : Finset Root, p.card = 3 → p.image Sum.inl ∈ G.edges
  neutral_pairs : ∀ p : Finset Root, p.card = 2 → p ∉ Γ → ∀ d : D,
    insert (Sum.inr d) (p.image Sum.inl) ∈ G.edges

theorem completion_completed {V : Type} [Fintype V] [DecidableEq V]
    (G : RGraph V 3) (μ : Rooting Root V) (hG : RootedLegal G μ) :
    Completed (Completion.graph G μ) :=
  ⟨Completion.rootedLegal G μ hG, Completion.graph_root_clique G μ,
    Completion.graph_neutral_pair G μ⟩

def missingPairGraph (G : RGraph (Root ⊕ D) 3) (d : D) : RGraph Root 2 :=
  ⟨Finset.univ.powersetCard 2 \ (rootLinkGraph G d).edges,
    fun p hp => (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp hp).1).2⟩

theorem mem_missingPairGraph (G : RGraph (Root ⊕ D) 3) (d : D) (p : Finset Root) :
    p ∈ (missingPairGraph G d).edges ↔ p.card = 2 ∧ p ∉ (rootLinkGraph G d).edges := by
  simp only [missingPairGraph, Finset.mem_sdiff, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]

theorem missingPairGraph_subset_Γ (G : RGraph (Root ⊕ D) 3) (hG : Completed G) (d : D) :
    (missingPairGraph G d).edges ⊆ Γ := by
  intro p hp
  by_contra hn
  obtain ⟨hcard, hnot⟩ := (mem_missingPairGraph G d p).mp hp
  apply hnot
  apply ((model G).mem_rootLink d p).mpr
  apply (mem_model G p {d}).mpr
  have he := hG.neutral_pairs p hcard hn d
  convert he using 1
  ext (r | x) <;> simp

theorem missing_neighbors_card_le_one (G : RGraph (Root ⊕ D) 3)
    (hG : Completed G) (d : D) (i : Root) :
    (Finset.univ.filter fun j => {i, j} ∈ (missingPairGraph G d).edges).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have hea := (Finset.mem_filter.mp ha).2
  have heb := (Finset.mem_filter.mp hb).2
  have hΓa := missingPairGraph_subset_Γ G hG d hea
  have hΓb := missingPairGraph_subset_Γ G hG d heb
  have heq : ({i, a} : Finset Root) = {i, b} := by
    by_contra hne
    exact Finset.disjoint_left.mp (Γ_matching hΓa hΓb hne)
      (by simp : i ∈ ({i, a} : Finset Root)) (by simp)
  have hia : i ≠ a := Finset.card_pair_eq_two_iff.mp ((missingPairGraph G d).uniform _ hea)
  have ha' : a ∈ ({i, b} : Finset Root) := by rw [← heq]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
  exact ha'.resolve_left (Ne.symm hia)

/-- Actual data mass missing each root pair; the diagonal vanishes
because a singleton cannot be an edge of the missing pair graph. -/
def missingMatrix (G : RGraph (Root ⊕ D) 3) (w : D → ℝ) : Matrix Root Root ℝ :=
  fun i j => ∑ d, if {i, j} ∈ (missingPairGraph G d).edges then w d else 0

def linkVector (G : RGraph (Root ⊕ D) 3) (w : D → ℝ) (r : Root) : ℝ :=
  (dataLinkGraph G r).edgePolynomial w

theorem missingMatrix_symmetric (G : RGraph (Root ⊕ D) 3) (w : D → ℝ) (i j : Root) :
    missingMatrix G w i j = missingMatrix G w j i := by
  simp only [missingMatrix, Finset.pair_comm i j]

theorem missingMatrix_nonneg (G : RGraph (Root ⊕ D) 3) (w : D → ℝ)
    (hw : ∀ d, 0 ≤ w d) (i j : Root) : 0 ≤ missingMatrix G w i j := by
  apply Finset.sum_nonneg
  intro d _
  split_ifs <;> first | exact hw d | exact le_rfl

theorem missingMatrix_row_bound (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (w : D → ℝ) (hw : ∀ d, 0 ≤ w d) (i : Root) :
    (∑ j, missingMatrix G w i j) ≤ ∑ d, w d := by
  classical
  unfold missingMatrix
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro d _
  let S := Finset.univ.filter fun j => {i, j} ∈ (missingPairGraph G d).edges
  have hc : (S.card : ℝ) ≤ 1 := by exact_mod_cast missing_neighbors_card_le_one G hG d i
  calc
    (∑ j, if {i, j} ∈ (missingPairGraph G d).edges then w d else 0) = ∑ _j ∈ S, w d := by
      rw [Finset.sum_filter]
    _ = (S.card : ℝ) * w d := by simp
    _ ≤ w d := by nlinarith [hw d]

theorem linkVector_bounds (G : RGraph (Root ⊕ D) 3) (w : D → ℝ)
    (hw : ∀ d, 0 ≤ w d) (r : Root) :
    0 ≤ linkVector G w r ∧ linkVector G w r ≤ (∑ d, w d) ^ 2 / 2 := by
  refine ⟨(dataLinkGraph G r).edgePolynomial_nonneg hw, ?_⟩
  have hcomplete : linkVector G w r ≤ elementary Finset.univ w 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (dataLinkGraph G r).uniform _ hp⟩
    · intro p _ _
      exact Finset.prod_nonneg (fun d _ => hw d)
  have he := elementary_second_identity Finset.univ w
  have hs : 0 ≤ ∑ d, w d ^ 2 := Finset.sum_nonneg (fun d _ => sq_nonneg _)
  linarith

theorem rootLink_missing_sum (G : RGraph (Root ⊕ D) 3) (d : D) (z : Root → ℝ) :
    (rootLinkGraph G d).edgePolynomial z + (missingPairGraph G d).edgePolynomial z =
      elementary Finset.univ z 2 := by
  have hs : (rootLinkGraph G d).edges ⊆ Finset.univ.powersetCard 2 := by
    intro p hp
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (rootLinkGraph G d).uniform _ hp⟩
  have hh := Finset.sum_sdiff (f := fun p : Finset Root => ∏ r ∈ p, z r) hs
  simpa only [RGraph.edgePolynomial, missingPairGraph, elementary, add_comm] using hh

theorem missingMatrix_form (G : RGraph (Root ⊕ D) 3) (w : D → ℝ) (z : Root → ℝ) :
    (missingMatrix G w).toBilin' z z =
      2 * ∑ d, w d * (missingPairGraph G d).edgePolynomial z := by
  classical
  calc
    (missingMatrix G w).toBilin' z z =
        ∑ i, ∑ j, ∑ d, if {i, j} ∈ (missingPairGraph G d).edges then w d * (z i * z j) else 0 := by
      simp only [Matrix.toBilin'_apply, missingMatrix, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> ring
    _ = ∑ i, ∑ d, ∑ j, if {i, j} ∈ (missingPairGraph G d).edges then w d * (z i * z j) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ d, ∑ i, ∑ j, if {i, j} ∈ (missingPairGraph G d).edges then w d * (z i * z j) else 0 :=
      Finset.sum_comm
    _ = ∑ d, w d * (2 * (missingPairGraph G d).edgePolynomial z) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [pairGraph_ordered_sum]
      simp only [Finset.mul_sum, mul_ite, mul_zero]
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring

/-- The exact missing-pair polynomial identity needed for genuine root
weight transfers. Every coefficient is extracted from the actual host. -/
theorem completed_polynomial_eq (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (w : D → ℝ) (z : Root → ℝ) :
    G.edgePolynomial (Sum.elim z w) =
      Optimization.RootTransfer.completePolynomial (∑ d, w d) (missingMatrix G w) (linkVector G w) z := by
  rw [complete_polynomial_links G hG.legal hG.root_clique,
    Optimization.RootTransfer.completePolynomial_eq, missingMatrix_form]
  have hsum : (∑ d, w d * (rootLinkGraph G d).edgePolynomial z) +
      (∑ d, w d * (missingPairGraph G d).edgePolynomial z) =
        (∑ d, w d) * elementary Finset.univ z 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [← mul_add, rootLink_missing_sum]
  have he3 : Optimization.elementary z 3 = elementary Finset.univ z 3 :=
    Optimization.elementary_eq_sum z 3
  have he2 : Optimization.elementary z 2 = elementary Finset.univ z 2 :=
    Optimization.elementary_eq_sum z 2
  rw [he3, he2]
  change elementary Finset.univ z 3 + _ + (∑ r, z r * linkVector G w r) = _
  linarith

end TranscendentalTuran.Source.RootData
