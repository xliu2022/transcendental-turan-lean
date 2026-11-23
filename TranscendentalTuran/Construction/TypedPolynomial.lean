module

public import TranscendentalTuran.Construction.RootDataPolynomial
public import TranscendentalTuran.Construction.RootPairWeights
public import TranscendentalTuran.Construction.RootPartition
public import TuranUniversality.Weighted.Types

@[expose] public section

namespace TranscendentalTuran.Source.RootData

open TuranUniversality TuranUniversality.Weighted Encoding Network
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable def typedPartition (τ : D → PhysicalType) : TypePartition (Finset.univ : Finset D) PhysicalType where
  block ν := Finset.univ.filter fun d => τ d = ν
  disjoint := by
    intro ν _ σ _ hne
    apply Finset.disjoint_left.mpr
    intro d hd hd'
    exact hne ((Finset.mem_filter.mp hd).2.symm.trans (Finset.mem_filter.mp hd').2)
  cover := by ext d; simp

noncomputable def typeMass (τ : D → PhysicalType) (w : D → ℝ) : PhysicalType → ℝ :=
  (typedPartition τ).mass w

noncomputable def positiveTypeMass (b : Block) (y : PhysicalType → ℝ) : ℝ :=
  ∑ ν, if sign b ν = 1 then y ν else 0

noncomputable def negativeTypeMass (b : Block) (y : PhysicalType → ℝ) : ℝ :=
  ∑ ν, if sign b ν = -1 then y ν else 0

noncomputable def typedQuadratic (z : Root → ℝ) (y : PhysicalType → ℝ) : ℝ :=
  (∑ j : Fin Parameters.N, z (genericRoot j)) * elementary Finset.univ y 2 +
    (∑ r : Layer, z (layerRoot r) * (positiveTypeMass r.1 y ^ 2 + negativeTypeMass r.1 y ^ 2)) / 2

theorem typeMass_nonneg (τ : D → PhysicalType) (w : D → ℝ) (hw : ∀ d, 0 ≤ w d)
    (ν : PhysicalType) : 0 ≤ typeMass τ w ν :=
  Finset.sum_nonneg (fun d _ => hw d)

theorem sum_typeMass (τ : D → PhysicalType) (w : D → ℝ) :
    (∑ ν, typeMass τ w ν) = ∑ d, w d := (typedPartition τ).sum_blocks w

theorem sum_by_type (τ : D → PhysicalType) (w : D → ℝ) (f : PhysicalType → ℝ) :
    (∑ d, w d * f (τ d)) = ∑ ν, typeMass τ w ν * f ν := by
  rw [← (typedPartition τ).sum_blocks (fun d => w d * f (τ d))]
  apply Finset.sum_congr rfl
  intro ν _
  rw [typeMass, TypePartition.mass, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  exact congrArg (fun a => w d * f a) (Finset.mem_filter.mp hd).2

theorem dataLink_subset_crossPairs (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (τ : D → PhysicalType)
    (ht : ∀ d, Declared G (sumRooting D) (τ d) (Sum.inr d)) (r : Root) (hr : IsGeneric r) :
    (dataLinkGraph G r).edges ⊆ (typedPartition τ).crossPairs := by
  intro p hp
  have hc := (dataLinkGraph G r).uniform p hp
  obtain ⟨a, b, _hab, rfl⟩ := Finset.card_eq_two.mp hc
  have hne := hG.generic_different r hr _ _ _ _ (ht a) (ht b)
    ((dataLinkGraph_mem_pair G r a b).mp hp)
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc⟩, ?_⟩
  intro hw
  obtain ⟨ν, _hν, hpair⟩ := Finset.mem_biUnion.mp hw
  have hsub := (Finset.mem_powersetCard.mp hpair).1
  have ha := (Finset.mem_filter.mp (hsub (by simp : a ∈ ({a, b} : Finset D)))).2
  have hb := (Finset.mem_filter.mp (hsub (by simp : b ∈ ({a, b} : Finset D)))).2
  exact hne (ha.trans hb.symm)

theorem dataLink_generic_bound (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (τ : D → PhysicalType)
    (ht : ∀ d, Declared G (sumRooting D) (τ d) (Sum.inr d))
    (r : Root) (hr : IsGeneric r) (w : D → ℝ) (hw : ∀ d, 0 ≤ w d) :
    (dataLinkGraph G r).edgePolynomial w ≤ elementary Finset.univ (typeMass τ w) 2 := by
  change (dataLinkGraph G r).edgePolynomial w ≤
    elementary Finset.univ ((typedPartition τ).mass w) 2
  rw [← (typedPartition τ).crossWeight_eq w]
  apply Finset.sum_le_sum_of_subset_of_nonneg (dataLink_subset_crossPairs G hG τ ht r hr)
  intro p _ _
  exact Finset.prod_nonneg (fun d _ => hw d)

noncomputable def markedMass (G : RGraph (Root ⊕ D) 3) (w : D → ℝ) : ℝ := by
  classical
  exact ∑ d, if Marked G (sumRooting D) (Sum.inr d) then w d else 0

theorem markedMass_nonneg (G : RGraph (Root ⊕ D) 3) (w : D → ℝ) (hw : ∀ d, 0 ≤ w d) :
    0 ≤ markedMass G w := by
  classical
  apply Finset.sum_nonneg
  intro d _
  split_ifs <;> first | exact hw d | exact le_rfl

theorem rootLink_subset_allowed (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (τ : D → PhysicalType)
    (ht : ∀ d, Declared G (sumRooting D) (τ d) (Sum.inr d)) (d : D) :
    (rootLinkGraph G d).edges ⊆ allowedPairs (τ d) ∪
      (if Marked G (sumRooting D) (Sum.inr d) then {markerPair} else ∅) := by
  classical
  intro p hp
  by_cases hΓ : p ∈ Γ
  · rcases Finset.mem_insert.mp hΓ with hmark | hdecl
    · subst p
      have hm : Marked G (sumRooting D) (Sum.inr d) :=
        (rootLinkGraph_mem_pair G markerLeft markerRight d).mp hp
      exact Finset.mem_union_right _ (by simp [hm])
    · obtain ⟨⟨ν, j⟩, _, rfl⟩ := Finset.mem_image.mp hdecl
      have he : PairLink G (sumRooting D) (declaringRoot ((ν, j), 0))
          (declaringRoot ((ν, j), 1)) (Sum.inr d) :=
        (rootLinkGraph_mem_pair G _ _ d).mp (by simpa only [declaringPair_eq] using hp)
      have hd : Declared G (sumRooting D) (physicalOfIndex ν) (Sum.inr d) :=
        ⟨sumRooting_inr_data d, Or.inl ⟨j, by simpa only [physicalIndex_physicalOfIndex] using he⟩⟩
      have hτ := hG.declarations_unique _ _ _ (ht d) hd
      have hi : physicalIndex (τ d) = ν := by rw [hτ, physicalIndex_physicalOfIndex]
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      rw [hi]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact (mem_neutralPairs p).mpr ⟨(rootLinkGraph G d).uniform _ hp, hΓ⟩

theorem rootLink_weight_bound (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (τ : D → PhysicalType)
    (ht : ∀ d, Declared G (sumRooting D) (τ d) (Sum.inr d))
    (d : D) (z : Root → ℝ) (hz : ∀ r, 0 ≤ z r) :
    (rootLinkGraph G d).edgePolynomial z ≤ pairWeight (allowedPairs (τ d)) z +
      if Marked G (sumRooting D) (Sum.inr d) then markerWeight z else 0 := by
  classical
  calc
    (rootLinkGraph G d).edgePolynomial z ≤ pairWeight (allowedPairs (τ d) ∪
        (if Marked G (sumRooting D) (Sum.inr d) then {markerPair} else ∅)) z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (rootLink_subset_allowed G hG τ ht d)
      intro p _ _
      exact Finset.prod_nonneg (fun r _ => hz r)
    _ = _ := by
      by_cases hm : Marked G (sumRooting D) (Sum.inr d)
      · rw [if_pos hm, if_pos hm]
        have hdis : Disjoint (allowedPairs (τ d)) {markerPair} := by
          apply Finset.disjoint_left.mpr
          intro p hp hp'
          have he := Finset.mem_singleton.mp hp'
          subst p
          exact markerPair_not_allowedPairs _ hp
        rw [pairWeight, Finset.sum_union hdis]
        simp [pairWeight, markerPair, marker_distinct, markerWeight]
      · simp only [hm, if_false, Finset.union_empty, add_zero]

theorem two_root_weight_bound (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (τ : D → PhysicalType)
    (ht : ∀ d, Declared G (sumRooting D) (τ d) (Sum.inr d))
    (z : Root → ℝ) (w : D → ℝ) (hz : ∀ r, 0 ≤ z r) (hw : ∀ d, 0 ≤ w d) :
    (∑ d, w d * (rootLinkGraph G d).edgePolynomial z) ≤
      (∑ ν, typeMass τ w ν * pairWeight (allowedPairs ν) z) + markerWeight z * markedMass G w := by
  classical
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun d _ =>
    mul_le_mul_of_nonneg_left (rootLink_weight_bound G hG τ ht d z hz) (hw d))
  simp only [mul_add, Finset.sum_add_distrib] at hh
  rw [sum_by_type τ w (fun ν => pairWeight (allowedPairs ν) z)] at hh
  have hm : (∑ d, w d * (if Marked G (sumRooting D) (Sum.inr d) then markerWeight z else 0)) =
      markerWeight z * markedMass G w := by
    simp only [markedMass, Finset.mul_sum, mul_ite, mul_zero]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> ring
  rw [hm] at hh
  exact hh

theorem positiveAt_inr_iff (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (τ : D → PhysicalType)
    (ht : ∀ d, Declared G (sumRooting D) (τ d) (Sum.inr d)) (b : Block) (d : D) :
    PositiveAt G (sumRooting D) b (Sum.inr d) ↔ sign b (τ d) = 1 := by
  constructor
  · rintro ⟨ν, hν, hs⟩
    have he := hG.declarations_unique _ _ _ (ht d) hν
    exact he.symm ▸ hs
  · exact fun hs => ⟨τ d, ht d, hs⟩

theorem negativeAt_inr_iff (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (τ : D → PhysicalType)
    (ht : ∀ d, Declared G (sumRooting D) (τ d) (Sum.inr d)) (b : Block) (d : D) :
    NegativeAt G (sumRooting D) b (Sum.inr d) ↔ sign b (τ d) = -1 := by
  constructor
  · rintro ⟨ν, hν, hs⟩
    have he := hG.declarations_unique _ _ _ (ht d) hν
    exact he.symm ▸ hs
  · exact fun hs => ⟨τ d, ht d, hs⟩

theorem positiveMass_eq (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (τ : D → PhysicalType)
    (ht : ∀ d, Declared G (sumRooting D) (τ d) (Sum.inr d)) (b : Block) (w : D → ℝ) :
    (∑ c : PositiveVertex G (sumRooting D) b, dataWeights w c.val) =
      positiveTypeMass b (typeMass τ w) := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (PositiveAt G (sumRooting D) b))
    (by intro v; simp) (dataWeights w)]
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  simp only [dataWeights, Sum.elim_inl, Sum.elim_inr, ite_self, Finset.sum_const_zero, zero_add]
  simp_rw [positiveAt_inr_iff G hG τ ht]
  have hh := sum_by_type τ w (fun ν => if sign b ν = 1 then (1 : ℝ) else 0)
  simpa only [mul_ite, mul_one, mul_zero, positiveTypeMass] using hh

theorem negativeMass_eq (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (τ : D → PhysicalType)
    (ht : ∀ d, Declared G (sumRooting D) (τ d) (Sum.inr d)) (b : Block) (w : D → ℝ) :
    (∑ l : NegativeVertex G (sumRooting D) b, dataWeights w l.val) =
      negativeTypeMass b (typeMass τ w) := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (NegativeAt G (sumRooting D) b))
    (by intro v; simp) (dataWeights w)]
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  simp only [dataWeights, Sum.elim_inl, Sum.elim_inr, ite_self, Finset.sum_const_zero, zero_add]
  simp_rw [negativeAt_inr_iff G hG τ ht]
  have hh := sum_by_type τ w (fun ν => if sign b ν = -1 then (1 : ℝ) else 0)
  simpa only [mul_ite, mul_one, mul_zero, negativeTypeMass] using hh

theorem one_root_weight_bound (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (τ : D → PhysicalType)
    (ht : ∀ d, Declared G (sumRooting D) (τ d) (Sum.inr d))
    (z : Root → ℝ) (w : D → ℝ) (hz : ∀ r, 0 ≤ z r) (hw : ∀ d, 0 ≤ w d) :
    (∑ r, z r * (dataLinkGraph G r).edgePolynomial w) ≤
      typedQuadratic z (typeMass τ w) - actualEnergy (G := G) (μ := sumRooting D) z (dataWeights w) / 2 := by
  classical
  have hall : ∀ v, Data (sumRooting D) v → ∃ ν, Declared G (sumRooting D) ν v := by
    intro v hv
    obtain ⟨d, rfl⟩ := sumRooting_data_exists hv
    exact ⟨τ d, ht d⟩
  have hspecial : (∑ r : Layer, z (layerRoot r) * (dataLinkGraph G (layerRoot r)).edgePolynomial w) ≤
      (∑ r : Layer, z (layerRoot r) *
        (positiveTypeMass r.1 (typeMass τ w) ^ 2 + negativeTypeMass r.1 (typeMass τ w) ^ 2)) / 2 -
      actualEnergy (G := G) (μ := sumRooting D) z (dataWeights w) / 2 := by
    calc
      _ ≤ ∑ r : Layer, z (layerRoot r) *
          ((positiveTypeMass r.1 (typeMass τ w) ^ 2 + negativeTypeMass r.1 (typeMass τ w) ^ 2 -
            actualLayerEnergy (G := G) (μ := sumRooting D) r (dataWeights w)) / 2) := by
        apply Finset.sum_le_sum
        intro r _
        apply mul_le_mul_of_nonneg_left _ (hz _)
        have hh := dataLink_layer_bound G hG hall r w hw
        rw [positiveMass_eq G hG τ ht, negativeMass_eq G hG τ ht] at hh
        exact hh
      _ = _ := by
        simp only [mul_div, mul_sub, sub_div, actualEnergy, Finset.sum_div, Finset.sum_sub_distrib]
  have hgeneric : (∑ j : Fin Parameters.N, z (genericRoot j) *
      (dataLinkGraph G (genericRoot j)).edgePolynomial w) ≤
      (∑ j : Fin Parameters.N, z (genericRoot j)) * elementary Finset.univ (typeMass τ w) 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left
      (dataLink_generic_bound G hG τ ht _ (genericRoot_isGeneric j) w hw) (hz _)
  rw [sum_roots_of_passive_zero (fun r => z r * (dataLinkGraph G r).edgePolynomial w)
    (by intro r hr; rw [dataLink_passive_zero G hG r hr w, mul_zero])]
  unfold typedQuadratic
  linarith

/-- The paper's atomic upper bound, derived from the ordinary edge set
and the actual individual-layer components. -/
theorem atomic_polynomial_bound (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (τ : D → PhysicalType)
    (ht : ∀ d, Declared G (sumRooting D) (τ d) (Sum.inr d))
    (z : Root → ℝ) (w : D → ℝ) (hz : ∀ r, 0 ≤ z r) (hw : ∀ d, 0 ≤ w d) :
    G.edgePolynomial (Sum.elim z w) ≤ elementary Finset.univ z 3 +
      (∑ ν, typeMass τ w ν * pairWeight (allowedPairs ν) z) +
      typedQuadratic z (typeMass τ w) + markerWeight z * markedMass G w -
      actualEnergy (G := G) (μ := sumRooting D) z (dataWeights w) / 2 := by
  have hpoly := polynomial_links_bound G hG z w hz
  have htwo := two_root_weight_bound G hG τ ht z w hz hw
  have hone := one_root_weight_bound G hG τ ht z w hz hw
  linarith

end TranscendentalTuran.Source.RootData
