module

public import TranscendentalTuran.Green.Realization.ActualLayerPolynomial
public import TranscendentalTuran.Construction.TypedPolynomial

@[expose] public section

/-!
# Exact ordinary polynomial of a typed lower template

Formalization author and responsible maintainer: Xizhi Liu.

This is an identity for the literal finite simple three-graph `H.graph`.
Its root links, generic links, special links, and marked contribution are
all computed from the graph's actual edge set.
-/

namespace TranscendentalTuran.Green.Realization.TypedData

open Network Encoding Parameters TuranUniversality TuranUniversality.Weighted Source
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D] (H : TypedData D)

theorem graph_root_triple (p : Finset Root) (hp : p.card = 3) :
    p.image Sum.inl ∈ H.graph.edges := by
  change p.image Sum.inl ∈ H.linkData.model.edges.image (fun a => a.1.disjSum a.2)
  refine Finset.mem_image.mpr ⟨(p, ∅), ?_, ?_⟩
  · apply (H.linkData.mem_model_edges p ∅).mpr
    exact Or.inl ⟨rfl, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hp⟩⟩
  · simp only [Finset.disjSum_empty, Finset.map_eq_image]
    rfl

theorem rootLink_edges_eq (d : D) :
    (RootData.rootLinkGraph H.graph d).edges =
      allowedPairs (H.type d) ∪ if d = H.mark then {markerPair} else ∅ := by
  classical
  ext p
  by_cases hc : p.card = 2
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp hc
    rw [RootData.rootLinkGraph_mem_pair, H.graph_pairLink]
  · constructor
    · intro hp
      exact False.elim (hc ((RootData.rootLinkGraph H.graph d).uniform _ hp))
    · intro hp
      exact False.elim (hc (H.linkData.rootLink_uniform d p hp))

theorem rootLink_polynomial_eq (d : D) (z : Root → ℝ) :
    (RootData.rootLinkGraph H.graph d).edgePolynomial z = pairWeight (allowedPairs (H.type d)) z +
      if d = H.mark then markerWeight z else 0 := by
  classical
  rw [RGraph.edgePolynomial, H.rootLink_edges_eq]
  by_cases hd : d = H.mark
  · rw [if_pos hd, if_pos hd]
    have hdis : Disjoint (allowedPairs (H.type d)) {markerPair} := by
      apply Finset.disjoint_left.mpr
      intro p hp hpm
      exact markerPair_not_allowedPairs _ (Finset.mem_singleton.mp hpm ▸ hp)
    rw [Finset.sum_union hdis]
    simp [pairWeight, markerPair, marker_distinct, markerWeight]
  · simp only [hd, ite_false, Finset.union_empty, add_zero, pairWeight]

theorem two_root_polynomial_eq (z : Root → ℝ) (w : D → ℝ) :
    (∑ d, w d * (RootData.rootLinkGraph H.graph d).edgePolynomial z) =
      (∑ ν : PhysicalType, RootData.typeMass H.type w ν * pairWeight (allowedPairs ν) z) +
      markerWeight z * w H.mark := by
  classical
  simp_rw [H.rootLink_polynomial_eq, mul_add]
  rw [Finset.sum_add_distrib,
    RootData.sum_by_type H.type w (fun ν => pairWeight (allowedPairs ν) z)]
  congr 1
  simp [mul_ite, mul_comm]

theorem pair_mem_typedCross (a b : D) (hab : a ≠ b) :
    {a, b} ∈ (RootData.typedPartition H.type).crossPairs ↔ H.type a ≠ H.type b := by
  classical
  constructor
  · intro hp he
    apply (Finset.mem_sdiff.mp hp).2
    apply Finset.mem_biUnion.mpr
    refine ⟨H.type a, Finset.mem_univ _, Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hab⟩⟩
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · simp [RootData.typedPartition]
    · simp [RootData.typedPartition, he]
  · intro hne
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hab⟩, ?_⟩
    intro hp
    obtain ⟨ν, _, hp⟩ := Finset.mem_biUnion.mp hp
    have hs := (Finset.mem_powersetCard.mp hp).1
    have ha := (Finset.mem_filter.mp (hs (by simp : a ∈ ({a, b} : Finset D)))).2
    have hb := (Finset.mem_filter.mp (hs (by simp : b ∈ ({a, b} : Finset D)))).2
    exact hne (ha.trans hb.symm)

theorem genericLink_edges_eq {r : Root} (hr : IsGeneric r) :
    (RootData.dataLinkGraph H.graph r).edges = (RootData.typedPartition H.type).crossPairs := by
  classical
  ext p
  by_cases hc : p.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
    rw [RootData.dataLinkGraph_mem_pair, H.graph_link, H.dataPair_generic hr,
      H.pair_mem_typedCross a b hab]
  · constructor
    · intro hp
      exact False.elim (hc ((RootData.dataLinkGraph H.graph r).uniform _ hp))
    · intro hp
      exact False.elim (hc (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp hp).1).2)

theorem genericLink_polynomial_eq {r : Root} (hr : IsGeneric r) (w : D → ℝ) :
    (RootData.dataLinkGraph H.graph r).edgePolynomial w =
      elementary Finset.univ (RootData.typeMass H.type w) 2 := by
  rw [RGraph.edgePolynomial, H.genericLink_edges_eq hr]
  exact (RootData.typedPartition H.type).crossWeight_eq w

theorem one_root_polynomial_eq (h : RootedLegal H.graph (sumRooting D))
    (z : Root → ℝ) (w : D → ℝ) :
    (∑ r, z r * (RootData.dataLinkGraph H.graph r).edgePolynomial w) =
      RootData.typedQuadratic z (RootData.typeMass H.type w) -
        actualEnergy (G := H.graph) (μ := sumRooting D) z (RootData.dataWeights w) / 2 := by
  have ht (d : D) : Declared H.graph (sumRooting D) (H.type d) (Sum.inr d) :=
    (H.graph_declared _ _).mpr rfl
  have hpos (b : Block) : (∑ d, if sign b (H.type d) = 1 then w d else 0) =
      RootData.positiveTypeMass b (RootData.typeMass H.type w) :=
    (H.positive_mass_eq b w).symm.trans (RootData.positiveMass_eq H.graph h H.type ht b w)
  have hneg (b : Block) : (∑ d, if sign b (H.type d) = -1 then w d else 0) =
      RootData.negativeTypeMass b (RootData.typeMass H.type w) :=
    (H.negative_mass_eq b w).symm.trans (RootData.negativeMass_eq H.graph h H.type ht b w)
  rw [sum_roots_of_passive_zero
    (fun r => z r * (RootData.dataLinkGraph H.graph r).edgePolynomial w)
    (by intro r hr; rw [RootData.dataLink_passive_zero H.graph h r hr w, mul_zero])]
  have hgeneric (j : Fin N) :
      (RootData.dataLinkGraph H.graph (genericRoot j)).edgePolynomial w =
        elementary Finset.univ (RootData.typeMass H.type w) 2 :=
    H.genericLink_polynomial_eq (genericRoot_isGeneric j) w
  simp_rw [H.dataLink_layer_polynomial_eq h, hpos, hneg, hgeneric]
  rw [H.actualEnergy_eq_layerEnergy h]
  unfold RootData.typedQuadratic
  simp only [mul_div, mul_sub, sub_div, Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_mul]
  ring

/-- The exact polynomial of the ordinary lower template. -/
theorem graph_edgePolynomial_eq (h : RootedLegal H.graph (sumRooting D))
    (z : Root → ℝ) (w : D → ℝ) :
    H.graph.edgePolynomial (Sum.elim z w) = elementary Finset.univ z 3 +
      (∑ ν : PhysicalType, RootData.typeMass H.type w ν * pairWeight (allowedPairs ν) z) +
      RootData.typedQuadratic z (RootData.typeMass H.type w) + markerWeight z * w H.mark -
      actualEnergy (G := H.graph) (μ := sumRooting D) z (RootData.dataWeights w) / 2 := by
  rw [RootData.complete_polynomial_links H.graph h H.graph_root_triple,
    H.two_root_polynomial_eq, H.one_root_polynomial_eq h]
  ring

theorem graph_edgePolynomial_eq_layerEnergy (h : RootedLegal H.graph (sumRooting D))
    (z : Root → ℝ) (w : D → ℝ) :
    H.graph.edgePolynomial (Sum.elim z w) = elementary Finset.univ z 3 +
      (∑ ν : PhysicalType, RootData.typeMass H.type w ν * pairWeight (allowedPairs ν) z) +
      RootData.typedQuadratic z (RootData.typeMass H.type w) + markerWeight z * w H.mark -
      (∑ r : Layer, z (layerRoot r) * H.layerEnergy r.1 w) / 2 := by
  rw [H.graph_edgePolynomial_eq h, H.actualEnergy_eq_layerEnergy h]

end TranscendentalTuran.Green.Realization.TypedData
