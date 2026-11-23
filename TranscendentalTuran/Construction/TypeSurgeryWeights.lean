module

public import TranscendentalTuran.Construction.TypeSurgeryLegality
public import TranscendentalTuran.Construction.IncidentPairs

@[expose] public section

namespace TranscendentalTuran.Source.TypeSurgery

open TuranUniversality TuranUniversality.Weighted Encoding Network RootData
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

noncomputable section

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The mass already carrying a given physical declaration. Undeclared
vertices do not contribute to any of these seven disjoint masses. -/
noncomputable def declaredMass (G : RGraph (Root ⊕ D) 3) (w : D → ℝ) (τ : PhysicalType) : ℝ := by
  classical
  exact ∑ d ∈ Finset.univ.filter (fun d => Declared G (sumRooting D) τ (Sum.inr d)), w d

noncomputable def deletedPairs (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType) (r : Root) :
    Finset (Finset D) := by
  classical
  exact ((model G).dataLink r).filter (fun p => ¬ Keep G a τ r p)

noncomputable def deletedWeight (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)
    (r : Root) (w : D → ℝ) : ℝ := ∑ p ∈ deletedPairs G a τ r, ∏ d ∈ p, w d

theorem deleted_contains (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType) (r : Root)
    {p : Finset D} (hp : p ∈ deletedPairs G a τ r) : a ∈ p := by
  classical
  have hn := (Finset.mem_filter.mp hp).2
  by_contra ha
  exact hn (Or.inl ha)

theorem deletedWeight_nonneg (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)
    (r : Root) (w : D → ℝ) (hw : ∀ d, 0 ≤ w d) : 0 ≤ deletedWeight G a τ r w :=
  Finset.sum_nonneg (fun p _ => Finset.prod_nonneg (fun d _ => hw d))

theorem deletedWeight_le_mass (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)
    (r : Root) (w : D → ℝ) (hw : ∀ d, 0 ≤ w d) :
    deletedWeight G a τ r w ≤ w a * ∑ d, w d := by
  classical
  apply incident_pairs_weight_le _ a Finset.univ
  · intro p hp
    exact (model G).dataLink_uniform r p (Finset.mem_filter.mp hp).1
  · exact fun p hp => deleted_contains G a τ r hp
  · exact fun _ _ _ _ _ => Finset.mem_univ _
  · exact hw

theorem deletedWeight_generic_le (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)
    (r : Root) (hr : IsGeneric r) (w : D → ℝ) (hw : ∀ d, 0 ≤ w d) :
    deletedWeight G a τ r w ≤ w a * declaredMass G w τ := by
  classical
  apply incident_pairs_weight_le _ a (Finset.univ.filter (fun d => Declared G (sumRooting D) τ (Sum.inr d)))
  · intro p hp
    exact (model G).dataLink_uniform r p (Finset.mem_filter.mp hp).1
  · exact fun p hp => deleted_contains G a τ r hp
  · intro p hp d hd hda
    have ha := deleted_contains G a τ r hp
    have hpair := pair_eq_of_mem p ((model G).dataLink_uniform r p (Finset.mem_filter.mp hp).1)
      ha hd (Ne.symm hda)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hn
    apply (Finset.mem_filter.mp hp).2
    refine Or.inr ⟨hr, ?_⟩
    intro e he hea
    have hed : e = d := by
      rw [hpair] at he
      exact Finset.mem_singleton.mp ((Finset.mem_insert.mp he).resolve_left hea)
    simpa only [hed] using hn
  · exact hw

theorem dataLink_deletion (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)
    (r : Root) (w : D → ℝ) :
    (dataLinkGraph (graph G a τ) r).edgePolynomial w + deletedWeight G a τ r w =
      (dataLinkGraph G r).edgePolynomial w := by
  classical
  change (∑ p ∈ (model (graph G a τ)).dataLink r, ∏ d ∈ p, w d) +
    (∑ p ∈ deletedPairs G a τ r, ∏ d ∈ p, w d) = _
  rw [dataLink_filtered]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

theorem deletedWeight_passive_zero (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (a : D) (τ : PhysicalType)
    (r : Root) (hr : IsPassive r) (w : D → ℝ) : deletedWeight G a τ r w = 0 := by
  classical
  have hempty : (model G).dataLink r = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨p, hp⟩
    obtain ⟨x, y, _, rfl⟩ := Finset.card_eq_two.mp ((model G).dataLink_uniform r p hp)
    exact hG.passive_empty r hr _ _ ((dataLinkGraph_mem_pair G r x y).mp hp)
  simp only [deletedWeight, deletedPairs, hempty, Finset.filter_empty, Finset.sum_empty]

theorem total_deletedWeight_le (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (a : D) (τ : PhysicalType)
    (z : Root → ℝ) (w : D → ℝ) (hz : ∀ r, 0 ≤ z r) (hw : ∀ d, 0 ≤ w d) :
    (∑ r, z r * deletedWeight G a τ r w) ≤ w a *
      ((∑ r : Layer, z (layerRoot r)) * (∑ d, w d) +
       (∑ j : Fin Parameters.N, z (genericRoot j)) * declaredMass G w τ) := by
  rw [sum_roots_of_passive_zero (fun r => z r * deletedWeight G a τ r w)
    (fun r hr => by rw [deletedWeight_passive_zero G hG a τ r hr w, mul_zero])]
  have hs : (∑ r : Layer, z (layerRoot r) * deletedWeight G a τ (layerRoot r) w) ≤
      ∑ r : Layer, z (layerRoot r) * (w a * ∑ d, w d) := by
    apply Finset.sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_left (deletedWeight_le_mass G a τ _ w hw) (hz _)
  have hg : (∑ j : Fin Parameters.N, z (genericRoot j) * deletedWeight G a τ (genericRoot j) w) ≤
      ∑ j : Fin Parameters.N, z (genericRoot j) * (w a * declaredMass G w τ) := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (deletedWeight_generic_le G a τ _ (genericRoot_isGeneric j) w hw) (hz _)
  calc
    _ ≤ (∑ r : Layer, z (layerRoot r) * (w a * ∑ d, w d)) +
        ∑ j : Fin Parameters.N, z (genericRoot j) * (w a * declaredMass G w τ) := add_le_add hs hg
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

theorem undeclared_typePairs_disjoint (G : RGraph (Root ⊕ D) 3) (a : D)
    (hu : Undeclared G a) (τ : PhysicalType) :
    Disjoint ((model G).rootLink a) (typePairs (physicalIndex τ)) := by
  apply Finset.disjoint_left.mpr
  intro p hp ht
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
  apply hu τ
  refine ⟨sumRooting_inr_data a, Or.inl ⟨j, ?_⟩⟩
  apply (rootLinkGraph_mem_pair G _ _ a).mp
  change {declaringRoot ((physicalIndex τ, j), 0), declaringRoot ((physicalIndex τ, j), 1)} ∈
    (model G).rootLink a
  rw [← declaringPair_eq]
  exact hp

theorem rootLink_addition (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)
    (hu : Undeclared G a) (z : Root → ℝ) (d : D) :
    (rootLinkGraph (graph G a τ) d).edgePolynomial z =
      (rootLinkGraph G d).edgePolynomial z + if d = a then declaringWeight z (physicalIndex τ) else 0 := by
  classical
  change (∑ p ∈ (model (graph G a τ)).rootLink d, ∏ r ∈ p, z r) = _
  rw [rootLink_unchanged]
  by_cases hd : d = a
  · subst d
    simp only [ite_true]
    rw [Finset.sum_union (undeclared_typePairs_disjoint G a hu τ)]
    exact congrArg ((rootLinkGraph G a).edgePolynomial z + ·) (typePairs_weight z (physicalIndex τ))
  · simp only [hd, ite_false, Finset.union_empty, add_zero]
    rfl

/-- A single declaration has the exact advertised root-pair gain and
loses at most the incident special links and same-type generic links. -/
theorem polynomial_gain (G : RGraph (Root ⊕ D) 3) (hG : Completed G) (a : D)
    (hu : Undeclared G a) (τ : PhysicalType) (z : Root → ℝ) (w : D → ℝ)
    (hz : ∀ r, 0 ≤ z r) (hw : ∀ d, 0 ≤ w d) :
    G.edgePolynomial (Sum.elim z w) + w a *
      (declaringWeight z (physicalIndex τ) -
        (∑ r : Layer, z (layerRoot r)) * (∑ d, w d) -
        (∑ j : Fin Parameters.N, z (genericRoot j)) * declaredMass G w τ) ≤
      (graph G a τ).edgePolynomial (Sum.elim z w) := by
  classical
  have hnew := completed G a τ hG hu
  have hsplit := complete_polynomial_links G hG.legal hG.root_clique z w
  have hsplit' := complete_polynomial_links (graph G a τ) hnew.legal hnew.root_clique z w
  have hroot : (∑ d, w d * (rootLinkGraph (graph G a τ) d).edgePolynomial z) =
      (∑ d, w d * (rootLinkGraph G d).edgePolynomial z) + w a * declaringWeight z (physicalIndex τ) := by
    simp_rw [rootLink_addition G a τ hu z, mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hlink : (∑ r, z r * (dataLinkGraph (graph G a τ) r).edgePolynomial w) +
      (∑ r, z r * deletedWeight G a τ r w) = ∑ r, z r * (dataLinkGraph G r).edgePolynomial w := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [← mul_add, dataLink_deletion]
  have hcost := total_deletedWeight_le G hG.legal a τ z w hz hw
  rw [hroot] at hsplit'
  nlinarith

end
end TranscendentalTuran.Source.TypeSurgery
