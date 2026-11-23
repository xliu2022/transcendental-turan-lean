module

public import TranscendentalTuran.Construction.CompletedPolynomial
public import TranscendentalTuran.Construction.RootPartition
public import TuranUniversality.Weighted.LinkModel

@[expose] public section

namespace TranscendentalTuran.Source.TypeSurgery

open TuranUniversality TuranUniversality.Weighted Encoding Network RootData
open Classical

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

noncomputable section

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable def Undeclared (G : RGraph (Root ⊕ D) 3) (a : D) : Prop :=
  ∀ τ, ¬ Declared G (sumRooting D) τ (Sum.inr a)

/-- Keep every pair not incident with the vertex being declared. At that
vertex, keep only generic links to vertices not already of the new type. -/
noncomputable def Keep (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)
    (r : Root) (p : Finset D) : Prop :=
  a ∉ p ∨ (IsGeneric r ∧ ∀ d ∈ p, d ≠ a → ¬ Declared G (sumRooting D) τ (Sum.inr d))

noncomputable def linkData (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType) : LinkData Root D := by
  classical
  exact
    { rootTriples := (model G).rootTriples
      rootLink := fun d => (model G).rootLink d ∪ if d = a then typePairs (physicalIndex τ) else ∅
      dataLink := fun r => ((model G).dataLink r).filter (Keep G a τ r)
      dataTriples := (model G).dataTriples
      rootTriples_uniform := (model G).rootTriples_uniform
      rootLink_uniform := by
        intro d p hp
        rcases Finset.mem_union.mp hp with hp | hp
        · exact (model G).rootLink_uniform d p hp
        · split_ifs at hp
          · exact typePairs_card_two _ hp
          · exact False.elim (Finset.notMem_empty _ hp)
      dataLink_uniform := fun r p hp => (model G).dataLink_uniform r p (Finset.mem_filter.mp hp).1
      dataTriples_uniform := (model G).dataTriples_uniform }

noncomputable def graph (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType) : RGraph (Root ⊕ D) 3 :=
  (linkData G a τ).model.toRGraph

theorem mem_toRGraph (M : RootedModel Root D) (e : Finset (Root ⊕ D)) :
    e ∈ M.toRGraph.edges ↔ (e.toLeft, e.toRight) ∈ M.edges := by
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    simpa using hp
  · intro h
    exact Finset.mem_image.mpr ⟨(e.toLeft, e.toRight), h, Finset.toLeft_disjSum_toRight⟩

theorem model_toRGraph (M : RootedModel Root D) : model M.toRGraph = M := by
  have he : (model M.toRGraph).edges = M.edges := by
    ext p
    rw [mem_model, mem_toRGraph]
    simp
  have hext (A B : RootedModel Root D) (h : A.edges = B.edges) : A = B := by
    cases A
    cases B
    cases h
    rfl
  exact hext _ _ he

theorem model_graph (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType) :
    model (graph G a τ) = (linkData G a τ).model := model_toRGraph _

@[simp] theorem graph_link (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)
    (r : Root) (x y : D) :
    Link (graph G a τ) (sumRooting D) r (Sum.inr x) (Sum.inr y) ↔
      Link G (sumRooting D) r (Sum.inr x) (Sum.inr y) ∧ Keep G a τ r {x, y} := by
  rw [← dataLinkGraph_mem_pair (graph G a τ) r x y]
  change {x, y} ∈ (model (graph G a τ)).dataLink r ↔ _
  rw [model_graph G a τ, LinkData.model_dataLink]
  change {x, y} ∈ ((model G).dataLink r).filter (Keep G a τ r) ↔ _
  rw [Finset.mem_filter]
  exact and_congr (dataLinkGraph_mem_pair G r x y) Iff.rfl

@[simp] theorem graph_pairLink (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)
    (r s : Root) (d : D) :
    PairLink (graph G a τ) (sumRooting D) r s (Sum.inr d) ↔
      PairLink G (sumRooting D) r s (Sum.inr d) ∨
        (d = a ∧ {r, s} ∈ typePairs (physicalIndex τ)) := by
  classical
  rw [← rootLinkGraph_mem_pair (graph G a τ) r s d]
  change {r, s} ∈ (model (graph G a τ)).rootLink d ↔ _
  rw [model_graph G a τ, LinkData.model_rootLink]
  change {r, s} ∈ (model G).rootLink d ∪ (if d = a then typePairs (physicalIndex τ) else ∅) ↔ _
  rw [Finset.mem_union]
  change {r, s} ∈ (rootLinkGraph G d).edges ∨ _ ↔ _
  rw [rootLinkGraph_mem_pair G r s d]
  by_cases hd : d = a <;> simp [hd]

theorem markerPair_not_typePairs (ν : Fin 7) : markerPair ∉ typePairs ν := by
  intro h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
  exact markerPair_ne_declaringPair _ hj.symm

@[simp] theorem graph_marked (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType) (d : D) :
    Marked (graph G a τ) (sumRooting D) (Sum.inr d) ↔ Marked G (sumRooting D) (Sum.inr d) := by
  unfold Marked
  rw [graph_pairLink]
  change PairLink G (sumRooting D) markerLeft markerRight (Sum.inr d) ∨
      (d = a ∧ markerPair ∈ typePairs (physicalIndex τ)) ↔ _
  simp only [markerPair_not_typePairs, and_false, or_false]

theorem declaringPair_mem_typePairs (σ τ : PhysicalType) (j : Fin Parameters.N) :
    declaringPair (physicalIndex σ, j) ∈ typePairs (physicalIndex τ) ↔ σ = τ := by
  constructor
  · intro h
    exact (declaringPair_mem_allowedPairs σ τ j).mp (Finset.mem_union_right _ h)
  · rintro rfl
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

@[simp] theorem graph_declared (G : RGraph (Root ⊕ D) 3) (a : D) (τ σ : PhysicalType) (d : D) :
    Declared (graph G a τ) (sumRooting D) σ (Sum.inr d) ↔
      Declared G (sumRooting D) σ (Sum.inr d) ∨ (d = a ∧ σ = τ) := by
  constructor
  · rintro ⟨_, h | h⟩
    · obtain ⟨j, hj⟩ := h
      rcases (graph_pairLink G a τ _ _ d).mp hj with hold | ⟨hd, hp⟩
      · exact Or.inl ⟨sumRooting_inr_data d, Or.inl ⟨j, hold⟩⟩
      · exact Or.inr ⟨hd, (declaringPair_mem_typePairs σ τ j).mp
          (by simpa only [declaringPair_eq] using hp)⟩
    · exact Or.inl ⟨sumRooting_inr_data d, Or.inr ⟨h.1, (graph_marked G a τ d).mp h.2⟩⟩
  · rintro (⟨_, h | h⟩ | ⟨hd, hσ⟩)
    · obtain ⟨j, hj⟩ := h
      exact ⟨sumRooting_inr_data d, Or.inl ⟨j, (graph_pairLink G a τ _ _ d).mpr (Or.inl hj)⟩⟩
    · exact ⟨sumRooting_inr_data d, Or.inr ⟨h.1, (graph_marked G a τ d).mpr h.2⟩⟩
    · subst d
      subst σ
      let j : Fin Parameters.N := ⟨0, Parameters.N_pos⟩
      refine ⟨sumRooting_inr_data a, Or.inl ⟨j, ?_⟩⟩
      apply (graph_pairLink G a τ _ _ a).mpr
      exact Or.inr ⟨rfl, by
        rw [← declaringPair_eq]
        exact (declaringPair_mem_typePairs τ τ j).mpr rfl⟩

theorem link_old (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)
    {r : Root} {x y : Root ⊕ D}
    (h : Link (graph G a τ) (sumRooting D) r x y) : Link G (sumRooting D) r x y := by
  obtain ⟨d, rfl⟩ := sumRooting_data_exists h.1
  obtain ⟨e, rfl⟩ := sumRooting_data_exists h.2.1
  exact ((graph_link G a τ r d e).mp h).1

theorem special_link_ne (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)
    {r : Root} (hr : r.val < Parameters.K) {x y : Root ⊕ D}
    (h : Link (graph G a τ) (sumRooting D) r x y) :
    x ≠ Sum.inr a ∧ y ≠ Sum.inr a := by
  obtain ⟨d, rfl⟩ := sumRooting_data_exists h.1
  obtain ⟨e, rfl⟩ := sumRooting_data_exists h.2.1
  have hk := ((graph_link G a τ r d e).mp h).2
  have hnot : ¬ IsGeneric r := fun hg => by have := hg.1; omega
  have ha : a ∉ ({d, e} : Finset D) := hk.resolve_right (fun hh => hnot hh.1)
  constructor
  · intro hda
    have hd := Sum.inr.inj hda
    exact ha (by simp [hd])
  · intro hea
    have he := Sum.inr.inj hea
    exact ha (by simp [he])

theorem declared_old_of_ne (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)
    {σ : PhysicalType} {x : Root ⊕ D} (hx : x ≠ Sum.inr a)
    (h : Declared (graph G a τ) (sumRooting D) σ x) : Declared G (sumRooting D) σ x := by
  obtain ⟨d, rfl⟩ := sumRooting_data_exists h.1
  rcases (graph_declared G a τ σ d).mp h with hold | ⟨hd, _⟩
  · exact hold
  · exact False.elim (hx (congrArg Sum.inr hd))

theorem marked_old (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)
    {x : Root ⊕ D} (h : Marked (graph G a τ) (sumRooting D) x) : Marked G (sumRooting D) x := by
  obtain ⟨d, rfl⟩ := sumRooting_data_exists h.1
  exact (graph_marked G a τ d).mp h

theorem rootTriples_unchanged (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType) :
    (model (graph G a τ)).rootTriples = (model G).rootTriples := by
  rw [model_graph G a τ, LinkData.model_rootTriples]
  rfl

theorem dataTriples_unchanged (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType) :
    (model (graph G a τ)).dataTriples = (model G).dataTriples := by
  rw [model_graph G a τ, LinkData.model_dataTriples]
  rfl

theorem rootLink_unchanged (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType) (d : D) :
    (model (graph G a τ)).rootLink d =
      (model G).rootLink d ∪ if d = a then typePairs (physicalIndex τ) else ∅ := by
  rw [model_graph G a τ, LinkData.model_rootLink]
  rfl

theorem dataLink_filtered (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType) (r : Root) :
    (model (graph G a τ)).dataLink r = ((model G).dataLink r).filter (Keep G a τ r) := by
  rw [model_graph G a τ, LinkData.model_dataLink]
  rfl

end
end TranscendentalTuran.Source.TypeSurgery
