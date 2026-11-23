module

public import TranscendentalTuran.Construction.TotalRooting
public import TranscendentalTuran.Network.LayerLinks
public import TuranUniversality.Weighted.Model

@[expose] public section

namespace TranscendentalTuran.Source.RootData

open TuranUniversality TuranUniversality.Weighted Encoding Network
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [DecidableEq D]

def model (G : RGraph (Root ⊕ D) 3) : RootedModel Root D := RootedModel.ofRGraph G

theorem mem_model (G : RGraph (Root ⊕ D) 3) (p : Finset Root) (s : Finset D) :
    (p, s) ∈ (model G).edges ↔ p.disjSum s ∈ G.edges := by
  constructor
  · intro h
    obtain ⟨e, he, hh⟩ := Finset.mem_image.mp h
    have hp := congrArg Prod.fst hh
    have hs := congrArg Prod.snd hh
    change e.toLeft = p at hp
    change e.toRight = s at hs
    rw [← hp, ← hs, Finset.toLeft_disjSum_toRight]
    exact he
  · intro h
    exact Finset.mem_image.mpr ⟨p.disjSum s, h, by simp⟩

def rootLinkGraph (G : RGraph (Root ⊕ D) 3) (d : D) : RGraph Root 2 :=
  ⟨(model G).rootLink d, (model G).rootLink_uniform d⟩

def dataLinkGraph (G : RGraph (Root ⊕ D) 3) (r : Root) : RGraph D 2 :=
  ⟨(model G).dataLink r, (model G).dataLink_uniform r⟩

theorem rootLinkGraph_mem_pair (G : RGraph (Root ⊕ D) 3) (r s : Root) (d : D) :
    {r, s} ∈ (rootLinkGraph G d).edges ↔ PairLink G (sumRooting D) r s (Sum.inr d) := by
  rw [rootLinkGraph, (model G).mem_rootLink, mem_model, sumRooting_pairLink]
  have he : ({r, s} : Finset Root).disjSum {d} = {Sum.inl r, Sum.inl s, Sum.inr d} := by
    ext (a | b) <;> simp
  rw [he]

theorem dataLinkGraph_mem_pair (G : RGraph (Root ⊕ D) 3) (r : Root) (a b : D) :
    {a, b} ∈ (dataLinkGraph G r).edges ↔ Link G (sumRooting D) r (Sum.inr a) (Sum.inr b) := by
  rw [dataLinkGraph, (model G).mem_dataLink, mem_model, sumRooting_link]
  have he : ({r} : Finset Root).disjSum {a, b} = {Sum.inl r, Sum.inr a, Sum.inr b} := by
    ext (c | d) <;> simp
  rw [he]

theorem dataTriples_empty (G : RGraph (Root ⊕ D) 3) (hG : RootedLegal G (sumRooting D)) :
    (model G).dataTriples = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨p, hp⟩
  have he := (mem_model G ∅ p).mp ((model G).mem_dataTriples p |>.mp hp)
  obtain ⟨v, hv, hr⟩ := hG.covers_edges _ he
  cases v with
  | inl r => simpa using hv
  | inr d => exact sumRooting_inr_data d hr

theorem rootTriples_complete (G : RGraph (Root ⊕ D) 3)
    (hroot : ∀ p : Finset Root, p.card = 3 → p.image Sum.inl ∈ G.edges) :
    (model G).rootTriples = Finset.univ.powersetCard 3 := by
  ext p
  constructor
  · intro hp
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (model G).rootTriples_uniform p hp⟩
  · intro hp
    apply ((model G).mem_rootTriples p).mpr
    apply (mem_model G p ∅).mpr
    rw [Finset.disjSum_empty, Finset.map_eq_image]
    change p.image Sum.inl ∈ G.edges
    exact hroot p (Finset.mem_powersetCard.mp hp).2

theorem complete_polynomial_links [Fintype D] (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D))
    (hroot : ∀ p : Finset Root, p.card = 3 → p.image Sum.inl ∈ G.edges)
    (z : Root → ℝ) (w : D → ℝ) :
    G.edgePolynomial (Sum.elim z w) = elementary Finset.univ z 3 +
      (∑ d, w d * (rootLinkGraph G d).edgePolynomial z) +
      ∑ r, z r * (dataLinkGraph G r).edgePolynomial w := by
  have hh := (model G).edgePolynomial_links z w
  rw [dataTriples_empty G hG, rootTriples_complete G hroot] at hh
  simpa only [model, rootLinkGraph, dataLinkGraph, RootedModel.toRGraph_ofRGraph, RGraph.edgePolynomial,
    elementary, Finset.sum_empty, add_zero] using hh

theorem polynomial_links_bound [Fintype D] (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (z : Root → ℝ) (w : D → ℝ)
    (hz : ∀ r, 0 ≤ z r) :
    G.edgePolynomial (Sum.elim z w) ≤ elementary Finset.univ z 3 +
      (∑ d, w d * (rootLinkGraph G d).edgePolynomial z) +
      ∑ r, z r * (dataLinkGraph G r).edgePolynomial w := by
  have hsplit := (model G).edgePolynomial_four_shapes z w
  have hthree := (model G).contribution_three_le_complete z w hz
  rw [(model G).contribution_two_eq, (model G).contribution_one_eq,
    (model G).contribution_zero_eq, dataTriples_empty G hG, Finset.sum_empty, add_zero] at hsplit
  have hgraph : (model G).toRGraph = G := RootedModel.toRGraph_ofRGraph G
  rw [hgraph] at hsplit
  change G.edgePolynomial (Sum.elim z w) = (model G).contribution 3 z w +
    (∑ d, w d * (rootLinkGraph G d).edgePolynomial z) +
    ∑ r, z r * (dataLinkGraph G r).edgePolynomial w at hsplit
  linarith

def dataWeights (w : D → ℝ) : Root ⊕ D → ℝ := Sum.elim (fun _ => 0) w

theorem dataLinkGraph_eq_pullback [Fintype D] (G : RGraph (Root ⊕ D) 3) (r : Root) :
    dataLinkGraph G r = (Source.dataPairGraph (G := G) (μ := sumRooting D) r).pullback
      (Function.Embedding.inr : D ↪ Root ⊕ D) := by
  classical
  apply RGraph.ext
  ext p
  by_cases hc : p.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
    rw [dataLinkGraph_mem_pair, RGraph.mem_pullback]
    simp only [Finset.card_pair hab, Finset.map_eq_image, Finset.image_insert,
      Finset.image_singleton, Function.Embedding.inr_apply, true_and,
      Source.dataPairGraph_mem_pair]
  · constructor
    · intro hp
      exact False.elim (hc ((dataLinkGraph G r).uniform _ hp))
    · intro hp
      exact False.elim (hc (((Source.dataPairGraph (G := G) (μ := sumRooting D) r).pullback
        (Function.Embedding.inr : D ↪ Root ⊕ D)).uniform _ hp))

theorem dataLink_polynomial_eq [Fintype D] (G : RGraph (Root ⊕ D) 3) (r : Root) (w : D → ℝ) :
    (dataLinkGraph G r).edgePolynomial w =
      (Source.dataPairGraph (G := G) (μ := sumRooting D) r).edgePolynomial (dataWeights w) := by
  rw [dataLinkGraph_eq_pullback]
  have hh := (Source.dataPairGraph (G := G) (μ := sumRooting D) r).edgePolynomial_pullback
    (Function.Embedding.inr : D ↪ Root ⊕ D) (dataWeights w) (by
      intro v hv
      cases v with
      | inl r => rfl
      | inr d => exact False.elim (hv ⟨d, rfl⟩))
  simpa only [dataWeights, Function.comp_def, Function.Embedding.inr_apply, Sum.elim_inr] using hh

theorem dataLink_layer_bound [Fintype D] (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D))
    (ht : ∀ x, Data (sumRooting D) x → ∃ τ, Declared G (sumRooting D) τ x)
    (r : Layer) (w : D → ℝ) (hw : ∀ d, 0 ≤ w d) :
    (dataLinkGraph G (layerRoot r)).edgePolynomial w ≤
      ((∑ c : PositiveVertex G (sumRooting D) r.1, dataWeights w c.val) ^ 2 +
        (∑ l : NegativeVertex G (sumRooting D) r.1, dataWeights w l.val) ^ 2 -
          actualLayerEnergy (G := G) (μ := sumRooting D) r (dataWeights w)) / 2 := by
  rw [dataLink_polynomial_eq]
  exact actualLink_polynomial_bound hG ht r (dataWeights w)
    (fun x => by cases x with | inl r => exact le_rfl | inr d => exact hw d)

theorem dataLink_passive_zero [Fintype D] (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (r : Root) (hr : IsPassive r) (w : D → ℝ) :
    (dataLinkGraph G r).edgePolynomial w = 0 := by
  have he : (dataLinkGraph G r).edges = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨p, hp⟩
    obtain ⟨a, b, _hab, rfl⟩ := Finset.card_eq_two.mp ((dataLinkGraph G r).uniform _ hp)
    exact hG.passive_empty r hr _ _ ((dataLinkGraph_mem_pair G r a b).mp hp)
  simp only [RGraph.edgePolynomial, he, Finset.sum_empty]

end TranscendentalTuran.Source.RootData
