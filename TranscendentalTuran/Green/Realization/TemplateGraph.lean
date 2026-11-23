/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.TemplateCore
public import TranscendentalTuran.Construction.RootPairWeights
public import TranscendentalTuran.Construction.TotalRooting
public import TuranUniversality.Weighted.LinkModel
public import Mathlib.Data.Set.Insert

@[expose] public section

noncomputable section

namespace TranscendentalTuran.Green.Realization

open Network Encoding Parameters TuranUniversality Source

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

/-- The finite unordered pairs supplied by a symmetric irreflexive relation. -/
def pairSet {D : Type*} [Fintype D] [DecidableEq D] (R : D → D → Prop) : Finset (Finset D) := by
  classical
  exact Finset.univ.filter fun p => ∃ x y, p = {x, y} ∧ R x y

theorem pairSet_uniform {D : Type*} [Fintype D] [DecidableEq D] (R : D → D → Prop)
    (hi : ∀ x, ¬ R x x) {p : Finset D} (hp : p ∈ pairSet R) : p.card = 2 := by
  classical
  obtain ⟨x, y, rfl, hR⟩ := (Finset.mem_filter.mp hp).2
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hi x hR
  simp [hxy]

theorem pair_mem_pairSet {D : Type*} [Fintype D] [DecidableEq D] (R : D → D → Prop)
    (hs : ∀ x y, R x y ↔ R y x) (x y : D) : {x, y} ∈ pairSet R ↔ R x y := by
  classical
  constructor
  · intro h
    obtain ⟨a, b, he, hab⟩ := (Finset.mem_filter.mp h).2
    have he' : ({x, y} : Set D) = {a, b} := by
      simpa using congrArg (fun p : Finset D => (p : Set D)) he
    rcases Set.pair_eq_pair_iff.mp he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab
    · exact (hs _ _).mp hab
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, y, rfl, h⟩

namespace TypedData

variable {D : Type*} [Fintype D] [DecidableEq D] (H : TypedData D)

/-- One-root links: full signed-star links at special roots and cross-type links
at generic roots. Passive roots have empty one-root links. -/
def DataPair (r : Root) (x y : D) : Prop :=
  match rootBlock r with
  | some b => H.LayerPair b x y
  | none => IsGeneric r ∧ H.type x ≠ H.type y

theorem dataPair_symm (r : Root) (x y : D) : H.DataPair r x y ↔ H.DataPair r y x := by
  unfold DataPair
  cases rootBlock r with
  | none => exact and_congr Iff.rfl ne_comm
  | some b => exact H.layerPair_symm b x y

theorem dataPair_irrefl (r : Root) (x : D) : ¬ H.DataPair r x x := by
  unfold DataPair
  cases rootBlock r with
  | none => exact fun h => h.2 rfl
  | some b => exact fun h => h.1 rfl

@[simp] theorem dataPair_layerRoot (r : Layer) (x y : D) :
    H.DataPair (layerRoot r) x y ↔ H.LayerPair r.1 x y := by
  simp [DataPair]

theorem dataPair_generic {r : Root} (hr : IsGeneric r) (x y : D) :
    H.DataPair r x y ↔ H.type x ≠ H.type y := by
  simp [DataPair, rootBlock_none_of_ge hr.1, hr]

theorem dataPair_passive {r : Root} (hr : IsPassive r) (x y : D) : ¬ H.DataPair r x y := by
  have hg : ¬ IsGeneric r := by unfold IsPassive at hr; unfold IsGeneric; omega
  have hn := rootBlock_none_of_ge (r := r) (show K ≤ r.val by unfold IsPassive at hr; omega)
  simp [DataPair, hn, hg]

/-- The actual four link families of the ordinary lower-bound graph. -/
def linkData : Weighted.LinkData Root D where
  rootTriples := Finset.univ.powersetCard 3
  rootLink x := allowedPairs (H.type x) ∪ if x = H.mark then {markerPair} else ∅
  dataLink r := pairSet (H.DataPair r)
  dataTriples := ∅
  rootTriples_uniform p hp := (Finset.mem_powersetCard.mp hp).2
  rootLink_uniform x p hp := by
    rcases Finset.mem_union.mp hp with hp | hp
    · exact allowedPairs_card_two _ hp
    · split_ifs at hp
      · have he : p = markerPair := Finset.mem_singleton.mp hp
        subst p
        exact markerPair_card
      · exact False.elim (Finset.notMem_empty _ hp)
  dataLink_uniform r _ hp := pairSet_uniform _ (H.dataPair_irrefl r) hp
  dataTriples_uniform _ hp := False.elim (Finset.notMem_empty _ hp)

/-- The lower realization is an ordinary finite simple three-uniform graph. -/
def graph : RGraph (Root ⊕ D) 3 := H.linkData.model.toRGraph

private theorem mem_toRGraph (M : Weighted.RootedModel Root D) (e : Finset (Root ⊕ D)) :
    e ∈ M.toRGraph.edges ↔ (e.toLeft, e.toRight) ∈ M.edges := by
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    simpa using hp
  · intro h
    exact Finset.mem_image.mpr ⟨(e.toLeft, e.toRight), h, Finset.toLeft_disjSum_toRight⟩

@[simp] theorem graph_link (r : Root) (x y : D) :
    Link H.graph (sumRooting D) r (Sum.inr x) (Sum.inr y) ↔ H.DataPair r x y := by
  rw [sumRooting_link]
  change {Sum.inl r, Sum.inr x, Sum.inr y} ∈ H.linkData.model.toRGraph.edges ↔ _
  rw [mem_toRGraph]
  have h : ({r}, {x, y}) ∈ H.linkData.model.edges ↔ {x, y} ∈ H.linkData.dataLink r := by
    rw [← Weighted.RootedModel.mem_dataLink, Weighted.LinkData.model_dataLink]
  simpa only [Finset.toLeft_insert_inl, Finset.toRight_insert_inl,
    Finset.toLeft_insert_inr, Finset.toRight_insert_inr,
    toLeft_singleton_data, toRight_singleton_data, Finset.insert_empty] using
      h.trans (pair_mem_pairSet _ (H.dataPair_symm r) x y)

@[simp] theorem graph_pairLink (r s : Root) (x : D) :
    PairLink H.graph (sumRooting D) r s (Sum.inr x) ↔
      {r, s} ∈ allowedPairs (H.type x) ∪ if x = H.mark then {markerPair} else ∅ := by
  rw [sumRooting_pairLink]
  change {Sum.inl r, Sum.inl s, Sum.inr x} ∈ H.linkData.model.toRGraph.edges ↔ _
  rw [mem_toRGraph]
  have h : ({r, s}, {x}) ∈ H.linkData.model.edges ↔ {r, s} ∈ H.linkData.rootLink x := by
    rw [← Weighted.RootedModel.mem_rootLink, Weighted.LinkData.model_rootLink]
  change ({r, s}, {x}) ∈ H.linkData.model.edges ↔
    {r, s} ∈ allowedPairs (H.type x) ∪ (if x = H.mark then {markerPair} else ∅) at h
  simpa only [Finset.toLeft_insert_inl, Finset.toRight_insert_inl,
    toLeft_singleton_data, toRight_singleton_data, Finset.insert_empty] using h

@[simp] theorem graph_marked (x : D) :
    Marked H.graph (sumRooting D) (Sum.inr x) ↔ x = H.mark := by
  unfold Marked
  rw [H.graph_pairLink]
  change markerPair ∈ allowedPairs (H.type x) ∪ (if x = H.mark then {markerPair} else ∅) ↔ _
  by_cases hm : x = H.mark <;> simp [hm, markerPair_not_allowedPairs]

private theorem declaringPair_eq_pair (p : PairIndex) :
    declaringPair p = {declaringRoot (p, 0), declaringRoot (p, 1)} := by
  ext r
  simp [mem_declaringPair, Fin.exists_fin_two, eq_comm]

@[simp] theorem graph_declared (τ : PhysicalType) (x : D) :
    Declared H.graph (sumRooting D) τ (Sum.inr x) ↔ τ = H.type x := by
  unfold Declared
  simp only [sumRooting_inr_data, true_and, H.graph_pairLink, H.graph_marked]
  have hdecl : ∀ j : Fin N,
      {declaringRoot ((physicalIndex τ, j), 0), declaringRoot ((physicalIndex τ, j), 1)} ∈
        allowedPairs (H.type x) ∪ (if x = H.mark then {markerPair} else ∅) ↔ τ = H.type x := by
    intro j
    rw [← declaringPair_eq_pair]
    by_cases hm : x = H.mark <;>
      simp [hm, declaringPair_mem_allowedPairs, (markerPair_ne_declaringPair _).symm]
  simp_rw [hdecl]
  constructor
  · rintro (⟨_, h⟩ | ⟨rfl, rfl⟩)
    · exact h
    · exact H.mark_base.symm
  · intro h
    exact Or.inl ⟨⟨0, N_pos⟩, h⟩

end TypedData
end TranscendentalTuran.Green.Realization
