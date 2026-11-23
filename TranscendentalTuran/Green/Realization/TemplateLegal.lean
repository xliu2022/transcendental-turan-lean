/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.TemplateRelations

@[expose] public section

noncomputable section

namespace TranscendentalTuran.Green.Realization.TypedData

open Network Encoding Parameters TuranUniversality Source

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D] (H : TypedData D)

theorem graph_edge_has_root {e : Finset (Root ⊕ D)} (he : e ∈ H.graph.edges) :
    ∃ r : Root, Sum.inl r ∈ e := by
  obtain ⟨⟨p, q⟩, hp, rfl⟩ := Finset.mem_image.mp he
  have hn : p.Nonempty := by
    rcases (H.linkData.mem_model_edges p q).mp hp with h | ⟨x, _, h⟩ | ⟨r, h, _⟩ | h
    · exact Finset.card_pos.mp (by rw [H.linkData.rootTriples_uniform p h.2]; decide)
    · exact Finset.card_pos.mp (by rw [H.linkData.rootLink_uniform x p h]; decide)
    · rw [h]
      exact Finset.singleton_nonempty r
    · exact False.elim (Finset.notMem_empty _ h.2)
  obtain ⟨r, hr⟩ := hn
  exact ⟨r, by simpa using hr⟩

private theorem structural_data {r : Layer} {x y : Root ⊕ D}
    (h : StructuralAt H.graph (sumRooting D) r x y) :
    Data (sumRooting D) x ∧ Data (sumRooting D) y := by
  obtain ⟨τ, σ, hx, hy, _⟩ := h
  exact ⟨hx.1, hy.1⟩

theorem graph_structural {r : Layer} {x y : D}
    (h : StructuralAt H.graph (sumRooting D) r (Sum.inr x) (Sum.inr y)) :
    H.center r.1 y = some x ∨ H.center r.1 x = some y := by
  obtain ⟨τ, σ, hx, hy, _, _, hs, hl⟩ := h
  have hτ := (H.graph_declared τ x).mp hx
  have hσ := (H.graph_declared σ y).mp hy
  rw [hτ, hσ] at hs
  have hp := (H.dataPair_layerRoot r x y).mp ((H.graph_link _ x y).mp hl)
  exact H.layerPair_opposite hp hs

/-- The typed construction satisfies the actual ordinary rooting rules. All
structural relations in the conclusion are read from present triples. -/
theorem graph_rootedLegal (hL : H.Legal) : RootedLegal H.graph (sumRooting D) where
  covers_edges e he := by
    obtain ⟨r, hr⟩ := H.graph_edge_has_root he
    exact ⟨Sum.inl r, hr, (Rooting.mem_range _ _).mpr ⟨r, rfl⟩⟩
  passive_empty r hr x y hl := by
    obtain ⟨x, rfl⟩ := sumRooting_data_exists hl.1
    obtain ⟨y, rfl⟩ := sumRooting_data_exists hl.2.1
    exact H.dataPair_passive hr x y ((H.graph_link r x y).mp hl)
  declarations_unique x τ σ hx hy := by
    obtain ⟨x, rfl⟩ := sumRooting_data_exists hx.1
    exact ((H.graph_declared τ x).mp hx).trans ((H.graph_declared σ x).mp hy).symm
  generic_different r hr x y τ σ hx hy hl := by
    obtain ⟨x, rfl⟩ := sumRooting_data_exists hx.1
    obtain ⟨y, rfl⟩ := sumRooting_data_exists hy.1
    have hn := (H.dataPair_generic hr x y).mp ((H.graph_link r x y).mp hl)
    intro he
    apply hn
    rw [← (H.graph_declared τ x).mp hx, ← (H.graph_declared σ y).mp hy, he]
  special_allowed r x y τ σ hx hy hl := by
    obtain ⟨x, rfl⟩ := sumRooting_data_exists hx.1
    obtain ⟨y, rfl⟩ := sumRooting_data_exists hy.1
    have hp := (H.dataPair_layerRoot r x y).mp ((H.graph_link _ x y).mp hl)
    rw [(H.graph_declared τ x).mp hx, (H.graph_declared σ y).mp hy]
    refine ⟨hp.2.1, hp.2.2.1, ?_⟩
    rcases hp.2.2.2 with h | h | ⟨hs, _⟩
    · exact Or.inr (Or.inl (H.center_allowed _ _ _ h))
    · exact Or.inr (Or.inr (H.center_allowed _ _ _ h))
    · exact Or.inl hs
  matching_left b x y z h1 h2 := by
    cases x <;> cases y <;> cases z <;>
      simp_all only [graph_matching_root_left, graph_matching_root_right,
        graph_matching, Sum.inr.injEq, not_true_eq_false, false_implies]
    exact hL.matching_left _ _ _ _ h1 h2
  matching_right b x y z h1 h2 := by
    cases x <;> cases y <;> cases z <;>
      simp_all only [graph_matching_root_left, graph_matching_root_right,
        graph_matching, Sum.inr.injEq, not_true_eq_false, false_implies]
    exact Option.some.inj (h1.symm.trans h2)
  port_base_unique b c x y p hx hy h1 h2 := by
    obtain ⟨x, rfl⟩ := sumRooting_data_exists hx.1
    obtain ⟨y, rfl⟩ := sumRooting_data_exists hy.1
    have hp : Data (sumRooting D) p := by
      obtain ⟨_, σ, _, hp, _⟩ := h1
      exact hp.1
    obtain ⟨p, rfl⟩ := sumRooting_data_exists hp
    have hh := hL.port_base_unique b c x y p
      ((H.graph_declared .base x).mp hx).symm ((H.graph_declared .base y).mp hy).symm
      ((H.graph_matching b x p).mp h1) ((H.graph_matching c y p).mp h2)
    exact ⟨hh.1, congrArg Sum.inr hh.2⟩
  port_center_unique b c x y p hx hy h1 h2 := by
    cases x <;> cases y <;> cases p <;>
      simp_all only [IsCenter, graph_declared_root, graph_declared, graph_matching_root_left,
        graph_matching_root_right, graph_matching, Sum.inr.injEq, not_true_eq_false,
        false_or, false_implies]
    exact hL.port_center_unique _ _ _ _ _ (hx.imp Eq.symm Eq.symm)
      (hy.imp Eq.symm Eq.symm) h1 h2
  owner_functional b x a a' h1 h2 := by
    cases x <;> cases a <;> cases a' <;>
      simp_all only [graph_owner_root_left, graph_owner_root_right, graph_owner,
        Sum.inr.injEq, not_true_eq_false, false_implies]
    exact Option.some.inj (h1.symm.trans h2)
  same_component_forbidden r x y c hx hy hl := by
    obtain ⟨x, rfl⟩ := sumRooting_data_exists (H.structural_data hx).1
    obtain ⟨c, rfl⟩ := sumRooting_data_exists (H.structural_data hx).2
    obtain ⟨y, rfl⟩ := sumRooting_data_exists (H.structural_data hy).1
    exact H.no_pair_of_shared_neighbor (H.graph_structural hx) (H.graph_structural hy)
      ((H.dataPair_layerRoot r x y).mp ((H.graph_link _ x y).mp hl))
  marks_unique x y hx hy := by
    cases x <;> cases y <;>
      simp_all only [graph_marked_root, graph_marked, Sum.inr.injEq,
        not_true_eq_false, false_implies]
  E_preserves_vertical x y a b he ha hb := by
    cases x <;> cases y <;> cases a <;> cases b <;>
      simp_all only [graph_completeE_root_left, graph_completeE_root_right,
        graph_completeE, graph_owner_root_left, graph_owner_root_right, graph_owner,
        Sum.inr.injEq, not_true_eq_false, false_implies]
    exact hL.E_preserves_vertical _ _ _ _ he ha hb
  parentH_unique a b c ha hb := by
    cases a <;> cases b <;> cases c <;>
      simp_all only [graph_parentH_root_left, graph_parentH_root_right, graph_parentH,
        Sum.inr.injEq, not_true_eq_false, false_implies]
    exact hL.parentH_unique _ _ _ ha hb
  parentV_unique a b c ha hb := by
    cases a <;> cases b <;> cases c <;>
      simp_all only [graph_parentV_root_left, graph_parentV_root_right, graph_parentV,
        Sum.inr.injEq, not_true_eq_false, false_implies]
    exact hL.parentV_unique _ _ _ ha hb
  boundaryH m x y o hm hmo hxo := by
    cases m <;> cases x <;> cases y <;> cases o <;>
      simp_all only [graph_marked_root, graph_marked, graph_owner_root_left,
        graph_owner_root_right, graph_owner, graph_completeE_root_left,
        graph_completeE_root_right, graph_completeE, graph_completeD_root_left,
        graph_completeD_root_right, graph_completeD, not_true_eq_false,
        false_or, or_false, not_false_eq_true, false_implies]
    exact hL.boundaryH _ _ _ hmo hxo
  boundaryV m x y o hm hmo hxo := by
    cases m <;> cases x <;> cases y <;> cases o <;>
      simp_all only [graph_marked_root, graph_marked, graph_owner_root_left,
        graph_owner_root_right, graph_owner, graph_completeD_root_left,
        graph_completeD_root_right, graph_completeD, not_true_eq_false,
        not_false_eq_true, false_implies]
    exact hL.boundaryV _ _ _ hmo hxo

end TranscendentalTuran.Green.Realization.TypedData
