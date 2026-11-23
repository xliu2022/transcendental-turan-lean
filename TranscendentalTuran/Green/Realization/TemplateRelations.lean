/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.TemplateGraph

@[expose] public section

noncomputable section

namespace TranscendentalTuran.Green.Realization

open Network Encoding Parameters TuranUniversality Source

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

@[simp] theorem rootBlock_matchingRoot (b : Fin 4) (j : Fin M) :
    rootBlock (matchingRoot b j) = some (matchingBlock b) := by
  fin_cases b
  · exact rootBlock_layerRoot ⟨.match0, j⟩
  · exact rootBlock_layerRoot ⟨.match1, j⟩
  · exact rootBlock_layerRoot ⟨.match2, j⟩
  · exact rootBlock_layerRoot ⟨.match3, j⟩

@[simp] theorem rootBlock_ownershipRoot (b : Fin 2) (j : Fin κ) :
    rootBlock (ownershipRoot b j) = some (if b = 0 then .ownerH else .ownerV) := by
  fin_cases b
  · exact rootBlock_layerRoot ⟨.ownerH, j⟩
  · exact rootBlock_layerRoot ⟨.ownerV, j⟩

namespace TypedData

variable {D : Type*} [Fintype D] [DecidableEq D] (H : TypedData D)

theorem layerPair_allowed {b : Block} {x y : D}
    (ha : AllowedIncidence b (H.type x) (H.type y)) (hp : H.LayerPair b x y) :
    H.center b y = some x := by
  have hs := incidence_signs ha
  rcases hp.2.2.2 with h | h | ⟨he, _⟩
  · exact h
  · have hh := H.center_signs h
    omega
  · omega

@[simp] theorem graph_declared_root (τ : PhysicalType) (r : Root) :
    ¬ Declared H.graph (sumRooting D) τ (Sum.inl r) :=
  fun h => sumRooting_inl_not_data r h.1

@[simp] theorem graph_marked_root (r : Root) : ¬ Marked H.graph (sumRooting D) (Sum.inl r) :=
  fun h => sumRooting_inl_not_data r h.1

@[simp] theorem graph_matching (b : Fin 4) (x y : D) :
    MatchingEdge H.graph (sumRooting D) b (Sum.inr x) (Sum.inr y) ↔ H.Matching b x y := by
  constructor
  · rintro ⟨τ, σ, hx, hy, ha, j, hl⟩
    have hτ := (H.graph_declared τ x).mp hx
    have hσ := (H.graph_declared σ y).mp hy
    rw [hτ, hσ] at ha
    have hp : H.LayerPair (matchingBlock b) x y := by
      have hh := (H.graph_link (matchingRoot b j) x y).mp hl
      simpa only [DataPair, rootBlock_matchingRoot] using hh
    exact H.layerPair_allowed ha hp
  · intro h
    refine ⟨H.type x, H.type y, (H.graph_declared _ _).mpr rfl,
      (H.graph_declared _ _).mpr rfl, H.center_allowed _ _ _ h, ⟨0, M_pos⟩, ?_⟩
    apply (H.graph_link _ x y).mpr
    simpa only [DataPair, rootBlock_matchingRoot] using H.center_layerPair h

@[simp] theorem graph_matching_root_left (b : Fin 4) (r : Root) (v : Root ⊕ D) :
    ¬ MatchingEdge H.graph (sumRooting D) b (Sum.inl r) v := by
  rintro ⟨τ, _, h, _⟩
  exact H.graph_declared_root τ r h

@[simp] theorem graph_matching_root_right (b : Fin 4) (r : Root) (v : Root ⊕ D) :
    ¬ MatchingEdge H.graph (sumRooting D) b v (Sum.inl r) := by
  rintro ⟨_, τ, _, h, _⟩
  exact H.graph_declared_root τ r h

private theorem owner_types {b : Fin 2} {x o : D} (h : H.Owner b x o) :
    H.type x = .base ∧ H.type o = ownerType b := by
  have ha := H.center_allowed (if b = 0 then .ownerH else .ownerV) o x h
  fin_cases b <;> cases hx : H.type x <;> cases ho : H.type o <;>
    simp_all [AllowedIncidence, ownerType]

@[simp] theorem graph_owner (b : Fin 2) (x o : D) :
    OwnerEdge H.graph (sumRooting D) b (Sum.inr x) (Sum.inr o) ↔ H.Owner b x o := by
  constructor
  · rintro ⟨hx, ho, j, hl⟩
    have htx := ((H.graph_declared .base x).mp hx).symm
    have hto := ((H.graph_declared (ownerType b) o).mp ho).symm
    have hp : H.LayerPair (if b = 0 then .ownerH else .ownerV) x o := by
      have hh := (H.graph_link (ownershipRoot b j) x o).mp hl
      simpa only [DataPair, rootBlock_ownershipRoot] using hh
    have ha : AllowedIncidence (if b = 0 then .ownerH else .ownerV) (H.type o) (H.type x) := by
      rw [htx, hto]
      fin_cases b <;> trivial
    exact H.layerPair_allowed ha ((H.layerPair_symm _ x o).mp hp)
  · intro h
    have ht := H.owner_types h
    refine ⟨(H.graph_declared _ _).mpr ht.1.symm,
      (H.graph_declared _ _).mpr ht.2.symm, ⟨0, κ_pos⟩, ?_⟩
    apply (H.graph_link _ x o).mpr
    have hp := (H.layerPair_symm _ o x).mp (H.center_layerPair h)
    simpa only [DataPair, rootBlock_ownershipRoot] using hp

@[simp] theorem graph_owner_root_left (b : Fin 2) (r : Root) (v : Root ⊕ D) :
    ¬ OwnerEdge H.graph (sumRooting D) b (Sum.inl r) v :=
  fun h => H.graph_declared_root .base r h.1

@[simp] theorem graph_owner_root_right (b : Fin 2) (r : Root) (v : Root ⊕ D) :
    ¬ OwnerEdge H.graph (sumRooting D) b v (Sum.inl r) :=
  fun h => H.graph_declared_root (ownerType b) r h.2.1

@[simp] theorem graph_completeE (x y : D) :
    Source.CompleteE H.graph (sumRooting D) (Sum.inr x) (Sum.inr y) ↔ H.CompleteE x y := by
  simp only [Source.CompleteE, TypedData.CompleteE, Sum.exists,
    H.graph_declared_root, H.graph_declared, H.graph_matching,
    H.graph_matching_root_left, H.graph_matching_root_right,
    false_and, and_false, exists_false, false_or, or_false]
  simp only [eq_comm]

@[simp] theorem graph_completeD (x y : D) :
    Source.CompleteD H.graph (sumRooting D) (Sum.inr x) (Sum.inr y) ↔ H.CompleteD x y := by
  simp only [Source.CompleteD, TypedData.CompleteD, Sum.exists,
    H.graph_declared_root, H.graph_declared, H.graph_matching,
    H.graph_matching_root_left, H.graph_matching_root_right,
    false_and, and_false, exists_false, false_or, or_false]
  simp only [eq_comm]

@[simp] theorem graph_completeE_root_left (r : Root) (v : Root ⊕ D) :
    ¬ Source.CompleteE H.graph (sumRooting D) (Sum.inl r) v :=
  fun h => H.graph_declared_root .base r h.1

@[simp] theorem graph_completeE_root_right (r : Root) (v : Root ⊕ D) :
    ¬ Source.CompleteE H.graph (sumRooting D) v (Sum.inl r) :=
  fun h => H.graph_declared_root .base r h.2.1

@[simp] theorem graph_completeD_root_left (r : Root) (v : Root ⊕ D) :
    ¬ Source.CompleteD H.graph (sumRooting D) (Sum.inl r) v :=
  fun h => H.graph_declared_root .base r h.1

@[simp] theorem graph_completeD_root_right (r : Root) (v : Root ⊕ D) :
    ¬ Source.CompleteD H.graph (sumRooting D) v (Sum.inl r) :=
  fun h => H.graph_declared_root .base r h.2.1

@[simp] theorem graph_parentH (a b : D) :
    Source.ParentH H.graph (sumRooting D) (Sum.inr a) (Sum.inr b) ↔ H.ParentH a b := by
  simp [Source.ParentH, TypedData.ParentH, Sum.exists]

@[simp] theorem graph_parentV (a b : D) :
    Source.ParentV H.graph (sumRooting D) (Sum.inr a) (Sum.inr b) ↔ H.ParentV a b := by
  simp [Source.ParentV, TypedData.ParentV, Sum.exists]

@[simp] theorem graph_parentH_root_left (r : Root) (v : Root ⊕ D) :
    ¬ Source.ParentH H.graph (sumRooting D) (Sum.inl r) v := by
  rintro ⟨x, y, _, h, _⟩
  exact H.graph_owner_root_right 0 r x h

@[simp] theorem graph_parentH_root_right (r : Root) (v : Root ⊕ D) :
    ¬ Source.ParentH H.graph (sumRooting D) v (Sum.inl r) := by
  rintro ⟨x, y, _, _, h⟩
  exact H.graph_owner_root_right 0 r y h

@[simp] theorem graph_parentV_root_left (r : Root) (v : Root ⊕ D) :
    ¬ Source.ParentV H.graph (sumRooting D) (Sum.inl r) v := by
  rintro ⟨x, y, _, h, _⟩
  exact H.graph_owner_root_right 1 r y h

@[simp] theorem graph_parentV_root_right (r : Root) (v : Root ⊕ D) :
    ¬ Source.ParentV H.graph (sumRooting D) v (Sum.inl r) := by
  rintro ⟨x, y, _, _, h⟩
  exact H.graph_owner_root_right 1 r x h

end TypedData
end TranscendentalTuran.Green.Realization
