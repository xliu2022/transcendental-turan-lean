module

public import TranscendentalTuran.Green.Realization.ActualEnergy
public import TranscendentalTuran.Network.FullLayerLinks
public import TranscendentalTuran.Construction.RootDataPolynomial

@[expose] public section

/-!
# Exact special-link polynomial of the ordinary lower realization

Formalization author and responsible maintainer: Xizhi Liu.

Every permitted signed-star pair is present in the template graph. The
ordinary two-uniform root link therefore attains the signed-star identity.
-/

namespace TranscendentalTuran.Green.Realization.TypedData

open Network Encoding Parameters TuranUniversality Source
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D] (H : TypedData D)

theorem positive_mass_eq (b : Block) (w : D → ℝ) :
    (∑ c : PositiveVertex H.graph (sumRooting D) b, RootData.dataWeights w c.val) =
      ∑ d : D, if sign b (H.type d) = 1 then w d else 0 := by
  rw [← H.sum_positive_subtype]
  symm
  apply Fintype.sum_equiv (H.positiveEquiv b)
  intro c
  rfl

theorem negative_mass_eq (b : Block) (w : D → ℝ) :
    (∑ l : NegativeVertex H.graph (sumRooting D) b, RootData.dataWeights w l.val) =
      ∑ d : D, if sign b (H.type d) = -1 then w d else 0 := by
  rw [← H.sum_negative_subtype]
  symm
  apply Fintype.sum_equiv (H.negativeEquiv b)
  intro l
  rfl

theorem graph_link_of_permitted (h : RootedLegal H.graph (sumRooting D))
    (r : Layer) (a b : LayerVertex H.graph (sumRooting D) r.1)
    (hp : StarEnergy.PermittedPair (leafCenter (G := H.graph) (μ := sumRooting D) r) a b) :
    Link H.graph (sumRooting D) (layerRoot r) (layerVertexVal r.1 a) (layerVertexVal r.1 b) := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      obtain ⟨x, rfl⟩ := (H.positiveInr_bijective r.1).2 a
      obtain ⟨y, rfl⟩ := (H.positiveInr_bijective r.1).2 b
      change H.positiveInr r.1 x ≠ H.positiveInr r.1 y at hp
      change Link H.graph (sumRooting D) (layerRoot r) (Sum.inr x.val) (Sum.inr y.val)
      apply (H.graph_link _ _ _).mpr
      apply (H.dataPair_layerRoot r x.val y.val).mpr
      refine ⟨?_, ?_, ?_, Or.inr (Or.inr ⟨x.property.trans y.property.symm, ?_⟩)⟩
      · intro hxy
        exact hp (congrArg (H.positiveInr r.1) (Subtype.ext hxy))
      · unfold Active; rw [x.property]; norm_num
      · unfold Active; rw [y.property]; norm_num
      · rintro ⟨c, hc, _⟩
        have hs := (H.center_signs hc).2
        have hx := x.property
        omega
    | inr b => exact ((leafCenter_some_iff h r b a).mp hp).2.2
  | inr a =>
    cases b with
    | inl b => exact link_symm ((leafCenter_some_iff h r a b).mp hp).2.2
    | inr b =>
      obtain ⟨x, rfl⟩ := (H.negativeInr_bijective r.1).2 a
      obtain ⟨y, rfl⟩ := (H.negativeInr_bijective r.1).2 b
      change H.negativeInr r.1 x ≠ H.negativeInr r.1 y ∧
        ¬ StarEnergy.SameStar (leafCenter (G := H.graph) (μ := sumRooting D) r)
          (H.negativeInr r.1 x) (H.negativeInr r.1 y) at hp
      change Link H.graph (sumRooting D) (layerRoot r) (Sum.inr x.val) (Sum.inr y.val)
      apply (H.graph_link _ _ _).mpr
      apply (H.dataPair_layerRoot r x.val y.val).mpr
      refine ⟨?_, ?_, ?_, Or.inr (Or.inr ⟨x.property.trans y.property.symm, ?_⟩)⟩
      · intro hxy
        exact hp.1 (congrArg (H.negativeInr r.1) (Subtype.ext hxy))
      · unfold Active; rw [x.property]; norm_num
      · unfold Active; rw [y.property]; norm_num
      · rintro ⟨c, hcx, hcy⟩
        let c' : H.PositiveData r.1 := ⟨c, (H.center_signs hcx).1⟩
        exact hp.2 ⟨H.positiveInr r.1 c',
          (H.leafCenter_some_iff_center h r x c').mpr hcx,
          (H.leafCenter_some_iff_center h r y c').mpr hcy⟩

theorem dataLink_layer_polynomial_eq (h : RootedLegal H.graph (sumRooting D))
    (r : Layer) (w : D → ℝ) :
    (RootData.dataLinkGraph H.graph (layerRoot r)).edgePolynomial w =
      ((∑ d : D, if sign r.1 (H.type d) = 1 then w d else 0) ^ 2 +
        (∑ d : D, if sign r.1 (H.type d) = -1 then w d else 0) ^ 2 -
          H.layerEnergy r.1 w) / 2 := by
  have hall : ∀ v, Data (sumRooting D) v → ∃ τ, Declared H.graph (sumRooting D) τ v := by
    intro v hv
    obtain ⟨d, rfl⟩ := sumRooting_data_exists hv
    exact ⟨H.type d, (H.graph_declared _ _).mpr rfl⟩
  rw [RootData.dataLink_polynomial_eq,
    actualLink_polynomial_eq h hall r (RootData.dataWeights w) (H.graph_link_of_permitted h r),
    H.positive_mass_eq, H.negative_mass_eq]
  rw [RootData.dataWeights, H.actualLayerEnergy_eq_layerEnergy h r w]

theorem actualEnergy_eq_layerEnergy (h : RootedLegal H.graph (sumRooting D))
    (z : Root → ℝ) (w : D → ℝ) :
    actualEnergy (G := H.graph) (μ := sumRooting D) z (RootData.dataWeights w) =
      ∑ r : Layer, z (layerRoot r) * H.layerEnergy r.1 w := by
  unfold actualEnergy
  apply Finset.sum_congr rfl
  intro r _
  rw [RootData.dataWeights, H.actualLayerEnergy_eq_layerEnergy h r w]

end TranscendentalTuran.Green.Realization.TypedData
