module

public import TranscendentalTuran.Encoding.LocalRules

@[expose] public section

/-! # Ordinary subgraph monotonicity of the concrete source rules
Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  {G : RGraph V 3} {H : RGraph W 3} {μ : Rooting Root V} {ν : Rooting Root W}

structure RootedMap (G : RGraph V 3) (μ : Rooting Root V)
    (H : RGraph W 3) (ν : Rooting Root W) where
  map : V ↪ W
  hom : G.IsHom H map
  roots : ∀ r x, μ.val r = some x → ν.val r = some (map x)
  data : ∀ x, Data μ x → Data ν (map x)

namespace RootedMap

variable (F : RootedMap G μ H ν)

theorem link {r x y} (h : Link G μ r x y) : Link H ν r (F.map x) (F.map y) := by
  obtain ⟨hx, hy, v, hv, he⟩ := h
  refine ⟨F.data x hx, F.data y hy, F.map v, F.roots r v hv, ?_⟩
  simpa only [Finset.image_insert, Finset.image_singleton] using F.hom _ he

theorem pairLink {r s x} (h : PairLink G μ r s x) : PairLink H ν r s (F.map x) := by
  obtain ⟨hx, u, v, hu, hv, he⟩ := h
  refine ⟨F.data x hx, F.map u, F.map v, F.roots r u hu, F.roots s v hv, ?_⟩
  simpa only [Finset.image_insert, Finset.image_singleton] using F.hom _ he

theorem marked {x} (h : Marked G μ x) : Marked H ν (F.map x) := F.pairLink h

theorem declared {τ x} (h : Declared G μ τ x) : Declared H ν τ (F.map x) := by
  refine ⟨F.data x h.1, ?_⟩
  rcases h.2 with ⟨j, hj⟩ | ⟨ht, hm⟩
  · exact Or.inl ⟨j, F.pairLink hj⟩
  · exact Or.inr ⟨ht, F.marked hm⟩

theorem matchingEdge {b x y} (h : MatchingEdge G μ b x y) :
    MatchingEdge H ν b (F.map x) (F.map y) := by
  obtain ⟨τ, σ, hx, hy, ha, j, he⟩ := h
  exact ⟨τ, σ, F.declared hx, F.declared hy, ha, j, F.link he⟩

theorem ownerEdge {b x o} (h : OwnerEdge G μ b x o) :
    OwnerEdge H ν b (F.map x) (F.map o) := by
  obtain ⟨hx, ho, j, he⟩ := h
  exact ⟨F.declared hx, F.declared ho, j, F.link he⟩

theorem isCenter {x} (h : IsCenter G μ x) : IsCenter H ν (F.map x) := by
  rcases h with h | h
  · exact Or.inl (F.declared h)
  · exact Or.inr (F.declared h)

theorem completeE {x y} (h : CompleteE G μ x y) :
    CompleteE H ν (F.map x) (F.map y) := by
  obtain ⟨hx, hy, p, c, p', hp, hc, hp', h0, h1, h3, h2⟩ := h
  exact ⟨F.declared hx, F.declared hy, F.map p, F.map c, F.map p',
    F.declared hp, F.declared hc, F.declared hp', F.matchingEdge h0,
    F.matchingEdge h1, F.matchingEdge h3, F.matchingEdge h2⟩

theorem completeD {x y} (h : CompleteD G μ x y) :
    CompleteD H ν (F.map x) (F.map y) := by
  obtain ⟨hx, hy, p, c, p', hp, hc, hp', h1, h0, h2, h3⟩ := h
  exact ⟨F.declared hx, F.declared hy, F.map p, F.map c, F.map p',
    F.declared hp, F.declared hc, F.declared hp', F.matchingEdge h1,
    F.matchingEdge h0, F.matchingEdge h2, F.matchingEdge h3⟩

theorem parentH {a b} (h : ParentH G μ a b) : ParentH H ν (F.map a) (F.map b) := by
  obtain ⟨x, y, hm, hx, hy⟩ := h
  exact ⟨F.map x, F.map y, hm.imp F.completeE F.completeD, F.ownerEdge hx, F.ownerEdge hy⟩

theorem parentV {a b} (h : ParentV G μ a b) : ParentV H ν (F.map a) (F.map b) := by
  obtain ⟨x, y, hm, hx, hy⟩ := h
  exact ⟨F.map x, F.map y, F.completeD hm, F.ownerEdge hx, F.ownerEdge hy⟩

theorem structuralAt {r x y} (h : StructuralAt G μ r x y) :
    StructuralAt H ν r (F.map x) (F.map y) := by
  obtain ⟨τ, σ, hx, hy, hax, hay, hs, he⟩ := h
  exact ⟨τ, σ, F.declared hx, F.declared hy, hax, hay, hs, F.link he⟩

include F in
/-- Positive violations survive a rooted edge-preserving injection. -/
theorem rootedLegal (hH : RootedLegal H ν) : RootedLegal G μ := by
  classical
  constructor
  · intro e he
    obtain ⟨w, hw, hr⟩ := hH.covers_edges _ (F.hom e he)
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨v, hv, ?_⟩
    by_contra hd
    exact F.data v hd hr
  · intro r hr x y he
    exact hH.passive_empty r hr _ _ (F.link he)
  · intro x τ σ hx hy
    exact hH.declarations_unique _ _ _ (F.declared hx) (F.declared hy)
  · intro r hr x y τ σ hx hy he
    exact hH.generic_different r hr _ _ _ _ (F.declared hx) (F.declared hy) (F.link he)
  · intro r x y τ σ hx hy he
    exact hH.special_allowed r _ _ _ _ (F.declared hx) (F.declared hy) (F.link he)
  · intro b x y z hxy hxz
    exact F.map.injective (hH.matching_left b _ _ _ (F.matchingEdge hxy) (F.matchingEdge hxz))
  · intro b x y z hxz hyz
    exact F.map.injective (hH.matching_right b _ _ _ (F.matchingEdge hxz) (F.matchingEdge hyz))
  · intro b c x y p hx hy hxp hyp
    obtain ⟨hbc, hxy⟩ := hH.port_base_unique b c _ _ _
      (F.declared hx) (F.declared hy) (F.matchingEdge hxp) (F.matchingEdge hyp)
    exact ⟨hbc, F.map.injective hxy⟩
  · intro b c x y p hx hy hxp hyp
    obtain ⟨hbc, hxy⟩ := hH.port_center_unique b c _ _ _
      (F.isCenter hx) (F.isCenter hy) (F.matchingEdge hxp) (F.matchingEdge hyp)
    exact ⟨hbc, F.map.injective hxy⟩
  · intro b x a a' ha ha'
    exact F.map.injective (hH.owner_functional b _ _ _ (F.ownerEdge ha) (F.ownerEdge ha'))
  · intro r x y c hx hy hxy
    exact hH.same_component_forbidden r _ _ _ (F.structuralAt hx) (F.structuralAt hy) (F.link hxy)
  · intro x y hx hy
    exact F.map.injective (hH.marks_unique _ _ (F.marked hx) (F.marked hy))
  · intro x y a b hm ha hb
    exact F.map.injective (hH.E_preserves_vertical _ _ _ _
      (F.completeE hm) (F.ownerEdge ha) (F.ownerEdge hb))
  · intro a b c ha hb
    exact F.map.injective (hH.parentH_unique _ _ _ (F.parentH ha) (F.parentH hb))
  · intro a b c ha hb
    exact F.map.injective (hH.parentV_unique _ _ _ (F.parentV ha) (F.parentV hb))
  · intro m x y o hm hmo hxo he
    exact hH.boundaryH _ _ _ _ (F.marked hm) (F.ownerEdge hmo) (F.ownerEdge hxo)
      (he.imp F.completeE F.completeD)
  · intro m x y o hm hmo hxo he
    exact hH.boundaryV _ _ _ _ (F.marked hm) (F.ownerEdge hmo) (F.ownerEdge hxo) (F.completeD he)

end RootedMap

noncomputable def rootedMapOfEmbedding {f : V → W} (hf : G.IsEmbedding H f)
    (ν : Rooting Root W) : RootedMap G (pullbackRooting ν ⟨f, hf.1⟩) H ν where
  map := ⟨f, hf.1⟩
  hom := hf.2
  roots := fun r x hx => (pullbackRooting_some_iff ν ⟨f, hf.1⟩ r x).mp hx
  data := fun x hx h => hx ((mem_pullbackRooting_range ν ⟨f, hf.1⟩ x).mpr h)

theorem admissible_of_embedding {f : V → W} (hf : G.IsEmbedding H f)
    (hH : Admissible H) : Admissible G := by
  obtain ⟨ν, hν⟩ := hH
  exact ⟨pullbackRooting ν ⟨f, hf.1⟩, (rootedMapOfEmbedding hf ν).rootedLegal hν⟩

end TranscendentalTuran.Source
