module

public import TranscendentalTuran.Encoding.Certificates.Support

@[expose] public section

namespace TranscendentalTuran.Source.Certificates

open TuranUniversality Encoding Network Parameters

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

namespace Replay

theorem isCenter {W : Type*} [DecidableEq W] {H : RGraph W 3} {ν : Rooting Root W}
    {D : Finset V} {L : Finset Root} (F : Replay G μ D L H ν)
    (x : D) (h : IsCenter G μ x.val) : IsCenter H ν (F.map x) :=
  h.imp (F.declared x _) (F.declared x _)

theorem structural {W : Type*} [DecidableEq W] {H : RGraph W 3} {ν : Rooting Root W}
    {D : Finset V} {L : Finset Root} (F : Replay G μ D L H ν)
    (r : Layer) (hr : layerRoot r ∈ L) (x y : D)
    (h : StructuralAt G μ r x.val y.val) : StructuralAt H ν r (F.map x) (F.map y) := by
  obtain ⟨τ, σ, hx, hy, hax, hay, hs, he⟩ := h
  exact ⟨τ, σ, F.declared x _ hx, F.declared y _ hy, hax, hay, hs,
    F.link _ hr x y he⟩

end Replay

theorem witness_data_edge {x y z : V} (he : {x, y, z} ∈ G.edges)
    (hx : Data μ x) (hy : Data μ y) (hz : Data μ z) :
    Nonempty (SelectedWitness G μ) := by
  refine ⟨⟨{x, y, z}, ∅, (Finset.card_le_three).trans (by decide), by simp,
    ?_, by simp, ?_⟩⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  · intro W _ H ν F hlegal
    let a : ({x, y, z} : Finset V) := ⟨x, by simp⟩
    let b : ({x, y, z} : Finset V) := ⟨y, by simp⟩
    let c : ({x, y, z} : Finset V) := ⟨z, by simp⟩
    obtain ⟨v, hv, hroot⟩ := hlegal.covers_edges _ (F.triples a b c he)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact F.data a hroot
    · exact F.data b hroot
    · exact F.data c hroot

theorem witness_passive {r : Root} {x y : V}
    (hr : IsPassive r) (he : Link G μ r x y) : Nonempty (SelectedWitness G μ) := by
  refine ⟨⟨{x, y}, {r}, (Finset.card_le_two).trans (by decide), by simp,
    ?_, ?_, ?_⟩⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact he.1
    · exact he.2.1
  · intro s hs
    obtain rfl := Finset.mem_singleton.mp hs
    exact ⟨he.2.2.choose, he.2.2.choose_spec.1⟩
  · intro W _ H ν F hlegal
    exact hlegal.passive_empty r hr _ _
      (F.link r (by simp) ⟨x, by simp⟩ ⟨y, by simp⟩ he)

theorem witness_declaration_conflict {x : V} {τ σ : PhysicalType}
    (hx : Declared G μ τ x) (hy : Declared G μ σ x) (hne : τ ≠ σ) :
    Nonempty (SelectedWitness G μ) := by
  refine ⟨⟨{x}, ∅, by simp, by simp, ?_, by simp, ?_⟩⟩
  · intro v hv
    obtain rfl := Finset.mem_singleton.mp hv
    exact hx.1
  · intro W _ H ν F hlegal
    exact hne (hlegal.declarations_unique _ _ _
      (F.declared ⟨x, by simp⟩ _ hx) (F.declared ⟨x, by simp⟩ _ hy))

theorem witness_generic {r : Root} {x y : V} {τ σ : PhysicalType}
    (hr : IsGeneric r) (hx : Declared G μ τ x) (hy : Declared G μ σ y)
    (he : Link G μ r x y) (hbad : ¬ τ ≠ σ) : Nonempty (SelectedWitness G μ) := by
  refine ⟨⟨{x, y}, {r}, (Finset.card_le_two).trans (by decide), by simp,
    ?_, ?_, ?_⟩⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hx.1
    · exact hy.1
  · intro s hs
    obtain rfl := Finset.mem_singleton.mp hs
    exact ⟨he.2.2.choose, he.2.2.choose_spec.1⟩
  · intro W _ H ν F hlegal
    exact hbad (hlegal.generic_different r hr _ _ _ _
      (F.declared ⟨x, by simp⟩ _ hx) (F.declared ⟨y, by simp⟩ _ hy)
      (F.link r (by simp) ⟨x, by simp⟩ ⟨y, by simp⟩ he))

theorem witness_special {r : Layer} {x y : V} {τ σ : PhysicalType}
    (hx : Declared G μ τ x) (hy : Declared G μ σ y)
    (he : Link G μ (layerRoot r) x y)
    (hbad : ¬ (Active r.1 τ ∧ Active r.1 σ ∧
      (sign r.1 τ = sign r.1 σ ∨ AllowedIncidence r.1 τ σ ∨ AllowedIncidence r.1 σ τ))) :
    Nonempty (SelectedWitness G μ) := by
  refine ⟨⟨{x, y}, {layerRoot r}, (Finset.card_le_two).trans (by decide), by simp,
    ?_, ?_, ?_⟩⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hx.1
    · exact hy.1
  · intro s hs
    obtain rfl := Finset.mem_singleton.mp hs
    exact ⟨he.2.2.choose, he.2.2.choose_spec.1⟩
  · intro W _ H ν F hlegal
    exact hbad (hlegal.special_allowed r _ _ _ _
      (F.declared ⟨x, by simp⟩ _ hx) (F.declared ⟨y, by simp⟩ _ hy)
      (F.link _ (by simp) ⟨x, by simp⟩ ⟨y, by simp⟩ he))

theorem witness_matching_left {b : Fin 4} {x y z : V}
    (hy : MatchingEdge G μ b x y) (hz : MatchingEdge G μ b x z) (hne : y ≠ z) :
    Nonempty (SelectedWitness G μ) := by
  obtain ⟨s⟩ := MatchingToken.exists_of_edge hy
  obtain ⟨t⟩ := MatchingToken.exists_of_edge hz
  refine ⟨⟨{x, y, z}, {s.label, t.label},
    (Finset.card_le_three).trans (by decide), (Finset.card_le_two).trans (by decide),
    ?_, ?_, ?_⟩⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact s.left_decl.1
    · exact s.right_decl.1
    · exact t.right_decl.1
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact s.present
    · exact t.present
  · intro W _ H ν F hlegal
    have heq := hlegal.matching_left b _ _ _
      (MatchingToken.replay F s (by simp) (by simp) (by simp))
      (MatchingToken.replay F t (by simp) (by simp) (by simp))
    exact hne (congrArg Subtype.val (F.map.injective heq))

theorem witness_matching_right {b : Fin 4} {x y z : V}
    (hx : MatchingEdge G μ b x z) (hy : MatchingEdge G μ b y z) (hne : x ≠ y) :
    Nonempty (SelectedWitness G μ) := by
  obtain ⟨s⟩ := MatchingToken.exists_of_edge hx
  obtain ⟨t⟩ := MatchingToken.exists_of_edge hy
  refine ⟨⟨{x, y, z}, {s.label, t.label},
    (Finset.card_le_three).trans (by decide), (Finset.card_le_two).trans (by decide),
    ?_, ?_, ?_⟩⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact s.left_decl.1
    · exact t.left_decl.1
    · exact s.right_decl.1
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact s.present
    · exact t.present
  · intro W _ H ν F hlegal
    have heq := hlegal.matching_right b _ _ _
      (MatchingToken.replay F s (by simp) (by simp) (by simp))
      (MatchingToken.replay F t (by simp) (by simp) (by simp))
    exact hne (congrArg Subtype.val (F.map.injective heq))

theorem witness_role {b c : Fin 4} {x y p : V}
    (hrole : (Declared G μ .base x ∧ Declared G μ .base y) ∨
      (IsCenter G μ x ∧ IsCenter G μ y))
    (hx : MatchingEdge G μ b x p) (hy : MatchingEdge G μ c y p)
    (hbad : ¬ (b = c ∧ x = y)) : Nonempty (SelectedWitness G μ) := by
  obtain ⟨s⟩ := MatchingToken.exists_of_edge hx
  obtain ⟨t⟩ := MatchingToken.exists_of_edge hy
  refine ⟨⟨{x, y, p}, {s.label, t.label},
    (Finset.card_le_three).trans (by decide), (Finset.card_le_two).trans (by decide),
    ?_, ?_, ?_⟩⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact s.left_decl.1
    · exact t.left_decl.1
    · exact s.right_decl.1
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact s.present
    · exact t.present
  · intro W _ H ν F hlegal
    have hs := MatchingToken.replay F s (by simp) (by simp) (by simp)
    have ht := MatchingToken.replay F t (by simp) (by simp) (by simp)
    have heq : b = c ∧ F.map ⟨x, by simp⟩ = F.map ⟨y, by simp⟩ := by
      rcases hrole with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact hlegal.port_base_unique b c _ _ _
          (F.declared ⟨x, by simp⟩ _ hx) (F.declared ⟨y, by simp⟩ _ hy) hs ht
      · exact hlegal.port_center_unique b c _ _ _
          (F.isCenter ⟨x, by simp⟩ hx) (F.isCenter ⟨y, by simp⟩ hy) hs ht
    exact hbad ⟨heq.1, congrArg Subtype.val (F.map.injective heq.2)⟩

theorem witness_owner_functional {b : Fin 2} {x a a' : V}
    (ha : OwnerEdge G μ b x a) (ha' : OwnerEdge G μ b x a') (hne : a ≠ a') :
    Nonempty (SelectedWitness G μ) := by
  obtain ⟨s⟩ := OwnerToken.exists_of_edge ha
  obtain ⟨t⟩ := OwnerToken.exists_of_edge ha'
  refine ⟨⟨{x, a, a'}, {s.label, t.label},
    (Finset.card_le_three).trans (by decide), (Finset.card_le_two).trans (by decide),
    ?_, ?_, ?_⟩⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact s.base_decl.1
    · exact s.owner_decl.1
    · exact t.owner_decl.1
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact s.present
    · exact t.present
  · intro W _ H ν F hlegal
    have heq := hlegal.owner_functional b _ _ _
      (OwnerToken.replay F s (by simp) (by simp) (by simp))
      (OwnerToken.replay F t (by simp) (by simp) (by simp))
    exact hne (congrArg Subtype.val (F.map.injective heq))

theorem witness_same_component {r : Layer} {x y c : V}
    (hx : StructuralAt G μ r x c) (hy : StructuralAt G μ r y c)
    (he : Link G μ (layerRoot r) x y) : Nonempty (SelectedWitness G μ) := by
  have hxcopy := hx
  obtain ⟨τ, σ, hxd, hcd, _, _, _, _⟩ := hxcopy
  refine ⟨⟨{x, y, c}, {layerRoot r}, (Finset.card_le_three).trans (by decide),
    by simp, ?_, ?_, ?_⟩⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact he.1
    · exact he.2.1
    · exact hcd.1
  · intro s hs
    obtain rfl := Finset.mem_singleton.mp hs
    exact ⟨he.2.2.choose, he.2.2.choose_spec.1⟩
  · intro W _ H ν F hlegal
    exact hlegal.same_component_forbidden r _ _ _
      (F.structural r (by simp) ⟨x, by simp⟩ ⟨c, by simp⟩ hx)
      (F.structural r (by simp) ⟨y, by simp⟩ ⟨c, by simp⟩ hy)
      (F.link _ (by simp) ⟨x, by simp⟩ ⟨y, by simp⟩ he)

theorem witness_two_marks {x y : V} (hx : Marked G μ x) (hy : Marked G μ y)
    (hne : x ≠ y) : Nonempty (SelectedWitness G μ) := by
  refine ⟨⟨{x, y}, ∅, (Finset.card_le_two).trans (by decide), by simp,
    ?_, by simp, ?_⟩⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hx.1
    · exact hy.1
  · intro W _ H ν F hlegal
    have heq := hlegal.marks_unique _ _ (F.marked ⟨x, by simp⟩ hx) (F.marked ⟨y, by simp⟩ hy)
    exact hne (congrArg Subtype.val (F.map.injective heq))

end TranscendentalTuran.Source.Certificates
