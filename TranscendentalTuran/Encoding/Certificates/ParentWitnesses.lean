module

public import TranscendentalTuran.Encoding.Certificates.ChainWitnesses

@[expose] public section

namespace TranscendentalTuran.Source.Certificates

open TuranUniversality Encoding Network Parameters

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

/-- Two five-vertex chains and three owners give thirteen data vertices;
their eight structural labels and four ownership labels give twelve. -/
theorem two_chain_resources (D₁ D₂ : Finset V) (L₁ L₂ : Finset Root)
    (hD₁ : D₁.card ≤ 5) (hD₂ : D₂.card ≤ 5) (hL₁ : L₁.card ≤ 4) (hL₂ : L₂.card ≤ 4)
    (hdata₁ : ∀ v ∈ D₁, Data μ v) (hdata₂ : ∀ v ∈ D₂, Data μ v)
    (hpresent₁ : ∀ r ∈ L₁, ∃ v, μ.val r = some v)
    (hpresent₂ : ∀ r ∈ L₂, ∃ v, μ.val r = some v)
    (a b c : V) (ha : Data μ a) (hb : Data μ b) (hc : Data μ c)
    (r₀ r₁ r₂ r₃ : Root) (hr₀ : ∃ v, μ.val r₀ = some v) (hr₁ : ∃ v, μ.val r₁ = some v)
    (hr₂ : ∃ v, μ.val r₂ = some v) (hr₃ : ∃ v, μ.val r₃ = some v)
    (hfail : ∀ {W : Type} [DecidableEq W] (H : RGraph W 3) (ν : Rooting Root W),
      Replay G μ ((D₁ ∪ D₂) ∪ {a, b, c}) ((L₁ ∪ L₂) ∪ {r₀, r₁, r₂, r₃}) H ν →
        ¬ RootedLegal H ν) : Nonempty (SelectedWitness G μ) := by
  refine ⟨⟨(D₁ ∪ D₂) ∪ {a, b, c}, (L₁ ∪ L₂) ∪ {r₀, r₁, r₂, r₃},
    ?_, ?_, ?_, ?_, hfail⟩⟩
  · have h₁ := Finset.card_union_le D₁ D₂
    have h₂ := Finset.card_union_le (D₁ ∪ D₂) ({a, b, c} : Finset V)
    have h₃ := Finset.card_le_three (a := a) (b := b) (c := c)
    omega
  · have h₁ := Finset.card_union_le L₁ L₂
    have h₂ := Finset.card_union_le (L₁ ∪ L₂) ({r₀, r₁, r₂, r₃} : Finset Root)
    have h₃ := Finset.card_le_four (a := r₀) (b := r₁) (c := r₂) (d := r₃)
    omega
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact hdata₁ v hv
      · exact hdata₂ v hv
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
  · intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · rcases Finset.mem_union.mp hr with hr | hr
      · exact hpresent₁ r hr
      · exact hpresent₂ r hr
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem witness_parentH {a b c : V}
    (ha : ParentH G μ a c) (hb : ParentH G μ b c) (hne : a ≠ b) :
    Nonempty (SelectedWitness G μ) := by
  obtain ⟨x, y, hm, hxa, hyc⟩ := ha
  obtain ⟨x', y', hm', hxb, hyc'⟩ := hb
  obtain ⟨s⟩ := MoveToken.exists_of_move hm
  obtain ⟨t⟩ := MoveToken.exists_of_move hm'
  obtain ⟨s₀⟩ := OwnerToken.exists_of_edge hxa
  obtain ⟨s₁⟩ := OwnerToken.exists_of_edge hyc
  obtain ⟨t₀⟩ := OwnerToken.exists_of_edge hxb
  obtain ⟨t₁⟩ := OwnerToken.exists_of_edge hyc'
  refine two_chain_resources s.data t.data s.labels t.labels s.data_card t.data_card
    s.labels_card t.labels_card s.data_status t.data_status s.labels_present t.labels_present
    a b c s₀.owner_decl.1 t₀.owner_decl.1 s₁.owner_decl.1
    s₀.label s₁.label t₀.label t₁.label s₀.present s₁.present t₀.present t₁.present ?_
  intro W _ H ν F hlegal
  have hDs : s.data ⊆ (s.data ∪ t.data) ∪ {a, b, c} :=
    Finset.subset_union_left.trans Finset.subset_union_left
  have hDt : t.data ⊆ (s.data ∪ t.data) ∪ {a, b, c} :=
    Finset.subset_union_right.trans Finset.subset_union_left
  have hLs : s.labels ⊆ (s.labels ∪ t.labels) ∪ {s₀.label, s₁.label, t₀.label, t₁.label} :=
    Finset.subset_union_left.trans Finset.subset_union_left
  have hLt : t.labels ⊆ (s.labels ∪ t.labels) ∪ {s₀.label, s₁.label, t₀.label, t₁.label} :=
    Finset.subset_union_right.trans Finset.subset_union_left
  have hx := hDs s.left_mem
  have hy := hDs s.right_mem
  have hx' := hDt t.left_mem
  have hy' := hDt t.right_mem
  have hpa : ParentH H ν (F.map ⟨a, by simp⟩) (F.map ⟨c, by simp⟩) :=
    ⟨F.map ⟨x, hx⟩, F.map ⟨y, hy⟩, MoveToken.replay F s hDs hLs hx hy,
      OwnerToken.replay F s₀ hx (by simp) (by simp),
      OwnerToken.replay F s₁ hy (by simp) (by simp)⟩
  have hpb : ParentH H ν (F.map ⟨b, by simp⟩) (F.map ⟨c, by simp⟩) :=
    ⟨F.map ⟨x', hx'⟩, F.map ⟨y', hy'⟩, MoveToken.replay F t hDt hLt hx' hy',
      OwnerToken.replay F t₀ hx' (by simp) (by simp),
      OwnerToken.replay F t₁ hy' (by simp) (by simp)⟩
  have heq := hlegal.parentH_unique _ _ _ hpa hpb
  exact hne (congrArg Subtype.val (F.map.injective heq))

theorem witness_parentV {a b c : V}
    (ha : ParentV G μ a c) (hb : ParentV G μ b c) (hne : a ≠ b) :
    Nonempty (SelectedWitness G μ) := by
  obtain ⟨x, y, hm, hya, hxc⟩ := ha
  obtain ⟨x', y', hm', hyb, hxc'⟩ := hb
  obtain ⟨s⟩ := exists_DToken hm
  obtain ⟨t⟩ := exists_DToken hm'
  obtain ⟨s₀⟩ := OwnerToken.exists_of_edge hya
  obtain ⟨s₁⟩ := OwnerToken.exists_of_edge hxc
  obtain ⟨t₀⟩ := OwnerToken.exists_of_edge hyb
  obtain ⟨t₁⟩ := OwnerToken.exists_of_edge hxc'
  refine two_chain_resources s.data t.data s.labels t.labels s.data_card t.data_card
    s.labels_card t.labels_card s.data_status t.data_status s.labels_present t.labels_present
    a b c s₀.owner_decl.1 t₀.owner_decl.1 s₁.owner_decl.1
    s₀.label s₁.label t₀.label t₁.label s₀.present s₁.present t₀.present t₁.present ?_
  intro W _ H ν F hlegal
  have hDs : s.data ⊆ (s.data ∪ t.data) ∪ {a, b, c} :=
    Finset.subset_union_left.trans Finset.subset_union_left
  have hDt : t.data ⊆ (s.data ∪ t.data) ∪ {a, b, c} :=
    Finset.subset_union_right.trans Finset.subset_union_left
  have hLs : s.labels ⊆ (s.labels ∪ t.labels) ∪ {s₀.label, s₁.label, t₀.label, t₁.label} :=
    Finset.subset_union_left.trans Finset.subset_union_left
  have hLt : t.labels ⊆ (s.labels ∪ t.labels) ∪ {s₀.label, s₁.label, t₀.label, t₁.label} :=
    Finset.subset_union_right.trans Finset.subset_union_left
  have hx := hDs s.left_mem
  have hy := hDs s.right_mem
  have hx' := hDt t.left_mem
  have hy' := hDt t.right_mem
  have hpa : ParentV H ν (F.map ⟨a, by simp⟩) (F.map ⟨c, by simp⟩) :=
    ⟨F.map ⟨x, hx⟩, F.map ⟨y, hy⟩, ChainToken.replay F s hDs hLs hx hy,
      OwnerToken.replay F s₀ hy (by simp) (by simp),
      OwnerToken.replay F s₁ hx (by simp) (by simp)⟩
  have hpb : ParentV H ν (F.map ⟨b, by simp⟩) (F.map ⟨c, by simp⟩) :=
    ⟨F.map ⟨x', hx'⟩, F.map ⟨y', hy'⟩, ChainToken.replay F t hDt hLt hx' hy',
      OwnerToken.replay F t₀ hy' (by simp) (by simp),
      OwnerToken.replay F t₁ hx' (by simp) (by simp)⟩
  have heq := hlegal.parentV_unique _ _ _ hpa hpb
  exact hne (congrArg Subtype.val (F.map.injective heq))

/-- Every failure of the actual seventeen source clauses has a selected
positive witness with the manuscript's exact data and structural budgets. -/
theorem exists_selectedWitness (hbad : ¬ RootedLegal G μ) :
    Nonempty (SelectedWitness G μ) := by
  classical
  by_contra hnone
  apply hbad
  constructor
  · intro e he
    by_contra hroot
    obtain ⟨x, y, z, _, _, _, rfl⟩ := Finset.card_eq_three.mp (G.uniform e he)
    have hd (v : V) (hv : v ∈ ({x, y, z} : Finset V)) : Data μ v :=
      fun hr => hroot ⟨v, hv, hr⟩
    exact hnone (witness_data_edge he (hd x (by simp)) (hd y (by simp)) (hd z (by simp)))
  · intro r hr x y he
    exact hnone (witness_passive hr he)
  · intro x τ σ hx hy
    by_contra hne
    exact hnone (witness_declaration_conflict hx hy hne)
  · intro r hr x y τ σ hx hy he
    by_contra hne
    exact hnone (witness_generic hr hx hy he (fun h => h hne))
  · intro r x y τ σ hx hy he
    by_contra hallowed
    exact hnone (witness_special hx hy he hallowed)
  · intro b x y z hy hz
    by_contra hne
    exact hnone (witness_matching_left hy hz hne)
  · intro b x y z hx hy
    by_contra hne
    exact hnone (witness_matching_right hx hy hne)
  · intro b c x y p hx hy hxp hyp
    by_contra hrole
    exact hnone (witness_role (Or.inl ⟨hx, hy⟩) hxp hyp hrole)
  · intro b c x y p hx hy hxp hyp
    by_contra hrole
    exact hnone (witness_role (Or.inr ⟨hx, hy⟩) hxp hyp hrole)
  · intro b x a a' ha ha'
    by_contra hne
    exact hnone (witness_owner_functional ha ha' hne)
  · intro r x y c hx hy he
    exact hnone (witness_same_component hx hy he)
  · intro x y hx hy
    by_contra hne
    exact hnone (witness_two_marks hx hy hne)
  · intro x y a b hm ha hb
    by_contra hne
    exact hnone (witness_owner_preservation hm ha hb hne)
  · intro a b c ha hb
    by_contra hne
    exact hnone (witness_parentH ha hb hne)
  · intro a b c ha hb
    by_contra hne
    exact hnone (witness_parentV ha hb hne)
  · intro m x y o hm hmo hxo he
    exact hnone (witness_boundaryH hm hmo hxo he)
  · intro m x y o hm hmo hxo he
    exact hnone (witness_boundaryV hm hmo hxo he)

end TranscendentalTuran.Source.Certificates
