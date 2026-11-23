module

public import TranscendentalTuran.Encoding.Certificates.LocalWitnesses

@[expose] public section

namespace TranscendentalTuran.Source.Certificates

open TuranUniversality Encoding Network Parameters

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

namespace ChainToken

variable {b₀ b₁ b₂ b₃ : Fin 4} {center : PhysicalType} {x y : V}

theorem left_mem (t : ChainToken G μ b₀ b₁ b₂ b₃ center x y) : x ∈ t.data := by
  simp [data]
theorem right_mem (t : ChainToken G μ b₀ b₁ b₂ b₃ center x y) : y ∈ t.data := by
  simp [data]

end ChainToken

inductive MoveToken (G : RGraph V 3) (μ : Rooting Root V) (x y : V)
  | east : EToken G μ x y → MoveToken G μ x y
  | diagonal : DToken G μ x y → MoveToken G μ x y

namespace MoveToken

variable {x y : V}

def data : MoveToken G μ x y → Finset V
  | .east t => t.data
  | .diagonal t => t.data
def labels : MoveToken G μ x y → Finset Root
  | .east t => t.labels
  | .diagonal t => t.labels

theorem data_card (t : MoveToken G μ x y) : t.data.card ≤ 5 := by
  cases t with
  | east t => exact t.data_card
  | diagonal t => exact t.data_card
theorem labels_card (t : MoveToken G μ x y) : t.labels.card ≤ 4 := by
  cases t with
  | east t => exact t.labels_card
  | diagonal t => exact t.labels_card
theorem data_status (t : MoveToken G μ x y) : ∀ v ∈ t.data, Data μ v := by
  cases t with
  | east t => exact t.data_status
  | diagonal t => exact t.data_status
theorem labels_present (t : MoveToken G μ x y) :
    ∀ r ∈ t.labels, ∃ v, μ.val r = some v := by
  cases t with
  | east t => exact t.labels_present
  | diagonal t => exact t.labels_present
theorem left_mem (t : MoveToken G μ x y) : x ∈ t.data := by
  cases t with
  | east t => exact t.left_mem
  | diagonal t => exact t.left_mem
theorem right_mem (t : MoveToken G μ x y) : y ∈ t.data := by
  cases t with
  | east t => exact t.right_mem
  | diagonal t => exact t.right_mem

theorem exists_of_move (h : CompleteE G μ x y ∨ CompleteD G μ x y) :
    Nonempty (MoveToken G μ x y) := by
  rcases h with h | h
  · obtain ⟨t⟩ := exists_EToken h
    exact ⟨.east t⟩
  · obtain ⟨t⟩ := exists_DToken h
    exact ⟨.diagonal t⟩

theorem replay {W : Type*} [DecidableEq W] {H : RGraph W 3} {ν : Rooting Root W}
    {D : Finset V} {L : Finset Root} (F : Replay G μ D L H ν)
    (t : MoveToken G μ x y) (hD : t.data ⊆ D) (hL : t.labels ⊆ L)
    (hx : x ∈ D) (hy : y ∈ D) :
    CompleteE H ν (F.map ⟨x, hx⟩) (F.map ⟨y, hy⟩) ∨
      CompleteD H ν (F.map ⟨x, hx⟩) (F.map ⟨y, hy⟩) := by
  cases t with
  | east t => exact Or.inl (ChainToken.replay F t hD hL hx hy)
  | diagonal t => exact Or.inr (ChainToken.replay F t hD hL hx hy)

end MoveToken

theorem witness_owner_preservation {x y a b : V}
    (hm : CompleteE G μ x y) (ha : OwnerEdge G μ 1 x a) (hb : OwnerEdge G μ 1 y b)
    (hne : a ≠ b) : Nonempty (SelectedWitness G μ) := by
  obtain ⟨t⟩ := exists_EToken hm
  obtain ⟨s⟩ := OwnerToken.exists_of_edge ha
  obtain ⟨u⟩ := OwnerToken.exists_of_edge hb
  let D := t.data ∪ {a, b}
  let L := t.labels ∪ {s.label, u.label}
  have hD : t.data ⊆ D := Finset.subset_union_left
  have hL : t.labels ⊆ L := Finset.subset_union_left
  have hx : x ∈ D := hD t.left_mem
  have hy : y ∈ D := hD t.right_mem
  have haD : a ∈ D := by simp [D]
  have hbD : b ∈ D := by simp [D]
  have hsL : s.label ∈ L := by simp [L]
  have huL : u.label ∈ L := by simp [L]
  refine ⟨⟨D, L, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have h := Finset.card_union_le t.data ({a, b} : Finset V)
    have h' := Finset.card_le_two (a := a) (b := b)
    have ht := t.data_card
    dsimp [D]; omega
  · have h := Finset.card_union_le t.labels ({s.label, u.label} : Finset Root)
    have h' := Finset.card_le_two (a := s.label) (b := u.label)
    have ht := t.labels_card
    dsimp [L]; omega
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact t.data_status v hv
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact s.owner_decl.1
      · exact u.owner_decl.1
  · intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact t.labels_present r hr
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact s.present
      · exact u.present
  · intro W _ H ν F hlegal
    have heq := hlegal.E_preserves_vertical _ _ _ _
      (ChainToken.replay F t hD hL hx hy)
      (OwnerToken.replay F s hx haD hsL) (OwnerToken.replay F u hy hbD huL)
    exact hne (congrArg Subtype.val (F.map.injective heq))

theorem witness_boundaryH {m x y o : V}
    (hm : Marked G μ m) (hmo : OwnerEdge G μ 0 m o) (hxo : OwnerEdge G μ 0 x o)
    (hmove : CompleteE G μ y x ∨ CompleteD G μ y x) :
    Nonempty (SelectedWitness G μ) := by
  obtain ⟨t⟩ := MoveToken.exists_of_move hmove
  obtain ⟨s⟩ := OwnerToken.exists_of_edge hmo
  obtain ⟨u⟩ := OwnerToken.exists_of_edge hxo
  let D := t.data ∪ {m, o}
  let L := t.labels ∪ {s.label, u.label}
  have hD : t.data ⊆ D := Finset.subset_union_left
  have hL : t.labels ⊆ L := Finset.subset_union_left
  have hx : x ∈ D := hD t.right_mem
  have hy : y ∈ D := hD t.left_mem
  have hmD : m ∈ D := by simp [D]
  have hoD : o ∈ D := by simp [D]
  have hsL : s.label ∈ L := by simp [L]
  have huL : u.label ∈ L := by simp [L]
  refine ⟨⟨D, L, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have h := Finset.card_union_le t.data ({m, o} : Finset V)
    have h' := Finset.card_le_two (a := m) (b := o)
    have ht := t.data_card
    dsimp [D]; omega
  · have h := Finset.card_union_le t.labels ({s.label, u.label} : Finset Root)
    have h' := Finset.card_le_two (a := s.label) (b := u.label)
    have ht := t.labels_card
    dsimp [L]; omega
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact t.data_status v hv
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hm.1
      · exact s.owner_decl.1
  · intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact t.labels_present r hr
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact s.present
      · exact u.present
  · intro W _ H ν F hlegal
    exact hlegal.boundaryH _ _ _ _ (F.marked ⟨m, hmD⟩ hm)
      (OwnerToken.replay F s hmD hoD hsL) (OwnerToken.replay F u hx hoD huL)
      (MoveToken.replay F t hD hL hy hx)

theorem witness_boundaryV {m x y o : V}
    (hm : Marked G μ m) (hmo : OwnerEdge G μ 1 m o) (hxo : OwnerEdge G μ 1 x o)
    (hmove : CompleteD G μ x y) : Nonempty (SelectedWitness G μ) := by
  obtain ⟨t⟩ := exists_DToken hmove
  obtain ⟨s⟩ := OwnerToken.exists_of_edge hmo
  obtain ⟨u⟩ := OwnerToken.exists_of_edge hxo
  let D := t.data ∪ {m, o}
  let L := t.labels ∪ {s.label, u.label}
  have hD : t.data ⊆ D := Finset.subset_union_left
  have hL : t.labels ⊆ L := Finset.subset_union_left
  have hx : x ∈ D := hD t.left_mem
  have hy : y ∈ D := hD t.right_mem
  have hmD : m ∈ D := by simp [D]
  have hoD : o ∈ D := by simp [D]
  have hsL : s.label ∈ L := by simp [L]
  have huL : u.label ∈ L := by simp [L]
  refine ⟨⟨D, L, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have h := Finset.card_union_le t.data ({m, o} : Finset V)
    have h' := Finset.card_le_two (a := m) (b := o)
    have ht := t.data_card
    dsimp [D]; omega
  · have h := Finset.card_union_le t.labels ({s.label, u.label} : Finset Root)
    have h' := Finset.card_le_two (a := s.label) (b := u.label)
    have ht := t.labels_card
    dsimp [L]; omega
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact t.data_status v hv
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hm.1
      · exact s.owner_decl.1
  · intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact t.labels_present r hr
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact s.present
      · exact u.present
  · intro W _ H ν F hlegal
    exact hlegal.boundaryV _ _ _ _ (F.marked ⟨m, hmD⟩ hm)
      (OwnerToken.replay F s hmD hoD hsL) (OwnerToken.replay F u hx hoD huL)
      (ChainToken.replay F t hD hL hx hy)

end TranscendentalTuran.Source.Certificates
