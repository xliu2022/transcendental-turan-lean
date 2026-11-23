module

public import TranscendentalTuran.Encoding.LocalRules

@[expose] public section

namespace TranscendentalTuran.Source.Certificates

open TuranUniversality Encoding Network Parameters

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  {G : RGraph V 3} {μ : Rooting Root V} {H : RGraph W 3} {ν : Rooting Root W}

/-- The primitive information retained by a selected certificate. Data
vertices carry all of their existing declarations and their mark status;
only the explicitly selected one-root labels need their links retained. -/
structure Replay (G : RGraph V 3) (μ : Rooting Root V)
    (D : Finset V) (L : Finset Root) (H : RGraph W 3) (ν : Rooting Root W) where
  map : D ↪ W
  data : ∀ x, Data ν (map x)
  declared : ∀ x τ, Declared G μ τ x.val → Declared H ν τ (map x)
  marked : ∀ x, Marked G μ x.val → Marked H ν (map x)
  link : ∀ r ∈ L, ∀ x y : D, Link G μ r x.val y.val → Link H ν r (map x) (map y)
  triples : ∀ x y z : D, {x.val, y.val, z.val} ∈ G.edges →
    {map x, map y, map z} ∈ H.edges

/-- The exact finite resources needed before declaration roots and the
marker pair are added. The final source witness uses 26 + 12 + 2 roots. -/
structure SelectedWitness (G : RGraph V 3) (μ : Rooting Root V) where
  data : Finset V
  labels : Finset Root
  data_bound : data.card ≤ 13
  labels_bound : labels.card ≤ 12
  data_status : ∀ x ∈ data, Data μ x
  labels_present : ∀ r ∈ labels, ∃ v, μ.val r = some v
  fails : ∀ {W : Type} [DecidableEq W] (H : RGraph W 3) (ν : Rooting Root W),
    Replay G μ data labels H ν → ¬ RootedLegal H ν

structure MatchingToken (G : RGraph V 3) (μ : Rooting Root V)
    (b : Fin 4) (x y : V) where
  leftType : PhysicalType
  rightType : PhysicalType
  left_decl : Declared G μ leftType x
  right_decl : Declared G μ rightType y
  allowed : AllowedIncidence (matchingBlock b) leftType rightType
  index : Fin M
  link : Link G μ (matchingRoot b index) x y

namespace MatchingToken

def label {b : Fin 4} {x y : V} (t : MatchingToken G μ b x y) : Root := matchingRoot b t.index

theorem exists_of_edge {b : Fin 4} {x y : V} (h : MatchingEdge G μ b x y) :
    Nonempty (MatchingToken G μ b x y) := by
  obtain ⟨τ, σ, hx, hy, ha, j, he⟩ := h
  exact ⟨⟨τ, σ, hx, hy, ha, j, he⟩⟩

theorem present {b : Fin 4} {x y : V} (t : MatchingToken G μ b x y) :
    ∃ v, μ.val t.label = some v := by
  obtain ⟨_, _, v, hv, _⟩ := t.link
  exact ⟨v, hv⟩

theorem replay {D : Finset V} {L : Finset Root}
    (F : Replay G μ D L H ν) {b : Fin 4} {x y : V}
    (t : MatchingToken G μ b x y) (hx : x ∈ D) (hy : y ∈ D) (hr : t.label ∈ L) :
    MatchingEdge H ν b (F.map ⟨x, hx⟩) (F.map ⟨y, hy⟩) :=
  ⟨t.leftType, t.rightType, F.declared ⟨x, hx⟩ _ t.left_decl,
    F.declared ⟨y, hy⟩ _ t.right_decl, t.allowed, t.index,
    F.link t.label hr ⟨x, hx⟩ ⟨y, hy⟩ t.link⟩

end MatchingToken

structure OwnerToken (G : RGraph V 3) (μ : Rooting Root V)
    (b : Fin 2) (x o : V) where
  base_decl : Declared G μ .base x
  owner_decl : Declared G μ (ownerType b) o
  index : Fin κ
  link : Link G μ (ownershipRoot b index) x o

namespace OwnerToken

def label {b : Fin 2} {x o : V} (t : OwnerToken G μ b x o) : Root := ownershipRoot b t.index

theorem exists_of_edge {b : Fin 2} {x o : V} (h : OwnerEdge G μ b x o) :
    Nonempty (OwnerToken G μ b x o) := by
  obtain ⟨hx, ho, j, he⟩ := h
  exact ⟨⟨hx, ho, j, he⟩⟩

theorem present {b : Fin 2} {x o : V} (t : OwnerToken G μ b x o) :
    ∃ v, μ.val t.label = some v := by
  obtain ⟨_, _, v, hv, _⟩ := t.link
  exact ⟨v, hv⟩

theorem replay {D : Finset V} {L : Finset Root}
    (F : Replay G μ D L H ν) {b : Fin 2} {x o : V}
    (t : OwnerToken G μ b x o) (hx : x ∈ D) (ho : o ∈ D) (hr : t.label ∈ L) :
    OwnerEdge H ν b (F.map ⟨x, hx⟩) (F.map ⟨o, ho⟩) :=
  ⟨F.declared ⟨x, hx⟩ _ t.base_decl, F.declared ⟨o, ho⟩ _ t.owner_decl, t.index,
    F.link t.label hr ⟨x, hx⟩ ⟨o, ho⟩ t.link⟩

end OwnerToken

def ChainClause (G : RGraph V 3) (μ : Rooting Root V)
    (b₀ b₁ b₂ b₃ : Fin 4) (center : PhysicalType) (x y : V) : Prop :=
  Declared G μ .base x ∧ Declared G μ .base y ∧
  ∃ p c p', Declared G μ .port01 p ∧ Declared G μ center c ∧
    Declared G μ .port23 p' ∧
    MatchingEdge G μ b₀ x p ∧ MatchingEdge G μ b₁ c p ∧
    MatchingEdge G μ b₂ c p' ∧ MatchingEdge G μ b₃ y p'

structure ChainToken (G : RGraph V 3) (μ : Rooting Root V)
    (b₀ b₁ b₂ b₃ : Fin 4) (center : PhysicalType) (x y : V) where
  port₀ : V
  middle : V
  port₁ : V
  x_decl : Declared G μ .base x
  y_decl : Declared G μ .base y
  port₀_decl : Declared G μ .port01 port₀
  middle_decl : Declared G μ center middle
  port₁_decl : Declared G μ .port23 port₁
  edge₀ : MatchingToken G μ b₀ x port₀
  edge₁ : MatchingToken G μ b₁ middle port₀
  edge₂ : MatchingToken G μ b₂ middle port₁
  edge₃ : MatchingToken G μ b₃ y port₁

namespace ChainToken

variable {b₀ b₁ b₂ b₃ : Fin 4} {center : PhysicalType} {x y : V}

theorem exists_of_clause (h : ChainClause G μ b₀ b₁ b₂ b₃ center x y) :
    Nonempty (ChainToken G μ b₀ b₁ b₂ b₃ center x y) := by
  obtain ⟨hx, hy, p, c, p', hp, hc, hp', h₀, h₁, h₂, h₃⟩ := h
  obtain ⟨t₀⟩ := MatchingToken.exists_of_edge h₀
  obtain ⟨t₁⟩ := MatchingToken.exists_of_edge h₁
  obtain ⟨t₂⟩ := MatchingToken.exists_of_edge h₂
  obtain ⟨t₃⟩ := MatchingToken.exists_of_edge h₃
  exact ⟨⟨p, c, p', hx, hy, hp, hc, hp', t₀, t₁, t₂, t₃⟩⟩

def data (t : ChainToken G μ b₀ b₁ b₂ b₃ center x y) : Finset V :=
  {x, y, t.port₀, t.middle, t.port₁}

def labels (t : ChainToken G μ b₀ b₁ b₂ b₃ center x y) : Finset Root :=
  {t.edge₀.label, t.edge₁.label, t.edge₂.label, t.edge₃.label}

theorem data_card (t : ChainToken G μ b₀ b₁ b₂ b₃ center x y) : t.data.card ≤ 5 := by
  have h₁ := Finset.card_insert_le x ({y, t.port₀, t.middle, t.port₁} : Finset V)
  have h₂ := Finset.card_insert_le y ({t.port₀, t.middle, t.port₁} : Finset V)
  have h₃ := Finset.card_le_three (a := t.port₀) (b := t.middle) (c := t.port₁)
  dsimp [data]
  omega

theorem labels_card (t : ChainToken G μ b₀ b₁ b₂ b₃ center x y) : t.labels.card ≤ 4 := by
  have h₁ := Finset.card_insert_le t.edge₀.label
    ({t.edge₁.label, t.edge₂.label, t.edge₃.label} : Finset Root)
  have h₂ := Finset.card_le_three (a := t.edge₁.label) (b := t.edge₂.label) (c := t.edge₃.label)
  dsimp [labels]
  omega

theorem data_status (t : ChainToken G μ b₀ b₁ b₂ b₃ center x y) :
    ∀ v ∈ t.data, Data μ v := by
  intro v hv
  simp only [data, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact t.x_decl.1
  · exact t.y_decl.1
  · exact t.port₀_decl.1
  · exact t.middle_decl.1
  · exact t.port₁_decl.1

theorem labels_present (t : ChainToken G μ b₀ b₁ b₂ b₃ center x y) :
    ∀ r ∈ t.labels, ∃ v, μ.val r = some v := by
  intro r hr
  simp only [labels, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact t.edge₀.present
  · exact t.edge₁.present
  · exact t.edge₂.present
  · exact t.edge₃.present

theorem replay {D : Finset V} {L : Finset Root} (F : Replay G μ D L H ν)
    (t : ChainToken G μ b₀ b₁ b₂ b₃ center x y)
    (hD : t.data ⊆ D) (hL : t.labels ⊆ L)
    (hx : x ∈ D) (hy : y ∈ D) :
    ChainClause H ν b₀ b₁ b₂ b₃ center (F.map ⟨x, hx⟩) (F.map ⟨y, hy⟩) := by
  have hp : t.port₀ ∈ D := hD (by simp [data])
  have hc : t.middle ∈ D := hD (by simp [data])
  have hp' : t.port₁ ∈ D := hD (by simp [data])
  exact ⟨F.declared ⟨x, hx⟩ _ t.x_decl, F.declared ⟨y, hy⟩ _ t.y_decl,
    F.map ⟨t.port₀, hp⟩, F.map ⟨t.middle, hc⟩, F.map ⟨t.port₁, hp'⟩,
    F.declared ⟨t.port₀, hp⟩ _ t.port₀_decl, F.declared ⟨t.middle, hc⟩ _ t.middle_decl,
    F.declared ⟨t.port₁, hp'⟩ _ t.port₁_decl,
    MatchingToken.replay F t.edge₀ hx hp (hL (by simp [labels])),
    MatchingToken.replay F t.edge₁ hc hp (hL (by simp [labels])),
    MatchingToken.replay F t.edge₂ hc hp' (hL (by simp [labels])),
    MatchingToken.replay F t.edge₃ hy hp' (hL (by simp [labels]))⟩

end ChainToken

abbrev EToken (G : RGraph V 3) (μ : Rooting Root V) (x y : V) :=
  ChainToken G μ 0 1 3 2 .center13 x y
abbrev DToken (G : RGraph V 3) (μ : Rooting Root V) (x y : V) :=
  ChainToken G μ 1 0 2 3 .center02 x y

theorem exists_EToken {x y : V} (h : CompleteE G μ x y) : Nonempty (EToken G μ x y) :=
  ChainToken.exists_of_clause h
theorem exists_DToken {x y : V} (h : CompleteD G μ x y) : Nonempty (DToken G μ x y) :=
  ChainToken.exists_of_clause h

end TranscendentalTuran.Source.Certificates
