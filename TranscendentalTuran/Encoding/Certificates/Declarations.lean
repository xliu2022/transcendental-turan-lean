module

public import TranscendentalTuran.Encoding.Certificates.FiniteSlice

@[expose] public section

namespace TranscendentalTuran.Source.Certificates

open TuranUniversality Encoding Network Parameters

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

theorem declaring_roots_in_Γ (p : PairIndex) :
    {declaringRoot (p, 0), declaringRoot (p, 1)} ∈ Γ := by
  have heq : ({declaringRoot (p, 0), declaringRoot (p, 1)} : Finset Root) = declaringPair p := by
    ext r
    constructor
    · intro hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact mem_declaringPair.mpr ⟨0, rfl⟩
      · exact mem_declaringPair.mpr ⟨1, rfl⟩
    · intro hr
      obtain ⟨s, rfl⟩ := mem_declaringPair.mp hr
      fin_cases s <;> simp
  rw [heq]
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)

theorem marker_roots_in_Γ : ({markerLeft, markerRight} : Finset Root) ∈ Γ := by
  exact Finset.mem_insert_self _ _

/-- One present declaring or marking triple, with its exact two root labels. -/
inductive DeclarationToken (G : RGraph V 3) (μ : Rooting Root V) (τ : PhysicalType) (x : V)
  | ordinary (j : Fin N)
      (edge : PairLink G μ (declaringRoot ((physicalIndex τ, j), 0))
        (declaringRoot ((physicalIndex τ, j), 1)) x) : DeclarationToken G μ τ x
  | marked (base : τ = .base) (edge : Marked G μ x) : DeclarationToken G μ τ x

namespace DeclarationToken

variable {τ : PhysicalType} {x : V}

def labels : DeclarationToken G μ τ x → Finset Root
  | .ordinary j _ => {declaringRoot ((physicalIndex τ, j), 0),
      declaringRoot ((physicalIndex τ, j), 1)}
  | .marked _ _ => {markerLeft, markerRight}

theorem exists_of_declared (h : Declared G μ τ x) : Nonempty (DeclarationToken G μ τ x) := by
  rcases h.2 with ⟨j, hj⟩ | ⟨hτ, hm⟩
  · exact ⟨.ordinary j hj⟩
  · exact ⟨.marked hτ hm⟩

theorem labels_card (t : DeclarationToken G μ τ x) : t.labels.card ≤ 2 := by
  cases t <;> exact Finset.card_le_two

theorem labels_present (t : DeclarationToken G μ τ x) :
    ∀ r ∈ t.labels, ∃ v, μ.val r = some v := by
  cases t with
  | ordinary j h =>
      obtain ⟨_, u, v, hu, hv, _⟩ := h
      intro r hr
      simp only [labels, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact ⟨u, hu⟩
      · exact ⟨v, hv⟩
  | marked hτ h =>
      obtain ⟨_, u, v, hu, hv, _⟩ := h
      intro r hr
      simp only [labels, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact ⟨u, hu⟩
      · exact ⟨v, hv⟩

theorem lift (S : Slice μ) (x : S.data) (t : DeclarationToken G μ τ x.val)
    (hL : t.labels ⊆ S.labels) :
    Declared (S.pattern G).graph (S.pattern G).canonical τ (Sum.inr (S.dataIndex x)) := by
  refine ⟨S.data_out G x, ?_⟩
  cases t with
  | ordinary j h =>
      have hr := hL (show declaringRoot ((physicalIndex τ, j), 0) ∈
        (DeclarationToken.ordinary j h).labels by simp [labels])
      have hs := hL (show declaringRoot ((physicalIndex τ, j), 1) ∈
        (DeclarationToken.ordinary j h).labels by simp [labels])
      exact Or.inl ⟨j, S.lift_pairLink G ⟨_, hr⟩ ⟨_, hs⟩ x
        (declaring_roots_in_Γ (physicalIndex τ, j)) h⟩
  | marked hτ h =>
      have hr := hL (show markerLeft ∈ (DeclarationToken.marked hτ h).labels by simp [labels])
      have hs := hL (show markerRight ∈ (DeclarationToken.marked hτ h).labels by simp [labels])
      exact Or.inr ⟨hτ, S.lift_pairLink G ⟨_, hr⟩ ⟨_, hs⟩ x marker_roots_in_Γ h⟩

end DeclarationToken

/-- Once conflicting declarations have been excluded, a single declaring
triple per data vertex preserves every type used by a positive witness. -/
theorem select_declaration_support
    (hunique : ∀ x τ σ, Declared G μ τ x → Declared G μ σ x → τ = σ) (x : V) :
    ∃ L : Finset Root, L.card ≤ 2 ∧ (∀ r ∈ L, ∃ v, μ.val r = some v) ∧
      ∀ τ, Declared G μ τ x → ∃ t : DeclarationToken G μ τ x, t.labels ⊆ L := by
  classical
  by_cases h : ∃ τ, Declared G μ τ x
  · obtain ⟨τ, hτ⟩ := h
    obtain ⟨t⟩ := DeclarationToken.exists_of_declared hτ
    refine ⟨t.labels, t.labels_card, t.labels_present, ?_⟩
    intro σ hσ
    have heq := hunique x σ τ hσ hτ
    subst σ
    exact ⟨t, Finset.Subset.refl _⟩
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro τ hτ
    exact False.elim (h ⟨τ, hτ⟩)

end TranscendentalTuran.Source.Certificates
