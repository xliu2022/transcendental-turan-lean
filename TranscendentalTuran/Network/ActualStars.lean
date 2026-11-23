module

public import TranscendentalTuran.Encoding.LocalRules

@[expose] public section

/-!
# The individual-layer structural graphs are actual stars

Formalization author and responsible maintainer: Xizhi Liu.

Positive vertices are centers and negative vertices are leaves. In matching
blocks both sides have degree at most one; in owner blocks every negative
vertex has at most one positive neighbor. These assertions are consequences
of the manuscript's local rules, not additional assumptions.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

def PositiveAt (G : RGraph V 3) (μ : Rooting Root V) (b : Block) (x : V) : Prop :=
  ∃ τ, Declared G μ τ x ∧ sign b τ = 1

def NegativeAt (G : RGraph V 3) (μ : Rooting Root V) (b : Block) (x : V) : Prop :=
  ∃ τ, Declared G μ τ x ∧ sign b τ = -1

def CrossAt (G : RGraph V 3) (μ : Rooting Root V) (r : Layer) (c l : V) : Prop :=
  PositiveAt G μ r.1 c ∧ NegativeAt G μ r.1 l ∧ Link G μ (layerRoot r) c l

theorem positive_negative_disjoint (h : RootedLegal G μ) (b : Block) (x : V)
    (hp : PositiveAt G μ b x) (hn : NegativeAt G μ b x) : False := by
  obtain ⟨τ, hτ, ht⟩ := hp
  obtain ⟨σ, hσ, hs⟩ := hn
  have he := h.declarations_unique x τ σ hτ hσ
  subst σ
  omega

theorem CrossAt.allowed (h : RootedLegal G μ) {r : Layer} {c l : V}
    (hc : CrossAt G μ r c l) :
    ∃ τ σ, Declared G μ τ c ∧ Declared G μ σ l ∧
      AllowedIncidence r.1 τ σ := by
  obtain ⟨⟨τ, hτ, ht⟩, ⟨σ, hσ, hs⟩, he⟩ := hc
  have ha := (h.special_allowed r c l τ σ hτ hσ he).2.2
  refine ⟨τ, σ, hτ, hσ, ?_⟩
  rcases ha with ha | ha | ha
  · omega
  · exact ha
  · have hn := (incidence_signs ha).1
    omega

theorem CrossAt.structural (h : RootedLegal G μ) {r : Layer} {c l : V}
    (hc : CrossAt G μ r c l) : StructuralAt G μ r c l := by
  obtain ⟨⟨τ, hτ, ht⟩, ⟨σ, hσ, hs⟩, he⟩ := hc
  refine ⟨τ, σ, hτ, hσ, ?_, ?_, ?_, he⟩
  · unfold Active; omega
  · unfold Active; omega
  · omega

theorem CrossAt.structural_reverse {r : Layer} {c l : V}
    (hc : CrossAt G μ r c l) : StructuralAt G μ r l c := by
  obtain ⟨⟨τ, hτ, ht⟩, ⟨σ, hσ, hs⟩, he⟩ := hc
  refine ⟨σ, τ, hσ, hτ, ?_, ?_, ?_, link_symm he⟩
  · unfold Active; omega
  · unfold Active; omega
  · omega

def matchingLayer (b : Fin 4) (j : Fin Parameters.M) : Layer :=
  ⟨matchingBlock b, ⟨j.val, by
    have he : repetitions (matchingBlock b) = Parameters.M := by fin_cases b <;> rfl
    rw [he]
    exact j.isLt⟩⟩

theorem CrossAt.matching (h : RootedLegal G μ) (b : Fin 4) (j : Fin Parameters.M)
    {c l : V} (hc : CrossAt G μ (matchingLayer b j) c l) : MatchingEdge G μ b c l := by
  obtain ⟨τ, σ, hτ, hσ, ha⟩ := hc.allowed h
  refine ⟨τ, σ, hτ, hσ, ha, j, ?_⟩
  fin_cases b <;> exact hc.2.2

theorem ownerH_allowed {τ σ : PhysicalType} (h : AllowedIncidence .ownerH τ σ) :
    τ = .ownerH ∧ σ = .base := by
  cases τ <;> cases σ <;> simp_all [AllowedIncidence]

theorem ownerV_allowed {τ σ : PhysicalType} (h : AllowedIncidence .ownerV τ σ) :
    τ = .ownerV ∧ σ = .base := by
  cases τ <;> cases σ <;> simp_all [AllowedIncidence]

theorem CrossAt.ownerH (h : RootedLegal G μ) (j : Fin Parameters.κ) {c l : V}
    (hc : CrossAt G μ ⟨.ownerH, j⟩ c l) : OwnerEdge G μ 0 l c := by
  obtain ⟨τ, σ, hτ, hσ, ha⟩ := hc.allowed h
  obtain ⟨rfl, rfl⟩ := ownerH_allowed ha
  exact ⟨hσ, hτ, j, link_symm hc.2.2⟩

theorem CrossAt.ownerV (h : RootedLegal G μ) (j : Fin Parameters.κ) {c l : V}
    (hc : CrossAt G μ ⟨.ownerV, j⟩ c l) : OwnerEdge G μ 1 l c := by
  obtain ⟨τ, σ, hτ, hσ, ha⟩ := hc.allowed h
  obtain ⟨rfl, rfl⟩ := ownerV_allowed ha
  exact ⟨hσ, hτ, j, link_symm hc.2.2⟩

/-- Every negative vertex belongs to at most one positive-centered star. -/
theorem crossAt_unique_center (h : RootedLegal G μ) (r : Layer) {c d l : V}
    (hc : CrossAt G μ r c l) (hd : CrossAt G μ r d l) : c = d := by
  obtain ⟨b, j⟩ := r
  cases b with
  | match0 => exact h.matching_right 0 c d l (hc.matching h 0 j) (hd.matching h 0 j)
  | match1 => exact h.matching_right 1 c d l (hc.matching h 1 j) (hd.matching h 1 j)
  | match2 => exact h.matching_right 2 c d l (hc.matching h 2 j) (hd.matching h 2 j)
  | match3 => exact h.matching_right 3 c d l (hc.matching h 3 j) (hd.matching h 3 j)
  | ownerH => exact h.owner_functional 0 l c d (hc.ownerH h j) (hd.ownerH h j)
  | ownerV => exact h.owner_functional 1 l c d (hc.ownerV h j) (hd.ownerV h j)

theorem crossAt_matching_unique_leaf (h : RootedLegal G μ)
    (b : Fin 4) (j : Fin Parameters.M) {c l m : V}
    (hl : CrossAt G μ (matchingLayer b j) c l)
    (hm : CrossAt G μ (matchingLayer b j) c m) : l = m :=
  h.matching_left b c l m (hl.matching h b j) (hm.matching h b j)

/-- The actual same-layer prohibition removes exactly the within-star leaf pairs. -/
theorem no_pair_inside_star (h : RootedLegal G μ) (r : Layer) {c l m : V}
    (hl : CrossAt G μ r c l) (hm : CrossAt G μ r c m) :
    ¬ Link G μ (layerRoot r) l m :=
  h.same_component_forbidden r l m c hl.structural_reverse hm.structural_reverse

end TranscendentalTuran.Source
