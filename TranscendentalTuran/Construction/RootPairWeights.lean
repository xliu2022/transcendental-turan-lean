module

public import TranscendentalTuran.Encoding.Layout
public import TuranUniversality.Weighted.Symmetric
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace TranscendentalTuran.Encoding

open TuranUniversality TuranUniversality.Weighted Parameters Network
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

def physicalOfIndex : Fin 7 → PhysicalType :=
  ![.base, .port01, .port23, .center13, .center02, .ownerH, .ownerV]

@[simp] theorem physicalIndex_physicalOfIndex (ν : Fin 7) :
    physicalIndex (physicalOfIndex ν) = ν := by fin_cases ν <;> rfl

@[simp] theorem physicalOfIndex_physicalIndex (τ : PhysicalType) :
    physicalOfIndex (physicalIndex τ) = τ := by cases τ <;> rfl

@[macro_inline] def physicalEquiv : PhysicalType ≃ Fin 7 :=
  ⟨physicalIndex, physicalOfIndex, physicalOfIndex_physicalIndex, physicalIndex_physicalOfIndex⟩

theorem declaringPair_eq (p : PairIndex) :
    declaringPair p = {declaringRoot (p, 0), declaringRoot (p, 1)} := by
  ext r
  simp only [mem_declaringPair, Fin.exists_fin_two, Finset.mem_insert, Finset.mem_singleton]
  constructor <;> rintro (h | h) <;> first | exact Or.inl h.symm | exact Or.inr h.symm

/-- Root pairs that neither declare a physical type nor mark the source. -/
@[macro_inline] def neutralPairs : Finset (Finset Root) := Finset.univ.powersetCard 2 \ Γ

/-- The prescribed unmarked two-root link of a data vertex of type `τ`. -/
def allowedPairs (τ : PhysicalType) : Finset (Finset Root) :=
  neutralPairs ∪ typePairs (physicalIndex τ)

theorem declaringPair_mem_Γ (p : PairIndex) : declaringPair p ∈ Γ :=
  Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)

theorem markerPair_mem_Γ : markerPair ∈ Γ := Finset.mem_insert_self _ _

theorem markerPair_ne_declaringPair (p : PairIndex) : markerPair ≠ declaringPair p := by
  intro h
  have hm : markerLeft ∈ markerPair := by simp [markerPair]
  have hp : markerLeft ∈ declaringPair p := by simpa only [h] using hm
  exact Finset.disjoint_left.mp (marker_declaring_disjoint p) hm hp

theorem mem_neutralPairs (p : Finset Root) :
    p ∈ neutralPairs ↔ p.card = 2 ∧ p ∉ Γ := by
  simp only [neutralPairs, Finset.mem_sdiff, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]

theorem typePairs_subset_Γ (ν : Fin 7) : typePairs ν ⊆ Γ := by
  intro p hp
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
  exact declaringPair_mem_Γ (ν, j)

theorem typePairs_card_two (ν : Fin 7) {p : Finset Root} (hp : p ∈ typePairs ν) : p.card = 2 :=
  Γ_card_two (typePairs_subset_Γ ν hp)

theorem allowedPairs_card_two (τ : PhysicalType) {p : Finset Root}
    (hp : p ∈ allowedPairs τ) : p.card = 2 := by
  rcases Finset.mem_union.mp hp with hn | ht
  · exact (mem_neutralPairs p).mp hn |>.1
  · exact typePairs_card_two _ ht

theorem declaringPair_mem_allowedPairs (τ σ : PhysicalType) (j : Fin N) :
    declaringPair (physicalIndex τ, j) ∈ allowedPairs σ ↔ τ = σ := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hn | ht
    · exact False.elim (((mem_neutralPairs _).mp hn).2 (declaringPair_mem_Γ _))
    · obtain ⟨k, _, heq⟩ := Finset.mem_image.mp ht
      exact physicalIndex_injective
        (congrArg Prod.fst (declaringPair_injective heq)).symm
  · rintro rfl
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

theorem markerPair_not_allowedPairs (τ : PhysicalType) : markerPair ∉ allowedPairs τ := by
  intro h
  rcases Finset.mem_union.mp h with hn | ht
  · exact ((mem_neutralPairs _).mp hn).2 markerPair_mem_Γ
  · obtain ⟨j, _, heq⟩ := Finset.mem_image.mp ht
    exact markerPair_ne_declaringPair _ heq.symm

def pairWeight (P : Finset (Finset Root)) (z : Root → ℝ) : ℝ :=
  ∑ p ∈ P, ∏ r ∈ p, z r

def declaringWeight (z : Root → ℝ) (ν : Fin 7) : ℝ :=
  ∑ j : Fin N, z (declaringRoot ((ν, j), 0)) * z (declaringRoot ((ν, j), 1))

def markerWeight (z : Root → ℝ) : ℝ := z markerLeft * z markerRight

theorem declaringPair_weight (z : Root → ℝ) (p : PairIndex) :
    (∏ r ∈ declaringPair p, z r) = z (declaringRoot (p, 0)) * z (declaringRoot (p, 1)) := by
  rw [declaringPair, Finset.prod_image]
  · exact Fin.prod_univ_two _
  · intro a _ b _ h
    exact congrArg Prod.snd (declaringRoot_injective h)

theorem typePairs_weight (z : Root → ℝ) (ν : Fin 7) :
    pairWeight (typePairs ν) z = declaringWeight z ν := by
  unfold pairWeight typePairs declaringWeight
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j _
    exact declaringPair_weight z (ν, j)
  · intro a _ b _ h
    exact congrArg Prod.snd (declaringPair_injective h)

theorem Γ_weight (z : Root → ℝ) :
    pairWeight Γ z = markerWeight z + ∑ ν : Fin 7, declaringWeight z ν := by
  have hnot : markerPair ∉ declaringPairs := by
    intro h
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
    exact markerPair_ne_declaringPair p hp.symm
  unfold pairWeight Γ
  rw [Finset.sum_insert hnot]
  have hm : (∏ r ∈ markerPair, z r) = markerWeight z := by
    simp [markerPair, marker_distinct, markerWeight]
  rw [hm]
  congr 1
  rw [declaringPairs, Finset.sum_image]
  · simp_rw [declaringPair_weight]
    exact Fintype.sum_prod_type _
  · intro a _ b _ h
    exact declaringPair_injective h

theorem neutralPairs_weight (z : Root → ℝ) :
    pairWeight neutralPairs z + pairWeight Γ z = elementary Finset.univ z 2 := by
  apply Finset.sum_sdiff
  intro p hp
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Γ_card_two hp⟩

theorem allowedPairs_weight (z : Root → ℝ) (τ : PhysicalType) :
    pairWeight (allowedPairs τ) z = elementary Finset.univ z 2 - markerWeight z -
      ∑ ν ∈ Finset.univ.erase (physicalIndex τ), declaringWeight z ν := by
  have hdis : Disjoint neutralPairs (typePairs (physicalIndex τ)) := by
    apply Finset.disjoint_left.mpr
    intro p hn ht
    exact ((mem_neutralPairs p).mp hn).2 (typePairs_subset_Γ _ ht)
  have hu : pairWeight (allowedPairs τ) z = pairWeight neutralPairs z +
      pairWeight (typePairs (physicalIndex τ)) z := Finset.sum_union hdis
  have hn := neutralPairs_weight z
  rw [Γ_weight] at hn
  have hs := Finset.sum_erase_add (s := Finset.univ) (f := declaringWeight z)
    (Finset.mem_univ (physicalIndex τ))
  rw [hu, typePairs_weight]
  linarith

end TranscendentalTuran.Encoding
