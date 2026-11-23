module

public import TranscendentalTuran.Construction.Parameters
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Explicit declaring pairs

Formalization author and responsible maintainer: Xizhi Liu.

The root labels are zero based: labels `0` and `1` implement the pair written
`12` in the manuscript. The declaring pairs all lie among the passive roots.
The maps below are computable; their proofs never enumerate the root set.
-/

namespace TranscendentalTuran.Encoding

open Parameters

abbrev Root := Fin q
abbrev PairIndex := Fin 7 × Fin N

def passiveSlot (i : Fin ((7 * N) * 2)) : Root :=
  ⟨K + N + i.val, by have hi := i.isLt; unfold q; omega⟩

theorem passiveSlot_injective : Function.Injective passiveSlot := by
  intro a b h
  have hv := congrArg Fin.val h
  apply Fin.ext
  change K + N + a.val = K + N + b.val at hv
  omega

def declaringRoot (p : PairIndex × Fin 2) : Root :=
  passiveSlot (finProdFinEquiv (finProdFinEquiv p.1, p.2))

theorem declaringRoot_injective : Function.Injective declaringRoot := by
  intro a b h
  have h1 := passiveSlot_injective h
  have h2 := finProdFinEquiv.injective h1
  apply Prod.ext
  · exact finProdFinEquiv.injective (congrArg Prod.fst h2)
  · simpa only using congrArg (fun z : Fin (7 * N) × Fin 2 => z.2) h2

theorem declaringRoot_passive (p : PairIndex × Fin 2) :
    K + N ≤ (declaringRoot p).val := by
  change K + N ≤ K + N + _
  omega

def declaringPair (p : PairIndex) : Finset Root :=
  Finset.univ.image (fun s : Fin 2 => declaringRoot (p, s))

theorem mem_declaringPair {p : PairIndex} {r : Root} :
    r ∈ declaringPair p ↔ ∃ s : Fin 2, declaringRoot (p, s) = r := by
  simp [declaringPair]

theorem declaringPair_card (p : PairIndex) : (declaringPair p).card = 2 := by
  rw [declaringPair, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact congrArg Prod.snd (declaringRoot_injective h)

theorem declaringPair_disjoint {p p' : PairIndex} (h : p ≠ p') :
    Disjoint (declaringPair p) (declaringPair p') := by
  apply Finset.disjoint_left.mpr
  intro r hr hr'
  obtain ⟨s, hs⟩ := mem_declaringPair.mp hr
  obtain ⟨s', hs'⟩ := mem_declaringPair.mp hr'
  exact h (congrArg Prod.fst (declaringRoot_injective (hs.trans hs'.symm)))

theorem declaringPair_injective : Function.Injective declaringPair := by
  intro p p' h
  have hr : declaringRoot (p, 0) ∈ declaringPair p :=
    mem_declaringPair.mpr ⟨0, rfl⟩
  rw [h] at hr
  obtain ⟨s, hs⟩ := mem_declaringPair.mp hr
  exact (congrArg Prod.fst (declaringRoot_injective hs)).symm

def markerLeft : Root := ⟨0, q_pos⟩
def markerRight : Root := ⟨1, by rw [q_value]; decide⟩
def markerPair : Finset Root := {markerLeft, markerRight}

theorem marker_distinct : markerLeft ≠ markerRight := by
  intro h
  have := congrArg Fin.val h
  change (0 : ℕ) = 1 at this
  omega

theorem markerPair_card : markerPair.card = 2 := by
  simp [markerPair, marker_distinct]

theorem marker_declaring_disjoint (p : PairIndex) :
    Disjoint markerPair (declaringPair p) := by
  apply Finset.disjoint_left.mpr
  intro r hr hd
  obtain ⟨s, rfl⟩ := mem_declaringPair.mp hd
  have hlow := declaringRoot_passive (p, s)
  simp only [markerPair, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with h | h
  · have hv := congrArg Fin.val h
    change (declaringRoot (p, s)).val = 0 at hv
    have hk := K_value
    omega
  · have hv := congrArg Fin.val h
    change (declaringRoot (p, s)).val = 1 at hv
    have hk := K_value
    omega

set_option compiler.extract_closed false in
/-- The family `F_ν`, with exactly `N` vertex-disjoint declaring pairs. -/
def typePairs (ν : Fin 7) : Finset (Finset Root) :=
  Finset.univ.image (fun j : Fin N => declaringPair (ν, j))

theorem typePairs_card (ν : Fin 7) : (typePairs ν).card = N := by
  rw [typePairs, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact congrArg Prod.snd (declaringPair_injective h)

set_option compiler.extract_closed false in
@[macro_inline] def declaringPairs : Finset (Finset Root) :=
  Finset.univ.image declaringPair

set_option compiler.extract_closed false in
@[macro_inline] def Γ : Finset (Finset Root) := insert markerPair declaringPairs

theorem Γ_card_two {e : Finset Root} (he : e ∈ Γ) : e.card = 2 := by
  simp only [Γ, Finset.mem_insert] at he
  rcases he with rfl | he
  · exact markerPair_card
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    exact declaringPair_card p

/-- The complete declaring-root family, including the marker, is a matching. -/
theorem Γ_matching {e f : Finset Root} (he : e ∈ Γ) (hf : f ∈ Γ) (hne : e ≠ f) :
    Disjoint e f := by
  simp only [Γ, Finset.mem_insert] at he hf
  rcases he with rfl | he <;> rcases hf with rfl | hf
  · exact (hne rfl).elim
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hf
    exact marker_declaring_disjoint p
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    exact (marker_declaring_disjoint p).symm
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨p', _, rfl⟩ := Finset.mem_image.mp hf
    apply declaringPair_disjoint
    intro h
    exact hne (congrArg declaringPair h)

end TranscendentalTuran.Encoding
