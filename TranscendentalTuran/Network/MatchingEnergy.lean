module

public import TranscendentalTuran.Network.LayerEnergy
public import TranscendentalTuran.Network.MatchingSquares
public import TranscendentalTuran.Network.OwnerPenalty

@[expose] public section

/-!
# Completion throughout the matching repetition blocks

Formalization author and responsible maintainer: Xizhi Liu.

The union incidence is an actual partial matching by the rooted local rules.
Completion is used only to lower the energy. The original polynomial still
uses the individual-layer energy from `LayerEnergy`.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network Parameters
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

noncomputable def unionLeafCenter (b : Fin 4)
    (l : NegativeVertex G μ (matchingBlock b)) : Option (PositiveVertex G μ (matchingBlock b)) := by
  classical
  exact if h : ∃ c : PositiveVertex G μ (matchingBlock b), MatchingEdge G μ b c.val l.val then
    some h.choose else none

theorem unionLeafCenter_some_iff (h : RootedLegal G μ) (b : Fin 4)
    (l : NegativeVertex G μ (matchingBlock b)) (c : PositiveVertex G μ (matchingBlock b)) :
    unionLeafCenter b l = some c ↔ MatchingEdge G μ b c.val l.val := by
  classical
  by_cases he : ∃ c : PositiveVertex G μ (matchingBlock b), MatchingEdge G μ b c.val l.val
  · rw [unionLeafCenter, dite_eq_left he, Option.some.injEq]
    constructor
    · intro hc; exact hc ▸ he.choose_spec
    · intro hc
      apply Subtype.ext
      exact h.matching_right b _ _ l.val he.choose_spec hc
  · rw [unionLeafCenter, dite_eq_right he]
    constructor
    · intro hc; cases hc
    · intro hc; exact False.elim (he ⟨c, hc⟩)

theorem unionLeafCenter_matching (h : RootedLegal G μ) (b : Fin 4) :
    StarEnergy.IsPartialMatching (unionLeafCenter (G := G) (μ := μ) b) := by
  intro l m c hl hm
  apply Subtype.ext
  exact h.matching_left b c.val l.val m.val
    ((unionLeafCenter_some_iff h b l c).mp hl) ((unionLeafCenter_some_iff h b m c).mp hm)

theorem leafCenter_matching (h : RootedLegal G μ) (b : Fin 4) (j : Fin M) :
    StarEnergy.IsPartialMatching (leafCenter (G := G) (μ := μ) (matchingLayer b j)) := by
  intro l m c hl hm
  apply Subtype.ext
  exact crossAt_matching_unique_leaf h b j
    ((leafCenter_some_iff h (matchingLayer b j) l c).mp hl)
    ((leafCenter_some_iff h (matchingLayer b j) m c).mp hm)

theorem leafCenter_subset_union (h : RootedLegal G μ) (b : Fin 4) (j : Fin M)
    (l : NegativeVertex G μ (matchingBlock b)) (c : PositiveVertex G μ (matchingBlock b))
    (hl : leafCenter (matchingLayer b j) l = some c) : unionLeafCenter b l = some c := by
  apply (unionLeafCenter_some_iff h b l c).mpr
  exact ((leafCenter_some_iff h (matchingLayer b j) l c).mp hl).matching h b j

noncomputable def unionMatchingEnergy (b : Fin 4) (w : V → ℝ) : ℝ :=
  StarEnergy.energy (unionLeafCenter (G := G) (μ := μ) b)
    (fun c => w c.val) (fun l => w l.val)

noncomputable def matchingBlockWeight (z : Root → ℝ) (b : Fin 4) : ℝ :=
  ∑ j : Fin M, z (matchingRoot b j)

noncomputable def matchingEnergy (z : Root → ℝ) (w : V → ℝ) : ℝ :=
  ∑ b : Fin 4, ∑ j : Fin M,
    z (matchingRoot b j) * actualLayerEnergy (G := G) (μ := μ) (matchingLayer b j) w

noncomputable def completedMatchingEnergy (z : Root → ℝ) (w : V → ℝ) : ℝ :=
  ∑ b : Fin 4, matchingBlockWeight z b * unionMatchingEnergy (G := G) (μ := μ) b w

theorem unionMatchingEnergy_nonneg (b : Fin 4) (w : V → ℝ) :
    0 ≤ unionMatchingEnergy (G := G) (μ := μ) b w := StarEnergy.energy_nonneg _ _ _

theorem completing_layer_decreases_energy (h : RootedLegal G μ)
    (b : Fin 4) (j : Fin M) (w : V → ℝ) (hw : ∀ x, 0 ≤ w x) :
    unionMatchingEnergy (G := G) (μ := μ) b w ≤
      actualLayerEnergy (G := G) (μ := μ) (matchingLayer b j) w :=
  StarEnergy.matching_energy_antitone (leafCenter_matching h b j)
    (unionLeafCenter_matching h b) (leafCenter_subset_union h b j)
    (fun c => w c.val) (fun l => w l.val) (fun c => hw c.val) (fun l => hw l.val)

theorem completing_blocks_decreases_energy (h : RootedLegal G μ)
    (z : Root → ℝ) (w : V → ℝ) (hz : ∀ r, 0 ≤ z r) (hw : ∀ x, 0 ≤ w x) :
    completedMatchingEnergy (G := G) (μ := μ) z w ≤ matchingEnergy (G := G) (μ := μ) z w := by
  apply Finset.sum_le_sum
  intro b _
  unfold matchingBlockWeight
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (completing_layer_decreases_energy h b j w hw) (hz _)

theorem actualEnergy_split (z : Root → ℝ) (w : V → ℝ) :
    actualEnergy (G := G) (μ := μ) z w =
      matchingEnergy (G := G) (μ := μ) z w + ownerEnergy (G := G) (μ := μ) z w := by
  unfold actualEnergy matchingEnergy ownerEnergy
  rw [Fintype.sum_sigma]
  rw [Fin.sum_univ_four, Fin.sum_univ_two]
  change (∑ j : Fin M, z (matchingRoot 0 j) * actualLayerEnergy ⟨.match0, j⟩ w) +
      ((∑ j : Fin M, z (matchingRoot 1 j) * actualLayerEnergy ⟨.match1, j⟩ w) +
      ((∑ j : Fin M, z (matchingRoot 2 j) * actualLayerEnergy ⟨.match2, j⟩ w) +
      ((∑ j : Fin M, z (matchingRoot 3 j) * actualLayerEnergy ⟨.match3, j⟩ w) +
      ((∑ j : Fin κ, z (ownershipRoot 0 j) * actualLayerEnergy ⟨.ownerH, j⟩ w) +
      ((∑ j : Fin κ, z (ownershipRoot 1 j) * actualLayerEnergy ⟨.ownerV, j⟩ w) + 0))))) = _
  change _ = ((∑ j : Fin M, z (matchingRoot 0 j) * actualLayerEnergy ⟨.match0, j⟩ w) +
      (∑ j : Fin M, z (matchingRoot 1 j) * actualLayerEnergy ⟨.match1, j⟩ w) +
      (∑ j : Fin M, z (matchingRoot 2 j) * actualLayerEnergy ⟨.match2, j⟩ w) +
      (∑ j : Fin M, z (matchingRoot 3 j) * actualLayerEnergy ⟨.match3, j⟩ w)) +
      ((∑ j : Fin κ, z (ownershipRoot 0 j) * actualLayerEnergy ⟨.ownerH, j⟩ w) +
      (∑ j : Fin κ, z (ownershipRoot 1 j) * actualLayerEnergy ⟨.ownerV, j⟩ w))
  ring

end TranscendentalTuran.Source
