module

public import TranscendentalTuran.Network.LayerEnergy

@[expose] public section

/-!
# Missing owners supply the incomplete-base penalty

Formalization author and responsible maintainer: Xizhi Liu.

Missing means absent from the entire owner repetition block. Such a base is
an actual singleton in every individual layer of that block. The two blocks
therefore charge every incomplete base at least once.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network Parameters
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

abbrev BaseVertex (G : RGraph V 3) (μ : Rooting Root V) :=
  {x : V // Declared G μ .base x}

noncomputable instance : Fintype (BaseVertex G μ) := Fintype.ofFinite _

def ownershipBlock : Fin 2 → Block := ![.ownerH, .ownerV]

def ownershipLayer (b : Fin 2) (j : Fin κ) : Layer :=
  ⟨ownershipBlock b, ⟨j.val, by
    have hb : repetitions (ownershipBlock b) = κ := by fin_cases b <;> rfl
    rw [hb]
    exact j.isLt⟩⟩

theorem negative_owner_iff (b : Fin 2) (x : V) :
    NegativeAt G μ (ownershipBlock b) x ↔ Declared G μ .base x := by
  constructor
  · rintro ⟨τ, hτ, hs⟩
    fin_cases b <;> cases τ <;> simp_all [ownershipBlock, sign]
  · intro hx
    refine ⟨.base, hx, ?_⟩
    fin_cases b <;> rfl

def baseNegativeEquiv (b : Fin 2) : BaseVertex G μ ≃ NegativeVertex G μ (ownershipBlock b) where
  toFun x := ⟨x.val, (negative_owner_iff b x.val).mpr x.property⟩
  invFun x := ⟨x.val, (negative_owner_iff b x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def missingOwnerSquares (b : Fin 2) (w : V → ℝ) : ℝ := by
  classical
  exact ∑ x : BaseVertex G μ, if ¬ ∃ o, OwnerEdge G μ b x.val o then w x.val ^ 2 else 0

def IsComplete (x : V) : Prop :=
  (∃ o, OwnerEdge G μ 0 x o) ∧ (∃ o, OwnerEdge G μ 1 x o)

noncomputable def incompleteSquares (w : V → ℝ) : ℝ := by
  classical
  exact ∑ x : BaseVertex G μ, if ¬ IsComplete (G := G) (μ := μ) x.val then w x.val ^ 2 else 0

noncomputable def ownerBlockWeight (z : Root → ℝ) (b : Fin 2) : ℝ :=
  ∑ j : Fin κ, z (ownershipRoot b j)

noncomputable def ownerEnergy (z : Root → ℝ) (w : V → ℝ) : ℝ :=
  ∑ b : Fin 2, ∑ j : Fin κ,
    z (ownershipRoot b j) * actualLayerEnergy (G := G) (μ := μ) (ownershipLayer b j) w

theorem missingOwnerSquares_nonneg (b : Fin 2) (w : V → ℝ) :
    0 ≤ missingOwnerSquares (G := G) (μ := μ) b w := by
  classical
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> first | exact sq_nonneg _ | exact le_rfl

theorem incompleteSquares_nonneg (w : V → ℝ) :
    0 ≤ incompleteSquares (G := G) (μ := μ) w := by
  classical
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> first | exact sq_nonneg _ | exact le_rfl

theorem incompleteSquares_le_missing (w : V → ℝ) :
    incompleteSquares (G := G) (μ := μ) w ≤
      missingOwnerSquares (G := G) (μ := μ) 0 w + missingOwnerSquares (G := G) (μ := μ) 1 w := by
  classical
  unfold incompleteSquares missingOwnerSquares
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  unfold IsComplete
  split_ifs <;> simp_all <;> positivity

theorem owner_layer_penalty (h : RootedLegal G μ) (b : Fin 2) (j : Fin κ) (w : V → ℝ) :
    missingOwnerSquares (G := G) (μ := μ) b w ≤
      actualLayerEnergy (G := G) (μ := μ) (ownershipLayer b j) w := by
  classical
  have hm (l : NegativeVertex G μ (ownershipBlock b))
      (hl : ¬ ∃ o, OwnerEdge G μ b l.val o) :
      leafCenter (G := G) (μ := μ) (ownershipLayer b j) l = none := by
    fin_cases b
    · exact leafCenter_ownerH_missing h j l hl
    · exact leafCenter_ownerV_missing h j l hl
  calc
    _ = ∑ l : NegativeVertex G μ (ownershipBlock b),
        if ¬ ∃ o, OwnerEdge G μ b l.val o then w l.val ^ 2 else 0 := by
      apply Fintype.sum_equiv (baseNegativeEquiv (G := G) (μ := μ) b)
      intro x
      rfl
    _ ≤ ∑ l : NegativeVertex G μ (ownershipBlock b),
        if leafCenter (ownershipLayer b j) l = none then w l.val ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro l _
      by_cases hl : ¬ ∃ o, OwnerEdge G μ b l.val o
      · simp [hl, hm l hl]
      · simp only [hl, ite_false]
        split_ifs <;> first | exact sq_nonneg _ | exact le_rfl
    _ ≤ _ := StarEnergy.unmatched_penalty _ _ _

theorem ownerEnergy_blocks_bound (h : RootedLegal G μ) (z : Root → ℝ) (w : V → ℝ)
    (hz : ∀ r, 0 ≤ z r) :
    (∑ b : Fin 2, ownerBlockWeight z b * missingOwnerSquares (G := G) (μ := μ) b w) ≤
      ownerEnergy (G := G) (μ := μ) z w := by
  apply Finset.sum_le_sum
  intro b _
  unfold ownerBlockWeight
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (owner_layer_penalty h b j w) (hz _)

theorem ownerEnergy_penalty (h : RootedLegal G μ) (z : Root → ℝ) (w : V → ℝ)
    (hz : ∀ r, 0 ≤ z r) {ell : ℝ} (hell : 0 ≤ ell)
    (hblocks : ∀ b : Fin 2, (κ : ℝ) * ell ≤ ownerBlockWeight z b) :
    (κ : ℝ) * ell * incompleteSquares (G := G) (μ := μ) w ≤
      ownerEnergy (G := G) (μ := μ) z w := by
  have hmissing := incompleteSquares_le_missing (G := G) (μ := μ) w
  have hsum : (κ : ℝ) * ell *
      (missingOwnerSquares (G := G) (μ := μ) 0 w + missingOwnerSquares (G := G) (μ := μ) 1 w) ≤
      ∑ b : Fin 2, ownerBlockWeight z b * missingOwnerSquares (G := G) (μ := μ) b w := by
    rw [Fin.sum_univ_two, mul_add]
    exact add_le_add
      (mul_le_mul_of_nonneg_right (hblocks 0) (missingOwnerSquares_nonneg 0 w))
      (mul_le_mul_of_nonneg_right (hblocks 1) (missingOwnerSquares_nonneg 1 w))
  exact (mul_le_mul_of_nonneg_left hmissing (mul_nonneg (Nat.cast_nonneg κ) hell)).trans
    (hsum.trans (ownerEnergy_blocks_bound h z w hz))

theorem ownerEnergy_sixteen (h : RootedLegal G μ) (z : Root → ℝ) (w : V → ℝ)
    (hz : ∀ r, 0 ≤ z r) {ell c : ℝ} (hell : 0 ≤ ell)
    (hblocks : ∀ b : Fin 2, (κ : ℝ) * ell ≤ ownerBlockWeight z b)
    (hc : c ≤ (M : ℝ) * ell / 2) :
    16 * c * incompleteSquares (G := G) (μ := μ) w ≤
      ownerEnergy (G := G) (μ := μ) z w := by
  have hk : (κ : ℝ) = 8 * (M : ℝ) := by norm_num [κ, M]
  have hcoef : 16 * c ≤ (κ : ℝ) * ell := by rw [hk]; linarith
  exact (mul_le_mul_of_nonneg_right hcoef (incompleteSquares_nonneg w)).trans
    (ownerEnergy_penalty h z w hz hell hblocks)

end TranscendentalTuran.Source
