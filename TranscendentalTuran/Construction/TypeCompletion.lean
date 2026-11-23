module

public import TranscendentalTuran.Construction.TypeSurgeryWeights

@[expose] public section

namespace TranscendentalTuran.Source.TypeSurgery

open TuranUniversality TuranUniversality.Weighted Encoding Network RootData
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

noncomputable section

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem declaredMass_nonneg (G : RGraph (Root ⊕ D) 3) (w : D → ℝ)
    (hw : ∀ d, 0 ≤ w d) (τ : PhysicalType) : 0 ≤ declaredMass G w τ :=
  Finset.sum_nonneg (fun d _ => hw d)

theorem sum_declaredMass_le (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (w : D → ℝ) (hw : ∀ d, 0 ≤ w d) :
    (∑ τ : PhysicalType, declaredMass G w τ) ≤ ∑ d, w d := by
  classical
  unfold declaredMass
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro d _
  by_cases hd : ∃ τ, Declared G (sumRooting D) τ (Sum.inr d)
  · obtain ⟨τ, hτ⟩ := hd
    have hiff (σ : PhysicalType) : Declared G (sumRooting D) σ (Sum.inr d) ↔ σ = τ := by
      constructor
      · exact fun hσ => hG.declarations_unique _ _ _ hσ hτ
      · rintro rfl; exact hτ
    simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, ite_true, le_refl]
  · have hn (τ : PhysicalType) : ¬ Declared G (sumRooting D) τ (Sum.inr d) :=
      fun hτ => hd ⟨τ, hτ⟩
    simpa only [hn, ite_false, Finset.sum_const_zero] using hw d

theorem exists_small_declaredMass (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (w : D → ℝ) (hw : ∀ d, 0 ≤ w d) :
    ∃ τ : PhysicalType, declaredMass G w τ ≤ (∑ d, w d) / 7 := by
  classical
  obtain ⟨τ, _, hτ⟩ := Finset.exists_min_image Finset.univ (declaredMass G w)
    (show (Finset.univ : Finset PhysicalType).Nonempty from ⟨.base, Finset.mem_univ _⟩)
  refine ⟨τ, ?_⟩
  have hsum : 7 * declaredMass G w τ ≤ ∑ σ : PhysicalType, declaredMass G w σ := by
    calc
      7 * declaredMass G w τ = ∑ _σ : PhysicalType, declaredMass G w τ := by
        simp only [Finset.sum_const, Finset.card_univ, type_card, nsmul_eq_mul, Nat.cast_ofNat]
      _ ≤ _ := Finset.sum_le_sum (fun σ hσ => hτ σ hσ)
  have := sum_declaredMass_le G hG w hw
  linarith

/-- The scalar inequality needed for declaration surgery. Its coefficients
are the actual root weights and its data mass is unchanged by surgery. -/
noncomputable def DeclarationBudget (z : Root → ℝ) (w : D → ℝ) : Prop :=
  ∀ ν : Fin 7,
    ((∑ j : Fin Parameters.N, z (genericRoot j)) / 7 +
      (∑ r : Layer, z (layerRoot r))) * (∑ d, w d) ≤ declaringWeight z ν

theorem exists_nondecreasing_declaration (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (a : D) (hu : Undeclared G a) (z : Root → ℝ) (w : D → ℝ)
    (hz : ∀ r, 0 ≤ z r) (hw : ∀ d, 0 ≤ w d) (hb : DeclarationBudget z w) :
    ∃ τ : PhysicalType,
      G.edgePolynomial (Sum.elim z w) ≤ (graph G a τ).edgePolynomial (Sum.elim z w) := by
  obtain ⟨τ, hτ⟩ := exists_small_declaredMass G hG.legal w hw
  refine ⟨τ, ?_⟩
  have hω : 0 ≤ ∑ j : Fin Parameters.N, z (genericRoot j) := Finset.sum_nonneg (fun j _ => hz _)
  have hm := mul_le_mul_of_nonneg_left hτ hω
  have hbudget := hb (physicalIndex τ)
  have hgain := polynomial_gain G hG a hu τ z w hz hw
  have hcoef : 0 ≤ declaringWeight z (physicalIndex τ) -
      (∑ r : Layer, z (layerRoot r)) * (∑ d, w d) -
      (∑ j : Fin Parameters.N, z (genericRoot j)) * declaredMass G w τ := by
    nlinarith
  exact le_trans (le_add_of_nonneg_right (mul_nonneg (hw a) hcoef)) hgain

noncomputable def undeclaredVertices (G : RGraph (Root ⊕ D) 3) : Finset D := by
  classical
  exact Finset.univ.filter (Undeclared G)

theorem undeclared_graph_iff (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType) (d : D) :
    Undeclared (graph G a τ) d ↔ Undeclared G d ∧ d ≠ a := by
  constructor
  · intro h
    refine ⟨fun σ hσ => h σ ((graph_declared G a τ σ d).mpr (Or.inl hσ)), ?_⟩
    intro hda
    exact h τ ((graph_declared G a τ τ d).mpr (Or.inr ⟨hda, rfl⟩))
  · rintro ⟨h, hda⟩ σ hσ
    rcases (graph_declared G a τ σ d).mp hσ with hold | hnew
    · exact h σ hold
    · exact hda hnew.1

theorem undeclaredVertices_graph (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType) :
    undeclaredVertices (graph G a τ) = (undeclaredVertices G).erase a := by
  classical
  ext d
  simp only [undeclaredVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, undeclared_graph_iff, and_comm]

/-- Every completed legal weighted host satisfying the localized declaration
budget can be changed on the same finite vertex set into an all-declared
legal host, without decreasing its actual graph polynomial. -/
theorem exists_all_declared (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (z : Root → ℝ) (w : D → ℝ) (hz : ∀ r, 0 ≤ z r) (hw : ∀ d, 0 ≤ w d)
    (hb : DeclarationBudget z w) :
    ∃ H : RGraph (Root ⊕ D) 3, Completed H ∧
      (∀ d : D, ∃ τ : PhysicalType, Declared H (sumRooting D) τ (Sum.inr d)) ∧
      G.edgePolynomial (Sum.elim z w) ≤ H.edgePolynomial (Sum.elim z w) := by
  classical
  have aux : ∀ n : ℕ, ∀ G : RGraph (Root ⊕ D) 3,
      (undeclaredVertices G).card = n → Completed G →
      ∃ H : RGraph (Root ⊕ D) 3, Completed H ∧
        (∀ d : D, ∃ τ : PhysicalType, Declared H (sumRooting D) τ (Sum.inr d)) ∧
        G.edgePolynomial (Sum.elim z w) ≤ H.edgePolynomial (Sum.elim z w) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hc hG
      by_cases hempty : undeclaredVertices G = ∅
      · refine ⟨G, hG, ?_, le_refl _⟩
        intro d
        by_contra hd
        have hu : Undeclared G d := fun τ hτ => hd ⟨τ, hτ⟩
        have hm : d ∈ undeclaredVertices G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
        rw [hempty] at hm
        exact Finset.notMem_empty _ hm
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hu : Undeclared G a := (Finset.mem_filter.mp ha).2
        obtain ⟨τ, hgain⟩ := exists_nondecreasing_declaration G hG a hu z w hz hw hb
        have hlt : (undeclaredVertices (graph G a τ)).card < n := by
          rw [undeclaredVertices_graph, ← hc]
          exact Finset.card_erase_lt_of_mem ha
        obtain ⟨H, hH, ht, hpoly⟩ := ih _ hlt (graph G a τ) rfl (completed G a τ hG hu)
        exact ⟨H, hH, ht, hgain.trans hpoly⟩
  exact aux _ G rfl hG

end
end TranscendentalTuran.Source.TypeSurgery
