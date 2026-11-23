module

public import TranscendentalTuran.Optimization.SourceObjective
public import TranscendentalTuran.Network.RootedSourceGain

@[expose] public section

/-!
# The actual typed-host upper bound

Formalization author and responsible maintainer: Xizhi Liu.

The ordinary polynomial estimate and the proved source-energy correction
are identified with the exact free-root rational objective.
-/

namespace TranscendentalTuran.Source.RootData

open TuranUniversality TuranUniversality.Weighted Encoding Network Parameters
open scoped BigOperators
attribute [local irreducible] Parameters.q Parameters.N
attribute [local instance] Classical.propDecidable
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem markedMass_cases (G : RGraph (Root ⊕ D) 3) (hG : RootedLegal G (sumRooting D))
    (w : D → ℝ) :
    markedMass G w = 0 ∨
      ∃ m, Marked G (sumRooting D) m ∧ markedMass G w = dataWeights w m := by
  by_cases hm : ∃ d, Marked G (sumRooting D) (Sum.inr d)
  · obtain ⟨d, hd⟩ := hm
    have hi (e : D) : Marked G (sumRooting D) (Sum.inr e) ↔ e = d := by
      constructor
      · intro he
        exact Sum.inr.inj (hG.marks_unique _ _ he hd)
      · rintro rfl; exact hd
    exact Or.inr ⟨Sum.inr d, hd, by simp only [markedMass, hi, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, dataWeights, Sum.elim_inr]⟩
  · left
    have hn (d : D) : ¬ Marked G (sumRooting D) (Sum.inr d) := fun hd => hm ⟨d, hd⟩
    simp only [markedMass, hn, ite_false, Finset.sum_const_zero]

theorem source_correction_eq (z : Root → ℝ) (g : ℝ) :
    markerWeight z ^ 2 * g / (2 * conductance (matchingBlockWeight z)) =
      markerWeight z ^ 2 * g * (∑ b : Fin 4, (∑ j : Fin M, z (matchingRoot b j))⁻¹) / 2 := by
  simp only [conductance, resistance, matchingBlockWeight, one_div, div_eq_mul_inv,
    mul_inv_rev, inv_inv]
  ring

theorem typed_polynomial_le_Ψ (G : RGraph (Root ⊕ D) 3)
    (hG : RootedLegal G (sumRooting D)) (τ : D → PhysicalType)
    (ht : ∀ d, Declared G (sumRooting D) (τ d) (Sum.inr d))
    (z : Root → ℝ) (w : D → ℝ) (hw : ∀ d, 0 ≤ w d)
    (hz : Optimization.Paper.sourceCoordinates z (typeMass τ w) ∈ Optimization.rootTypeDomain q) :
    G.edgePolynomial (Sum.elim z w) / (1 + ∑ d, w d) ^ 3 ≤
      Optimization.Paper.Ψ Green.cornerGreen := by
  have hell : (0 : ℝ) < 15 / (16 * (q : ℝ)) := by
    have hq : (0 : ℝ) < q := by exact_mod_cast q_pos
    positivity
  have hcompare : (17 : ℝ) / (16 * (q : ℝ)) ≤ 2 * (15 / (16 * (q : ℝ))) := by
    rw [q_value]
    norm_num
  have hroot (r : Root) : 15 / (16 * (q : ℝ)) ≤ z r ∧
      z r ≤ 2 * (15 / (16 * (q : ℝ))) := by
    have hh := Optimization.Paper.root_soft_bounds hz r
    exact ⟨hh.1, hh.2.trans hcompare⟩
  have hz0 : ∀ r, 0 ≤ z r := fun r => hell.le.trans (hroot r).1
  have hw0 : ∀ v, 0 ≤ dataWeights w v := by
    intro v
    cases v with
    | inl r => exact le_rfl
    | inr d => exact hw d
  have hgain := actual_source_gain hG z (dataWeights w) hw0
    (J := markerWeight z) hell hroot (markedMass_cases G hG w)
  rw [source_correction_eq] at hgain
  have hatomic := atomic_polynomial_bound G hG τ ht z w hz0 hw
  have hF : G.edgePolynomial (Sum.elim z w) ≤ elementary Finset.univ z 3 +
      (∑ ν, typeMass τ w ν * pairWeight (allowedPairs ν) z) +
      typedQuadratic z (typeMass τ w) + markerWeight z ^ 2 * Green.cornerGreen *
        (∑ b : Fin 4, (∑ j : Fin M, z (matchingRoot b j))⁻¹) / 2 := by
    linarith
  have hh := Optimization.Paper.source_expression_le_Ψ Green.cornerGreen hz hF
  rwa [sum_typeMass] at hh

end TranscendentalTuran.Source.RootData
