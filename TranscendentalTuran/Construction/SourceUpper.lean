module

public import TranscendentalTuran.Construction.LocalizedCoordinates
public import TranscendentalTuran.Construction.TypedUpper
public import TranscendentalTuran.Construction.TypeCompletion
public import TranscendentalTuran.Construction.SourceBasis
public import TranscendentalTuran.Core.Basic

@[expose] public section

/-!
# The source-class variational upper bound

Formalization author and responsible maintainer: Xizhi Liu.

An arbitrary legal partial-rooted graph is completed. Its actual finite
maximum is localized, normalized, and changed to an all-declared legal host
by finitely many nondecreasing surgeries. The proved atomic and energy bounds
then compare its value with the manuscript's explicit finite objective.
-/

namespace TranscendentalTuran.Source.RootData

open TuranUniversality Encoding Network Parameters
open scoped BigOperators
attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem completed_maximizer_le_Ψ (G : RGraph (Root ⊕ D) 3) (hG : Completed G)
    (z : Root → ℝ) (w : D → ℝ) (hx : ProbabilityWeights (Sum.elim z w))
    (hmax : ∀ v, ProbabilityWeights v → G.edgePolynomial v ≤ G.edgePolynomial (Sum.elim z w)) :
    G.edgePolynomial (Sum.elim z w) ≤ Optimization.Paper.Ψ Green.cornerGreen := by
  classical
  have hloc := maximizer_localized G hG z w hx hmax
  have hz : ∀ r, 0 ≤ normalizedRoots z r :=
    normalizedRoots_nonneg z (fun r => hx.1 (Sum.inl r))
  have hw : ∀ d, 0 ≤ normalizedData z w d :=
    normalizedData_nonneg z w hloc.1.le (fun d => hx.1 (Sum.inr d))
  have hbudget : TypeSurgery.DeclarationBudget (normalizedRoots z) (normalizedData z w) :=
    maximizer_declaration_gain G hG z w hx hmax
  obtain ⟨H, hH, htyped, hpoly⟩ := TypeSurgery.exists_all_declared G hG
    (normalizedRoots z) (normalizedData z w) hz hw hbudget
  choose τ hτ using htyped
  have hdom : Optimization.Paper.sourceCoordinates (normalizedRoots z)
      (typeMass τ (normalizedData z w)) ∈ Optimization.rootTypeDomain q := by
    exact maximizer_normalized_domain G hG z w hx hmax _
      (typeMass_nonneg τ (normalizedData z w) hw) (by rw [sum_typeMass])
  have hupper := typed_polynomial_le_Ψ H hH.legal τ hτ
    (normalizedRoots z) (normalizedData z w) hw hdom
  have hden : 0 ≤ (1 + ∑ d, normalizedData z w d) ^ 3 := by
    have ht : 0 ≤ ∑ d, normalizedData z w d := Finset.sum_nonneg fun d _ => hw d
    positivity
  calc
    _ = G.edgePolynomial (Sum.elim (normalizedRoots z) (normalizedData z w)) /
        (1 + ∑ d, normalizedData z w d) ^ 3 :=
      (probability_root_normalization G z w hx hloc.1).symm
    _ ≤ H.edgePolynomial (Sum.elim (normalizedRoots z) (normalizedData z w)) /
        (1 + ∑ d, normalizedData z w d) ^ 3 := div_le_div_of_nonneg_right hpoly hden
    _ ≤ _ := hupper

theorem completed_lambda_le_Ψ (G : RGraph (Root ⊕ D) 3) (hG : Completed G) :
    lambda G ≤ Optimization.Paper.Ψ Green.cornerGreen := by
  letI : Nonempty Root := ⟨⟨0, q_pos⟩⟩
  obtain ⟨x, hx, he⟩ := exists_lambda_maximizer G
  let z : Root → ℝ := fun r => x (Sum.inl r)
  let w : D → ℝ := fun d => x (Sum.inr d)
  have hsplit : Sum.elim z w = x := by funext v; cases v <;> rfl
  have hp : ProbabilityWeights (Sum.elim z w) := hsplit.symm ▸ hx
  have hmax : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ G.edgePolynomial (Sum.elim z w) := by
    intro y hy
    rw [hsplit, he]
    exact edgePolynomial_le_lambda G y hy
  have hh := completed_maximizer_le_Ψ G hG z w hp hmax
  rwa [hsplit, he] at hh

end TranscendentalTuran.Source.RootData

namespace TranscendentalTuran.Source

open TuranUniversality Encoding
attribute [local irreducible] Parameters.q Parameters.N

theorem admissible_lambda_le_Ψ {V : Type} [Fintype V] [DecidableEq V]
    (G : RGraph V 3) (hG : Admissible G) :
    lambda G ≤ Optimization.Paper.Ψ Green.cornerGreen := by
  classical
  obtain ⟨μ, hμ⟩ := hG
  have hlag := (Completion.vertexMap_embedding G μ).isHom.lagrangian_le
  have hlambda : lambda G ≤ lambda (Completion.graph G μ) :=
    div_le_div_of_nonneg_right hlag (by norm_num)
  exact hlambda.trans (RootData.completed_lambda_le_Ψ (Completion.graph G μ)
    (RootData.completion_completed G μ hμ))

theorem Ψ_cornerGreen_nonneg : 0 ≤ Optimization.Paper.Ψ Green.cornerGreen := by
  let G : RGraph (Fin 0) 3 := ⟨∅, by intro e he; exact False.elim (Finset.notMem_empty e he)⟩
  exact (lambda_nonneg G).trans (admissible_lambda_le_Ψ G (edgeless_admissible G rfl))

theorem classLambda_le_Ψ : classLambda finiteClass ≤ Optimization.Paper.Ψ Green.cornerGreen := by
  apply (classLambda_le_iff finiteClass Ψ_cornerGreen_nonneg).mpr
  intro G hG
  exact admissible_lambda_le_Ψ G.2 hG

end TranscendentalTuran.Source
