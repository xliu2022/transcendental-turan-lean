/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TranscendentalTuran.Core.Basic
public import TuranUniversality.Density.ProductUpper
public import TuranUniversality.Density.FamilyLower
public import TuranUniversality.Hypergraph.GuardedBasis

/-!
# Proved ordinary-density transfers

These are generic transfer theorems, not the final theorem for the manuscript's
source class. Their hypotheses state explicitly the source-class avoidance
and weighted bounds that the network and factor-recovery arguments must prove.

The reused `pairExtension` supplies a private edge for every core pair, rather
than only uncovered pairs. This finite construction variant has the same two
properties needed here: core pair coverage and extension of a core embedding
into a pair-covered host. Both properties have proofs in the reused library.

The ordinary-density upper and lower bridges are proved by finite sampling in
the reused modules. Thus these statements need no assumption identifying an
ordinary Turán density with a differently defined homomorphism density.
-/

@[expose] public section

namespace TranscendentalTuran.Transfer

open TuranUniversality

/-- Every real weighting in a homomorphism-free source class gives a lower
bound on the ordinary Turán density of the single forbidden graph. -/
theorem classLambda_lower_of_homFree (P : FiniteThreeGraph) (C : GraphClass)
    (hfree : ∀ G : FiniteThreeGraph, C G → P.2.HomFree G.2) :
    6 * classLambda C ≤ turanDensity P.2 := by
  have hπ : 0 ≤ turanDensity P.2 := by
    simpa using familyTuranDensity_nonneg ({P} : Finset FiniteThreeGraph)
  have hbound : classLambda C ≤ turanDensity P.2 / 6 := by
    apply (classLambda_le_iff C (div_nonneg hπ (by norm_num))).mpr
    intro G hG
    apply (lambda_le_iff G.2 (div_nonneg hπ (by norm_num))).mpr
    intro x hx
    have h := turanDensity_lower_weighted_of_homFree P.2 G.2 (hfree G hG) x hx
    norm_num [Nat.factorial] at h
    linarith
  linarith

/-- The product upper bound in exactly the manuscript's unnormalized
Lagrangian convention. Containment in `forbiddenClass` is ordinary. -/
theorem singletonProduct_turanDensity_upper (A : Finset FiniteThreeGraph)
    (hA : A.Nonempty) (hedges : ∀ B ∈ A, B.2.edges.Nonempty) :
    turanDensity (FiniteGraph.singletonProduct A).2 ≤
      6 * classLambda (forbiddenClass A) := by
  classical
  letI : Nonempty A := ⟨⟨hA.choose, hA.choose_spec⟩⟩
  apply product_turanDensity_upper (fun B : A => B.val.2)
    (fun B => hedges B.val B.property) _ (by
      exact mul_nonneg (by norm_num) (classLambda_nonneg _))
  intro n G x hx hfree
  have hG : forbiddenClass A ⟨n, G⟩ := by
    intro B hB
    exact hfree ⟨B, hB⟩
  exact mul_le_mul_of_nonneg_left
    (edgePolynomial_le_classLambda (forbiddenClass A) G hG x hx) (by norm_num)

/-- A precise assembly theorem. Its two substantive hypotheses remain
visible: the core-free weighted bound and the source homomorphism exclusion. -/
theorem singletonProduct_realizes_class (A : Finset FiniteThreeGraph)
    (hA : A.Nonempty) (hedges : ∀ B ∈ A, B.2.edges.Nonempty)
    (C : GraphClass)
    (hbound : classLambda (forbiddenClass A) ≤ classLambda C)
    (hfree : ∀ G : FiniteThreeGraph, C G →
      (FiniteGraph.singletonProduct A).2.HomFree G.2) :
    turanDensity (FiniteGraph.singletonProduct A).2 = 6 * classLambda C := by
  apply le_antisymm
  · exact (singletonProduct_turanDensity_upper A hA hedges).trans
      (mul_le_mul_of_nonneg_left hbound (by norm_num))
  · exact classLambda_lower_of_homFree (FiniteGraph.singletonProduct A) C hfree

/-- The guard union changes no weighted maximum when its separate branch
has a no larger maximum. This is the exact supremum step in the paper. -/
theorem guard_union_classLambda (C D : GraphClass)
    (hD : classLambda D ≤ classLambda C) :
    classLambda (fun G => C G ∨ D G) = classLambda C := by
  rw [classLambda_union, max_eq_left hD]

end TranscendentalTuran.Transfer
