/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Hypergraph.LagrangianHom
public import TuranUniversality.Density.Extremal
public import TuranUniversality.Density.FamilyExtremal

/-!
# Ordinary finite three-graphs and the manuscript's normalization

This project reuses the finite simple hypergraphs of `TuranUniversality`.
`RGraph.IsEmbedding` requires global injectivity and preserves edges; it is
ordinary, not induced, containment. `RGraph.IsHom` only preserves edges.
The reused `turanDensity` is defined from actual ordinary extremal numbers,
and `extremalDensity_tendsto` proves that it is their binomial-normalized limit.

The earlier project's `RGraph.lagrangian` is normalized by `r!`. The present
manuscript uses the unnormalized edge polynomial, so `lambda` divides by six.
-/

@[expose] public section

namespace TranscendentalTuran

open TuranUniversality

universe u

abbrev ThreeGraph (V : Type u) [DecidableEq V] := RGraph V 3
abbrev FiniteThreeGraph := FiniteGraph 3
abbrev GraphClass := FiniteThreeGraph → Prop

noncomputable def lambda {V : Type u} [DecidableEq V] [Fintype V]
    (G : ThreeGraph V) : ℝ := G.lagrangian / 6

theorem lambda_nonneg {V : Type u} [DecidableEq V] [Fintype V]
    (G : ThreeGraph V) : 0 ≤ lambda G :=
  div_nonneg G.lagrangian_nonneg (by norm_num)

theorem lambda_le_one_sixth {V : Type u} [DecidableEq V] [Fintype V]
    (G : ThreeGraph V) : lambda G ≤ 1 / 6 :=
  div_le_div_of_nonneg_right G.lagrangian_le_one (by norm_num)

@[simp] theorem six_mul_lambda {V : Type u} [DecidableEq V] [Fintype V]
    (G : ThreeGraph V) : 6 * lambda G = G.lagrangian := by
  unfold lambda
  ring

theorem edgePolynomial_le_lambda {V : Type u} [DecidableEq V] [Fintype V]
    (G : ThreeGraph V) (x : V → ℝ) (hx : ProbabilityWeights x) :
    G.edgePolynomial x ≤ lambda G := by
  have h := G.normalizedPolynomial_le_lagrangian x hx
  norm_num [Nat.factorial] at h
  unfold lambda
  linarith

theorem lambda_le_iff {V : Type u} [DecidableEq V] [Fintype V]
    (G : ThreeGraph V) {a : ℝ} (ha : 0 ≤ a) :
    lambda G ≤ a ↔ ∀ x : V → ℝ, ProbabilityWeights x → G.edgePolynomial x ≤ a := by
  constructor
  · intro h x hx
    exact (edgePolynomial_le_lambda G x hx).trans h
  · intro h
    have hG : G.lagrangian ≤ 6 * a := by
      apply (G.lagrangian_le_iff (by positivity)).mpr
      intro x hx
      have hx' := h x hx
      norm_num [Nat.factorial]
      linarith
    unfold lambda
    linarith

theorem exists_lambda_maximizer {V : Type u} [DecidableEq V] [Fintype V]
    [Nonempty V] (G : ThreeGraph V) :
    ∃ x : V → ℝ, ProbabilityWeights x ∧ G.edgePolynomial x = lambda G := by
  obtain ⟨x, hx, heq⟩ := G.exists_lagrangian_maximizer
  refine ⟨x, hx, ?_⟩
  norm_num [Nat.factorial] at heq
  unfold lambda
  linarith

/-- Ordinary avoidance, including injectivity on isolated forbidden vertices. -/
def forbiddenClass (A : Finset FiniteThreeGraph) : GraphClass :=
  fun G => familyFree A G.2

/-- The zero convention also makes the supremum meaningful for an empty class. -/
def classLambdaValues (C : GraphClass) : Set ℝ :=
  insert 0 {a | ∃ G : FiniteThreeGraph, C G ∧ a = lambda G.2}

noncomputable def classLambda (C : GraphClass) : ℝ := sSup (classLambdaValues C)

theorem classLambdaValues_nonempty (C : GraphClass) :
    (classLambdaValues C).Nonempty := ⟨0, Or.inl rfl⟩

theorem classLambdaValues_bddAbove (C : GraphClass) :
    BddAbove (classLambdaValues C) := by
  refine ⟨1 / 6, ?_⟩
  rintro a (rfl | ⟨G, _, rfl⟩)
  · norm_num
  · exact lambda_le_one_sixth G.2

theorem classLambda_nonneg (C : GraphClass) : 0 ≤ classLambda C :=
  le_csSup (classLambdaValues_bddAbove C) (Or.inl rfl)

theorem classLambda_le_one_sixth (C : GraphClass) : classLambda C ≤ 1 / 6 := by
  apply csSup_le (classLambdaValues_nonempty C)
  rintro a (rfl | ⟨G, _, rfl⟩)
  · norm_num
  · exact lambda_le_one_sixth G.2

theorem lambda_le_classLambda (C : GraphClass) (G : FiniteThreeGraph) (hG : C G) :
    lambda G.2 ≤ classLambda C :=
  le_csSup (classLambdaValues_bddAbove C) (Or.inr ⟨G, hG, rfl⟩)

theorem classLambda_le_iff (C : GraphClass) {a : ℝ} (ha : 0 ≤ a) :
    classLambda C ≤ a ↔ ∀ G : FiniteThreeGraph, C G → lambda G.2 ≤ a := by
  constructor
  · intro h G hG
    exact (lambda_le_classLambda C G hG).trans h
  · intro h
    apply csSup_le (classLambdaValues_nonempty C)
    rintro a' (rfl | ⟨G, hG, rfl⟩)
    · exact ha
    · exact h G hG

theorem edgePolynomial_le_classLambda (C : GraphClass) {n : ℕ}
    (G : ThreeGraph (Fin n)) (hG : C ⟨n, G⟩) (x : Fin n → ℝ)
    (hx : ProbabilityWeights x) : G.edgePolynomial x ≤ classLambda C :=
  (edgePolynomial_le_lambda G x hx).trans (lambda_le_classLambda C ⟨n, G⟩ hG)

theorem classLambda_mono {C D : GraphClass} (h : ∀ G, C G → D G) :
    classLambda C ≤ classLambda D := by
  apply (classLambda_le_iff C (classLambda_nonneg D)).mpr
  intro G hG
  exact lambda_le_classLambda D G (h G hG)

theorem classLambda_union (C D : GraphClass) :
    classLambda (fun G => C G ∨ D G) = max (classLambda C) (classLambda D) := by
  apply le_antisymm
  · apply (classLambda_le_iff _ (le_trans (classLambda_nonneg C) (le_max_left _ _))).mpr
    intro G hG
    rcases hG with hG | hG
    · exact (lambda_le_classLambda C G hG).trans (le_max_left _ _)
    · exact (lambda_le_classLambda D G hG).trans (le_max_right _ _)
  · exact max_le (classLambda_mono (fun _ h => Or.inl h))
      (classLambda_mono (fun _ h => Or.inr h))

end TranscendentalTuran
