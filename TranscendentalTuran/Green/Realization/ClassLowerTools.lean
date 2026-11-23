/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Core.Basic
public import TranscendentalTuran.Construction.SourceBasis
public import TuranUniversality.Density.WeightedHomPushforward
public import TuranUniversality.Hypergraph.Labeled
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

noncomputable section

open scoped BigOperators

namespace TranscendentalTuran.Green.Realization

open TuranUniversality Source

/-- Relabel an arbitrary finite admissible host to the canonical finite-graph
universe used by the class supremum. -/
theorem polynomial_le_source_classLambda {V : Type*} [Fintype V] [DecidableEq V]
    (G : RGraph V 3) (hG : Admissible G) (x : V → ℝ) (hx : ProbabilityWeights x) :
    G.edgePolynomial x ≤ classLambda finiteClass := by
  let F := FiniteGraph.ofRGraph G
  have hF : finiteClass F := admissible_of_embedding (FiniteGraph.ofRGraph_embedding G) hG
  have hp := Density.pushforwardWeight_probability (Fintype.equivFin V) x hx
  have he := G.edgePolynomial_le_pushforward F.2 (Fintype.equivFin V)
    (FiniteGraph.embedding_ofRGraph G).isHom x hx.1
  exact he.trans (edgePolynomial_le_classLambda finiteClass F.2 hF _ hp)

theorem edgePolynomial_div {V : Type*} [DecidableEq V] (G : RGraph V 3)
    (x : V → ℝ) (c : ℝ) :
    G.edgePolynomial (fun v => x v / c) = G.edgePolynomial x / c ^ 3 := by
  unfold RGraph.edgePolynomial
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.prod_div_distrib, Finset.prod_const, G.uniform e he]

/-- Unnormalized nonnegative weights give a lower bound after division by their
actual total mass cubed. -/
theorem normalized_polynomial_le_source_classLambda {V : Type*} [Fintype V] [DecidableEq V]
    (G : RGraph V 3) (hG : Admissible G) (x : V → ℝ) {c : ℝ}
    (hx : ∀ v, 0 ≤ x v) (hc : 0 < c) (hs : ∑ v, x v = c) :
    G.edgePolynomial x / c ^ 3 ≤ classLambda finiteClass := by
  have hp : ProbabilityWeights (fun v => x v / c) := by
    refine ⟨fun v => div_nonneg (hx v) hc.le, ?_⟩
    rw [← Finset.sum_div, hs, div_self hc.ne']
  simpa only [edgePolynomial_div] using polynomial_le_source_classLambda G hG _ hp

end TranscendentalTuran.Green.Realization
