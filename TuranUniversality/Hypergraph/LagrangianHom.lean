module

public import TuranUniversality.Hypergraph.Lagrangian
public import TuranUniversality.Density.WeightedHomPushforward
public import TuranUniversality.Density.FamilyLower

@[expose] public section

/-! # Actual finite Lagrangians under homomorphisms and forbidden families -/

namespace TuranUniversality.RGraph

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
  [Fintype V] [Fintype W] {r : ℕ}

theorem IsHom.lagrangian_le {G : RGraph V r} {H : RGraph W r} {f : V → W}
    (hf : G.IsHom H f) : G.lagrangian ≤ H.lagrangian := by
  apply (G.lagrangian_le_iff H.lagrangian_nonneg).mpr
  intro x hx
  exact (mul_le_mul_of_nonneg_left (G.edgePolynomial_le_pushforward H f hf x hx.1)
    (Nat.cast_nonneg r.factorial)).trans
    (H.normalizedPolynomial_le_lagrangian _ (Density.pushforwardWeight_probability f x hx))

theorem lagrangian_le_one (G : RGraph V r) : G.lagrangian ≤ 1 := by
  apply (G.lagrangian_le_iff zero_le_one).mpr
  intro x hx
  rw [← G.weightedHomDensity_oneEdge]
  exact (oneEdge r).weightedHomDensity_le_one G x hx

theorem lagrangian_le_familyTuranDensity (F : Finset (FiniteGraph r))
    (G : RGraph V r) (hG : familyHomFree F G) : G.lagrangian ≤ familyTuranDensity F := by
  apply (G.lagrangian_le_iff (familyTuranDensity_nonneg F)).mpr
  exact fun x hx => familyTuranDensity_lower_of_homFree F G hG x hx

end TuranUniversality.RGraph
