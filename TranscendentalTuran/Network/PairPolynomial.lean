module

public import TuranUniversality.Density.WeightedHom
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! # Double counting the weighted edges of an actual pair graph

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Network

open TuranUniversality TuranUniversality.Density
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pairGraph_hom_iff (G : RGraph V 2) (f : Fin 2 → V) :
    (RGraph.oneEdge 2).IsHom G f ↔ {f 0, f 1} ∈ G.edges := by
  have he : (Finset.univ : Finset (Fin 2)).image f = {f 0, f 1} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Fin.exists_fin_two,
      Finset.mem_insert, Finset.mem_singleton, eq_comm]
  simp [RGraph.IsHom, RGraph.oneEdge, he]

/-- The ordered pair sum counts every ordinary edge exactly twice. -/
theorem pairGraph_ordered_sum (G : RGraph V 2) (w : V → ℝ) :
    2 * G.edgePolynomial w =
      ∑ x, ∑ y, if {x, y} ∈ G.edges then w x * w y else 0 := by
  classical
  have h := G.weightedHomDensity_oneEdge w
  norm_num only [Nat.factorial, Nat.cast_ofNat] at h
  rw [← h, RGraph.weightedHomDensity, weightedMean]
  calc
    _ = ∑ p : V × V, if {p.1, p.2} ∈ G.edges then w p.1 * w p.2 else 0 := by
      apply Fintype.sum_equiv (finTwoArrowEquiv V)
      intro f
      simp only [productWeight, Fin.prod_univ_two, RGraph.homIndicator,
        pairGraph_hom_iff, finTwoArrowEquiv_apply, mul_ite, mul_one, mul_zero]
      rfl
    _ = _ := Fintype.sum_prod_type _

end TranscendentalTuran.Network
