module

public import TranscendentalTuran.Network.MarkedComponent
public import TranscendentalTuran.Green.FiniteNetwork.SourceGain

@[expose] public section

/-!
# Source gain for an actual marked base

Formalization author and responsible maintainer: Xizhi Liu.

The complete case uses the actual private-leaf coordinate projection. In the
incomplete case the owner penalty alone bounds the marked square. Thus no
completeness condition on the marked vertex is added to the source class.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network Green Green.FiniteNetwork
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

theorem incomplete_square_le (x : BaseVertex G μ)
    (hx : ¬ IsComplete (G := G) (μ := μ) x.val) (w : V → ℝ) :
    w x.val ^ 2 ≤ incompleteSquares (G := G) (μ := μ) w := by
  classical
  unfold incompleteSquares
  have hs := Finset.single_le_sum
    (s := Finset.univ) (a := x)
    (f := fun y : BaseVertex G μ =>
      if ¬ IsComplete (G := G) (μ := μ) y.val then w y.val ^ 2 else 0)
    (fun y _ => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl)
    (Finset.mem_univ x)
  rw [if_pos hx] at hs
  exact hs

theorem complete_marked_source_gain (h : RootedLegal G μ) {p : OwnedBase G μ}
    (hm : Marked G μ p.vertex) (w : V → ℝ) {J c E : ℝ} (hc : 0 < c)
    (hE : c * ((baseNetwork h).energy (fun x => w x.val) +
      12 * incompleteSquares (G := G) (μ := μ) w) ≤ E) :
    J * w p.vertex - E / 2 ≤ J ^ 2 * cornerGreen / (2 * c) := by
  have he : c * (privateNetwork h p).energy (privateWeight h p w) ≤ E :=
    (mul_le_mul_of_nonneg_left (privateNetwork_energy_le h p w) hc.le).trans hE
  exact (privateNetwork h p).source_gain_of_energy (privateProjection h hm)
    (privateWeight h p w) hc he

/-- This theorem handles both complete and incomplete marks. Its two energy
hypotheses are precisely the actual matching reduction and actual owner
penalty proved separately from the ordinary local rules. -/
theorem marked_source_gain (h : RootedLegal G μ) {m : V} (hm : Marked G μ m)
    (w : V → ℝ) {J c matchingE ownerE : ℝ} (hc : 0 < c)
    (hmatching : c * (baseNetwork h).energy (fun x => w x.val) ≤ matchingE)
    (howner : 16 * c * incompleteSquares (G := G) (μ := μ) w ≤ ownerE) :
    J * w m - (matchingE + ownerE) / 2 ≤ J ^ 2 * cornerGreen / (2 * c) := by
  classical
  let x : BaseVertex G μ := ⟨m, marked_declared hm⟩
  have hinc := incompleteSquares_nonneg (G := G) (μ := μ) w
  have hmatch0 : 0 ≤ matchingE :=
    (mul_nonneg hc.le ((baseNetwork h).energy_nonneg _)).trans hmatching
  by_cases hx : IsComplete (G := G) (μ := μ) m
  · let p : OwnedBase G μ := ownedOfComplete x hx
    have hp : p.vertex = m := rfl
    have hpen : 12 * c * incompleteSquares (G := G) (μ := μ) w ≤ ownerE := by
      nlinarith [mul_nonneg hc.le hinc]
    apply complete_marked_source_gain h (p := p) (hp.symm ▸ hm) w hc
    nlinarith
  · have hs := incomplete_square_le x hx w
    have he : 16 * c * w m ^ 2 ≤ matchingE + ownerE := by
      have ht := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 16 * c)
      change 16 * c * w m ^ 2 ≤ 16 * c * incompleteSquares (G := G) (μ := μ) w at ht
      linarith
    have hE0 : 0 ≤ matchingE + ownerE :=
      (mul_nonneg (by positivity) (sq_nonneg (w m))).trans he
    have hg := mul_le_mul_of_nonneg_right quarter_le_cornerGreen hE0
    have hscalar : c * w m ^ 2 ≤ cornerGreen * (matchingE + ownerE) := by
      nlinarith [mul_nonneg hc.le (sq_nonneg (w m))]
    exact Green.source_gain_bound hc
      (lt_of_lt_of_le (by norm_num) quarter_le_cornerGreen) hscalar

end TranscendentalTuran.Source
