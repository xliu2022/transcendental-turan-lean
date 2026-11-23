module

public import TranscendentalTuran.Network.RootedSourceGain

@[expose] public section

/-!
# Source gain under the six block-mean hypotheses

Formalization author and responsible maintainer: Xizhi Liu.

The manuscript's source-gain lemma bounds the six block means, not each
individual layer weight. This module proves that version directly from the
actual matching reduction and ownership penalty. Individual layer weights
may be zero or exceed twice the common lower bound.

The weights are represented by the ambient root function `z`. Nonnegativity
is stated on all roots, as in the ordinary weighted-host context; the energy
and block means use only layer roots. Any nonnegative family of layer weights
can be represented in this context by assigning zero to the other roots.

Proof adaptation: the matching reduction uses a weighted composition
inequality for finite partial bijections instead of enumerating full chains
and stubs separately. The defect records missing endpoints, so the exact
grounding terms and the four-resistor coefficient are preserved.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network Parameters
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : RGraph V 3} {μ : Rooting Root V}

/-- The mean of the actual root weights in a matching block. -/
noncomputable def matchingBlockMean (z : Root → ℝ) (b : Fin 4) : ℝ :=
  matchingBlockWeight z b / (M : ℝ)

/-- The mean of the actual root weights in an ownership block. -/
noncomputable def ownerBlockMean (z : Root → ℝ) (b : Fin 2) : ℝ :=
  ownerBlockWeight z b / (κ : ℝ)

/-- Exactly the six block-mean interval conditions from the manuscript. -/
def SixBlockMeanBounds (z : Root → ℝ) (ell : ℝ) : Prop :=
  (∀ b : Fin 4, ell ≤ matchingBlockMean z b ∧ matchingBlockMean z b ≤ 2 * ell) ∧
  (∀ b : Fin 2, ell ≤ ownerBlockMean z b ∧ ownerBlockMean z b ≤ 2 * ell)

theorem matchingBlockWeight_bounds_of_means (z : Root → ℝ) {ell : ℝ}
    (hmean : SixBlockMeanBounds z ell) (b : Fin 4) :
    (M : ℝ) * ell ≤ matchingBlockWeight z b ∧
      matchingBlockWeight z b ≤ (M : ℝ) * (2 * ell) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast M_pos
  have hm := hmean.1 b
  change ell ≤ matchingBlockWeight z b / (M : ℝ) ∧
    matchingBlockWeight z b / (M : ℝ) ≤ 2 * ell at hm
  constructor
  · simpa only [mul_comm] using (le_div_iff₀ hM).mp hm.1
  · simpa only [mul_comm] using (div_le_iff₀ hM).mp hm.2

theorem ownerBlockWeight_lower_of_means (z : Root → ℝ) {ell : ℝ}
    (hmean : SixBlockMeanBounds z ell) (b : Fin 2) :
    (κ : ℝ) * ell ≤ ownerBlockWeight z b := by
  have hκ : (0 : ℝ) < κ := by exact_mod_cast κ_pos
  have hm := (hmean.2 b).1
  change ell ≤ ownerBlockWeight z b / (κ : ℝ) at hm
  simpa only [mul_comm] using (le_div_iff₀ hκ).mp hm

/-- The four matching means imply positive conductances and the upper
conductance bound needed to compare with the ownership penalty. -/
theorem block_means_conductance (z : Root → ℝ) {ell : ℝ} (hell : 0 < ell)
    (hmean : SixBlockMeanBounds z ell) :
    (∀ b, 0 < matchingBlockWeight z b) ∧
      conductance (matchingBlockWeight z) ≤ (M : ℝ) * ell / 2 := by
  have hM : (0 : ℝ) < M := by exact_mod_cast M_pos
  have hW : ∀ b, 0 < matchingBlockWeight z b := fun b =>
    (mul_pos hM hell).trans_le (matchingBlockWeight_bounds_of_means z hmean b).1
  refine ⟨hW, ?_⟩
  have hh := conductance_le_quarter_upper hW
    (mul_pos hM (mul_pos (by norm_num) hell))
    (fun b => (matchingBlockWeight_bounds_of_means z hmean b).2)
  convert hh using 1 <;> ring

/-- The marked source-gain inequality with only block-mean interval bounds.
It also holds for negative `J`, although the manuscript only needs `J ≥ 0`. -/
theorem actual_marked_source_gain_of_block_means (h : RootedLegal G μ)
    {m : V} (hm : Marked G μ m) (z : Root → ℝ) (w : V → ℝ)
    (hz : ∀ r, 0 ≤ z r) (hw : ∀ x, 0 ≤ w x)
    {ell J : ℝ} (hell : 0 < ell) (hmean : SixBlockMeanBounds z ell) :
    J * w m - actualEnergy (G := G) (μ := μ) z w / 2 ≤
      J ^ 2 * Green.cornerGreen / (2 * conductance (matchingBlockWeight z)) := by
  obtain ⟨hW, hc⟩ := block_means_conductance z hell hmean
  have hmatching := matching_energy_reduction h z w hz hw hW
  have howner := ownerEnergy_sixteen h z w hz hell.le
    (ownerBlockWeight_lower_of_means z hmean) hc
  rw [actualEnergy_split]
  exact marked_source_gain h hm w (conductance_pos hW) hmatching howner

/-- The six-block-mean source-gain bound, including hosts with no mark and
marks lacking either ownership incidence. -/
theorem actual_source_gain_of_block_means (h : RootedLegal G μ)
    (z : Root → ℝ) (w : V → ℝ) (hz : ∀ r, 0 ≤ z r) (hw : ∀ x, 0 ≤ w x)
    {ell J a : ℝ} (hell : 0 < ell) (hmean : SixBlockMeanBounds z ell)
    (ha : a = 0 ∨ ∃ m, Marked G μ m ∧ a = w m) :
    J * a - actualEnergy (G := G) (μ := μ) z w / 2 ≤
      J ^ 2 * Green.cornerGreen / (2 * conductance (matchingBlockWeight z)) := by
  rcases ha with rfl | ⟨m, hm, rfl⟩
  · have hE := actualEnergy_nonneg (G := G) (μ := μ) z w hz
    have hc := conductance_pos (block_means_conductance z hell hmean).1
    have hgain : 0 ≤ J ^ 2 * Green.cornerGreen /
        (2 * conductance (matchingBlockWeight z)) :=
      div_nonneg
        (mul_nonneg (sq_nonneg J) (le_trans (by norm_num) Green.quarter_le_cornerGreen))
        (by positivity)
    nlinarith
  · exact actual_marked_source_gain_of_block_means h hm z w hz hw hell hmean

/-- Write the conductance form as the exact resistance expression used in
the manuscript. This identity has no positivity hypotheses. -/
theorem source_correction_eq_resistance (z : Root → ℝ) (J g : ℝ) :
    J ^ 2 * g / (2 * conductance (matchingBlockWeight z)) =
      J ^ 2 * g * resistance (matchingBlockWeight z) / 2 := by
  simp only [conductance, one_div, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- The manuscript's upper source-gain conclusion `Ja - E/2 ≤ J²gR/2`
under its six block-mean hypotheses. -/
theorem source_gain_block_means (h : RootedLegal G μ)
    (z : Root → ℝ) (w : V → ℝ) (hz : ∀ r, 0 ≤ z r) (hw : ∀ x, 0 ≤ w x)
    {ell J a : ℝ} (hell : 0 < ell) (hmean : SixBlockMeanBounds z ell)
    (ha : a = 0 ∨ ∃ m, Marked G μ m ∧ a = w m) :
    J * a - actualEnergy (G := G) (μ := μ) z w / 2 ≤
      J ^ 2 * Green.cornerGreen * resistance (matchingBlockWeight z) / 2 := by
  have hh := actual_source_gain_of_block_means h z w hz hw (J := J) hell hmean ha
  rwa [source_correction_eq_resistance] at hh

end TranscendentalTuran.Source
