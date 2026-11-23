module

public import TranscendentalTuran.Network.ActualReduction

@[expose] public section

/-!
# The source correction for an actual rooted host

Formalization author and responsible maintainer: Xizhi Liu.

The localized root interval gives both positive conductances and enough
owner penalty to pay for every private leaf. The resulting source gain uses
only actual rooted legality, nonnegative data weights, and that interval.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network Parameters
open scoped BigOperators
attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

theorem matchingBlockWeight_lower (z : Root → ℝ) {ell : ℝ}
    (hz : ∀ r, ell ≤ z r) (b : Fin 4) : (M : ℝ) * ell ≤ matchingBlockWeight z b := by
  calc
    (M : ℝ) * ell = ∑ _j : Fin M, ell := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _ => hz (matchingRoot b j)

theorem matchingBlockWeight_upper (z : Root → ℝ) {u : ℝ}
    (hz : ∀ r, z r ≤ u) (b : Fin 4) : matchingBlockWeight z b ≤ (M : ℝ) * u := by
  calc
    matchingBlockWeight z b ≤ ∑ _j : Fin M, u := Finset.sum_le_sum fun j _ => hz (matchingRoot b j)
    _ = _ := by simp

theorem ownerBlockWeight_lower (z : Root → ℝ) {ell : ℝ}
    (hz : ∀ r, ell ≤ z r) (b : Fin 2) : (κ : ℝ) * ell ≤ ownerBlockWeight z b := by
  calc
    (κ : ℝ) * ell = ∑ _j : Fin κ, ell := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _ => hz (ownershipRoot b j)

theorem root_interval_conductance (z : Root → ℝ) {ell : ℝ} (hell : 0 < ell)
    (hz : ∀ r, ell ≤ z r ∧ z r ≤ 2 * ell) :
    (∀ b, 0 < matchingBlockWeight z b) ∧
      conductance (matchingBlockWeight z) ≤ (M : ℝ) * ell / 2 := by
  have hM : (0 : ℝ) < M := by exact_mod_cast M_pos
  have hW : ∀ b, 0 < matchingBlockWeight z b := fun b =>
    (mul_pos hM hell).trans_le (matchingBlockWeight_lower z (fun r => (hz r).1) b)
  refine ⟨hW, ?_⟩
  have hh := conductance_le_quarter_upper hW
    (mul_pos hM (mul_pos (by norm_num) hell))
    (matchingBlockWeight_upper z (fun r => (hz r).2))
  convert hh using 1 <;> ring

theorem actual_marked_source_gain (h : RootedLegal G μ) {m : V} (hm : Marked G μ m)
    (z : Root → ℝ) (w : V → ℝ) (hw : ∀ x, 0 ≤ w x)
    {ell J : ℝ} (hell : 0 < ell) (hz : ∀ r, ell ≤ z r ∧ z r ≤ 2 * ell) :
    J * w m - actualEnergy (G := G) (μ := μ) z w / 2 ≤
      J ^ 2 * Green.cornerGreen / (2 * conductance (matchingBlockWeight z)) := by
  have hz0 : ∀ r, 0 ≤ z r := fun r => hell.le.trans (hz r).1
  obtain ⟨hW, hc⟩ := root_interval_conductance z hell hz
  have hmatching := matching_energy_reduction h z w hz0 hw hW
  have howner := ownerEnergy_sixteen h z w hz0 hell.le
    (ownerBlockWeight_lower z (fun r => (hz r).1)) hc
  rw [actualEnergy_split]
  exact marked_source_gain h hm w (conductance_pos hW) hmatching howner

/-- The unmarked case is included explicitly, using nonnegativity of the
actual energy. The single mark is supplied by its actual ordinary witness. -/
theorem actual_source_gain (h : RootedLegal G μ) (z : Root → ℝ) (w : V → ℝ)
    (hw : ∀ x, 0 ≤ w x) {ell J a : ℝ} (hell : 0 < ell)
    (hz : ∀ r, ell ≤ z r ∧ z r ≤ 2 * ell)
    (ha : a = 0 ∨ ∃ m, Marked G μ m ∧ a = w m) :
    J * a - actualEnergy (G := G) (μ := μ) z w / 2 ≤
      J ^ 2 * Green.cornerGreen / (2 * conductance (matchingBlockWeight z)) := by
  rcases ha with rfl | ⟨m, hm, rfl⟩
  · have hE := actualEnergy_nonneg (G := G) (μ := μ) z w
      (fun r => hell.le.trans (hz r).1)
    have hc := conductance_pos (root_interval_conductance z hell hz).1
    have hgain : 0 ≤ J ^ 2 * Green.cornerGreen / (2 * conductance (matchingBlockWeight z)) :=
      div_nonneg (mul_nonneg (sq_nonneg J) (le_trans (by norm_num) Green.quarter_le_cornerGreen)) (by positivity)
    nlinarith
  · exact actual_marked_source_gain h hm z w hw hell hz

end TranscendentalTuran.Source
