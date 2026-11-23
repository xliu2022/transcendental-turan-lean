module

public import TranscendentalTuran.Network.Series
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Four conductances and their effective series coefficient

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Network

open scoped BigOperators

noncomputable def resistance (W : Fin 4 → ℝ) : ℝ := ∑ b, 1 / W b
noncomputable def conductance (W : Fin 4 → ℝ) : ℝ := 1 / resistance W

theorem resistance_pos {W : Fin 4 → ℝ} (hW : ∀ b, 0 < W b) : 0 < resistance W :=
  Finset.sum_pos (fun b _ => one_div_pos.mpr (hW b)) Finset.univ_nonempty

theorem conductance_pos {W : Fin 4 → ℝ} (hW : ∀ b, 0 < W b) : 0 < conductance W :=
  one_div_pos.mpr (resistance_pos hW)

theorem conductance_le_weight {W : Fin 4 → ℝ} (hW : ∀ b, 0 < W b) (b : Fin 4) :
    conductance W ≤ W b := by
  have hs : 1 / W b ≤ resistance W := by
    apply Finset.single_le_sum (s := Finset.univ) (a := b) (f := fun i => 1 / W i)
    · exact fun i _ => (one_div_pos.mpr (hW i)).le
    · exact Finset.mem_univ _
  have hh := one_div_le_one_div_of_le (one_div_pos.mpr (hW b)) hs
  simpa only [conductance, one_div_one_div] using hh

theorem conductance_le_quarter_upper {W : Fin 4 → ℝ} (hW : ∀ b, 0 < W b)
    {a : ℝ} (ha : 0 < a) (hWa : ∀ b, W b ≤ a) : conductance W ≤ a / 4 := by
  have hs : 4 / a ≤ resistance W := by
    calc
      4 / a = ∑ _b : Fin 4, 1 / a := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun b _ => one_div_le_one_div_of_le (hW b) (hWa b)
  have hh := one_div_le_one_div_of_le (div_pos (by norm_num) ha) hs
  unfold conductance
  convert hh using 1 <;> field_simp

theorem four_series_bound {W : Fin 4 → ℝ} (hW : ∀ b, 0 < W b)
    (v : Fin 5 → ℝ) :
    conductance W * (v 0 - v 4) ^ 2 ≤
      ∑ b : Fin 4, W b * (v b.castSucc - v b.succ) ^ 2 := by
  have h := series_reduction Finset.univ W
    (fun b : Fin 4 => v b.castSucc - v b.succ) (fun b _ => hW b)
  have hs : (∑ b : Fin 4, (v b.castSucc - v b.succ)) = v 0 - v 4 := by
    rw [Fin.sum_univ_four]
    change (v 0 - v 1) + (v 1 - v 2) + (v 2 - v 3) + (v 3 - v 4) = _
    ring
  rw [hs] at h
  simpa only [conductance, resistance, div_eq_mul_inv, one_mul, mul_comm] using h

end TranscendentalTuran.Network
