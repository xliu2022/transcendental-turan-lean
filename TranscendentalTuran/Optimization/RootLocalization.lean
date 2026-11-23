module

public import TranscendentalTuran.Optimization.ElementaryIdentities
public import TranscendentalTuran.Optimization.Domain
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The real inequalities in root localization

Formalization author and responsible maintainer: Xizhi Liu.

The graph-specific bridge supplies two estimates: the data-link bound
and the one-sided transfer bound between extreme root weights. This
module proves their precise numerical consequences. These intermediate
lemmas do not assert either estimate for an arbitrary hypergraph.
-/

namespace TranscendentalTuran.Optimization.RootLocalization

open Finset

noncomputable def cliqueProbability (q : ℝ) : ℝ := 1 - 3 / q + 2 / q ^ 2

theorem cliqueProbability_gt_seven_eighths {q : ℝ} (hq : 64 ≤ q) :
    7 / 8 < cliqueProbability q := by
  have hq0 : 0 < q := by linarith
  have hi0 : 0 < 1 / q := by positivity
  have hi : 1 / q ≤ (1 / 64 : ℝ) := by
    apply (div_le_div_iff₀ hq0 (by norm_num)).2
    linarith
  have he : cliqueProbability q = 1 - 3 * (1 / q) + 2 * (1 / q) ^ 2 := by
    unfold cliqueProbability
    field_simp [ne_of_gt hq0] <;> ring
  rw [he]
  nlinarith

theorem cliqueProbability_gt_square {q : ℝ} (hq : 64 ≤ q) :
    (1 - 2 / q) ^ 2 < cliqueProbability q := by
  have hq0 : 0 < q := by linarith
  have hi0 : 0 < 1 / q := by positivity
  have hi : 1 / q ≤ (1 / 64 : ℝ) := by
    apply (div_le_div_iff₀ hq0 (by norm_num)).2
    linarith
  have he : cliqueProbability q - (1 - 2 / q) ^ 2 =
      1 / q - 2 * (1 / q) ^ 2 := by
    unfold cliqueProbability
    field_simp [ne_of_gt hq0] <;> ring
  have hp : 0 < (1 / q) * (1 - 2 * (1 / q)) :=
    mul_pos hi0 (by linarith)
  nlinarith

/-- The maximum-coordinate estimate can be obtained without introducing
a square root once the link derivative has been identified. -/
theorem coordinate_lt_two_div {q w : ℝ} (hq : 64 ≤ q)
    (hw : w ≤ 1) (hlink : cliqueProbability q ≤ (1 - w) ^ 2) :
    w < 2 / q := by
  have hq0 : 0 < q := by linarith
  have hsmall : 2 / q ≤ (1 / 32 : ℝ) := by
    apply (div_le_div_iff₀ hq0 (by norm_num)).2
    nlinarith
  have hp := cliqueProbability_gt_square hq
  by_contra hh
  push_neg at hh
  have hle : 1 - w ≤ 1 - 2 / q := by linarith
  have hs := mul_le_mul hle hle (by linarith : 0 ≤ 1 - w)
    (by linarith : 0 ≤ 1 - 2 / q)
  nlinarith

/-- The data-link estimate forces total normalized data mass at most
`2/q`. The case of zero data mass is included explicitly. -/
theorem data_ratio_le_two_div {q s t η : ℝ} (hq : 64 ≤ q)
    (hs : 0 < s) (ht : 0 ≤ t) (hst : s + t = 1) (hη : η < 1 / 8)
    (hdata : 0 < t → cliqueProbability q ≤ (1 - 1 / q) * s ^ 2 + 2 * η * t) :
    t / s ≤ 2 / q := by
  have hq0 : 0 < q := by linarith
  have hi0 : 0 < 1 / q := by positivity
  by_cases ht0 : t = 0
  · rw [ht0, zero_div]
    positivity
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let x := t / s
  have hx : 0 ≤ x := div_nonneg ht hs.le
  have hp := cliqueProbability_gt_seven_eighths hq
  have hscale := mul_le_mul_of_nonneg_right (hdata htp) (sq_nonneg (1 + x))
  have he : ((1 - 1 / q) * s ^ 2 + 2 * η * t) * (1 + x) ^ 2 =
      (1 - 1 / q) * (s + t) ^ 2 + 2 * η * x * (s + t) * (1 + x) := by
    dsimp [x]
    field_simp [ne_of_gt hs] <;> ring
  rw [he, hst] at hscale
  have hnum : 1 - 1 / q - cliqueProbability q = 2 * (1 - 1 / q) / q := by
    unfold cliqueProbability
    field_simp [ne_of_gt hq0] <;> ring
  have hpoly : (cliqueProbability q - 2 * η) * x ^ 2 +
      2 * (cliqueProbability q - η) * x ≤ 2 * (1 - 1 / q) / q := by
    nlinarith
  have hcoef0 : 0 ≤ cliqueProbability q - 2 * η := by linarith
  have hcoef1 : (3 / 2 : ℝ) ≤ 2 * (cliqueProbability q - η) := by linarith
  have hfirst := mul_nonneg hcoef0 (sq_nonneg x)
  have hsecond := mul_le_mul_of_nonneg_right hcoef1 hx
  have hright : 2 * (1 - 1 / q) / q ≤ 2 / q := by
    apply div_le_div_of_nonneg_right _ hq0.le
    linarith
  change x ≤ 2 / q
  linarith

/-- Quantitative consequence of transferring mass from a heaviest root
to a lightest root. -/
theorem root_diameter_le {q s t a b : ℝ} (hq : 64 ≤ q)
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b < 2 / q) (htq : t ≤ 2 * s / q)
    (htransfer : (b - a) * (1 - a - b) ≤ t * b + t ^ 2 / 2) :
    b - a ≤ 12 * s / q ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq0
  have hb0 : 0 ≤ b := ha.trans hab
  have hsmall : 2 / q ≤ (1 / 32 : ℝ) := by
    apply (div_le_div_iff₀ hq0 (by norm_num)).2
    nlinarith
  have hhalf : (1 / 2 : ℝ) ≤ 1 - a - b := by linarith
  have hD := mul_le_mul_of_nonneg_left hhalf (sub_nonneg.mpr hab)
  have htupper0 : 0 ≤ 2 * s / q := by positivity
  have hprod : t * b ≤ 4 * (s / q ^ 2) := by
    calc
      t * b ≤ (2 * s / q) * (2 / q) := mul_le_mul htq hb.le hb0 htupper0
      _ = _ := by field_simp [ne_of_gt hq0] <;> ring
  have hsq : t ^ 2 ≤ 4 * (s / q ^ 2) := by
    have hss : s ^ 2 ≤ s := by nlinarith
    calc
      t ^ 2 ≤ (2 * s / q) ^ 2 := by
        simpa only [pow_two] using mul_le_mul htq htq ht htupper0
      _ = 4 * (s ^ 2 / q ^ 2) := by field_simp [ne_of_gt hq0] <;> ring
      _ ≤ 4 * (s / q ^ 2) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hss hq2.le) (by norm_num)
  have he : 12 * s / q ^ 2 = 12 * (s / q ^ 2) := by ring
  rw [he]
  nlinarith

/-- A small diameter around a positive total root mass gives the precise
coordinate box used by the finite optimization. -/
theorem normalized_root_box {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ)
    {s a b : ℝ} (hs : 0 < s) (hsum : ∑ i, r i = s)
    (hr : ∀ i, a ≤ r i ∧ r i ≤ b)
    (hdiameter : b - a ≤ 12 * s / (n : ℝ) ^ 2) :
    ∀ i, 1 / (n : ℝ) - 16 / (n : ℝ) ^ 2 ≤ r i / s ∧
      r i / s ≤ 1 / (n : ℝ) + 16 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmeanlo : a ≤ s / (n : ℝ) := by
    apply (le_div_iff₀ hn0).2
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) => (hr i).1)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      hsum, mul_comm] using h
  have hmeanhi : s / (n : ℝ) ≤ b := by
    apply (div_le_iff₀ hn0).2
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) => (hr i).2)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      hsum, mul_comm] using h
  have hmargin : 12 * s / (n : ℝ) ^ 2 ≤ 16 * s / (n : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg (n : ℝ))
  intro i
  have hlo := (hr i).1
  have hhi := (hr i).2
  constructor
  · apply (le_div_iff₀ hs).2
    have he : (1 / (n : ℝ) - 16 / (n : ℝ) ^ 2) * s =
        s / (n : ℝ) - 16 * s / (n : ℝ) ^ 2 := by ring
    rw [he]
    linarith
  · apply (div_le_iff₀ hs).2
    have he : (1 / (n : ℝ) + 16 / (n : ℝ) ^ 2) * s =
        s / (n : ℝ) + 16 * s / (n : ℝ) ^ 2 := by ring
    rw [he]
    linarith

end TranscendentalTuran.Optimization.RootLocalization
