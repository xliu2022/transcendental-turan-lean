module

public import TranscendentalTuran.Optimization.PaperObjective
public import TranscendentalTuran.Optimization.ElementaryIdentities

@[expose] public section

/-!
# Uniform bounds on the manuscript's root domain

Formalization author and responsible maintainer: Xizhi Liu.

Every estimate uses the actual free root coordinates in `rootTypeDomain`.
The roots are not replaced by their common average.
-/

namespace TranscendentalTuran.Optimization.Paper

open Set Finset MvPolynomial Parameters Encoding
open TuranUniversality.Algebraicity

theorem q_pos_real : (0 : ℝ) < q := by exact_mod_cast q_pos

theorem q_ge_256 : 256 ≤ q := by rw [q_value]; norm_num

theorem root_soft_bounds {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) (r : Root) :
    15 / (16 * (q : ℝ)) ≤ z (Sum.inl r) ∧
      z (Sum.inl r) ≤ 17 / (16 * (q : ℝ)) := by
  have hr := hz.1 r
  have hlo : (15 : ℝ) / (16 * q) ≤ 1 / q - 16 / (q : ℝ) ^ 2 := by
    rw [q_value]; norm_num
  have hhi : (1 : ℝ) / q + 16 / (q : ℝ) ^ 2 ≤ 17 / (16 * q) := by
    rw [q_value]; norm_num
  exact ⟨hlo.trans hr.1, hr.2.trans hhi⟩

theorem root_le_two_div_q {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) (r : Root) :
    z (Sum.inl r) ≤ 2 / (q : ℝ) :=
  (rootTypeDomain_coordinate_bounds q_ge_64 hz (Sum.inl r)).2

theorem rootElementary_eval (z : Coord → ℝ) (k : ℕ) :
    qeval (rootElementary k) z = elementary (fun r : Root => z (Sum.inl r)) k := by
  rw [elementary_eq_sum]
  simp only [rootElementary, qeval_sum, qeval_prod, rootVar, qeval_X]

theorem root_sum_sq_upper {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    (∑ r : Root, z (Sum.inl r) ^ 2) ≤ 2 / (q : ℝ) := by
  calc
    (∑ r : Root, z (Sum.inl r) ^ 2) ≤
        ∑ r : Root, (2 / (q : ℝ)) * z (Sum.inl r) := by
      apply Finset.sum_le_sum
      intro r _
      have h := mul_le_mul_of_nonneg_right (root_le_two_div_q hz r) (root_pos hz r).le
      simpa only [pow_two] using h
    _ = 2 / (q : ℝ) := by rw [← Finset.mul_sum, hz.2.1, mul_one]

theorem root_sum_sq_lower {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    1 / (q : ℝ) ≤ ∑ r : Root, z (Sum.inl r) ^ 2 := by
  have hnn : 0 ≤ ∑ r : Root, (z (Sum.inl r) - 1 / (q : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun r _ => sq_nonneg _)
  have he : (∑ r : Root, (z (Sum.inl r) - 1 / (q : ℝ)) ^ 2) =
      (∑ r : Root, z (Sum.inl r) ^ 2) - 1 / (q : ℝ) := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hz.2.1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt q_pos_real]
    ring
  rw [he] at hnn
  linarith

theorem root_sum_cube_upper {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    (∑ r : Root, z (Sum.inl r) ^ 3) ≤
      (2 / (q : ℝ)) * ∑ r : Root, z (Sum.inl r) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have h := mul_le_mul_of_nonneg_right (root_le_two_div_q hz r)
    (sq_nonneg (z (Sum.inl r)))
  nlinarith

theorem e2_bounds {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    1 / 2 - 1 / (q : ℝ) ≤ qeval (rootElementary 2) z ∧
      qeval (rootElementary 2) z ≤ 1 / 2 := by
  have hid := two_mul_elementary_two (fun r : Root => z (Sum.inl r))
  rw [hz.2.1, ← rootElementary_eval] at hid
  have hu := root_sum_sq_upper hz
  have hn : 0 ≤ ∑ r : Root, z (Sum.inl r) ^ 2 :=
    Finset.sum_nonneg (fun r _ => sq_nonneg _)
  have he : 2 / (q : ℝ) = 2 * (1 / (q : ℝ)) := by ring
  rw [he] at hu
  constructor <;> nlinarith

theorem e2_sub_three_e3_lower {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    1 / (q : ℝ) - 2 / (q : ℝ) ^ 2 ≤
      qeval (rootElementary 2) z - 3 * qeval (rootElementary 3) z := by
  rw [rootElementary_eval, rootElementary_eval, elementary_two_sub_three hz.2.1]
  have hs := root_sum_sq_lower hz
  have hc := root_sum_cube_upper hz
  have hf : 0 ≤ 1 - 2 / (q : ℝ) := by rw [q_value]; norm_num
  have hh := mul_le_mul_of_nonneg_left hs hf
  have he : (1 - 2 / (q : ℝ)) * (1 / q) = 1 / q - 2 / (q : ℝ) ^ 2 := by
    field_simp [ne_of_gt q_pos_real] <;> ring
  rw [he] at hh
  nlinarith

theorem genericWeight_bounds {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    1 / 40 ≤ qeval genericWeight z ∧ qeval genericWeight z ≤ 1 / 24 := by
  simp only [genericWeight, qeval_sum, rootVar, qeval_X]
  have hlo : (N : ℝ) * (15 / (16 * (q : ℝ))) ≤
      ∑ j : Fin N, z (Sum.inl (genericRoot j)) := by
    calc
      (N : ℝ) * (15 / (16 * (q : ℝ))) = ∑ _j : Fin N, (15 / (16 * (q : ℝ))) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => (root_soft_bounds hz (genericRoot j)).1)
  have hhi : (∑ j : Fin N, z (Sum.inl (genericRoot j))) ≤
      (N : ℝ) * (17 / (16 * (q : ℝ))) := by
    calc
      _ ≤ ∑ _j : Fin N, (17 / (16 * (q : ℝ))) :=
        Finset.sum_le_sum (fun j _ => (root_soft_bounds hz (genericRoot j)).2)
      _ = _ := by simp
  constructor
  · apply le_trans _ hlo
    rw [N_value, q_value]; norm_num
  · apply le_trans hhi
    rw [N_value, q_value]; norm_num

theorem markerWeight_bounds {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    1 / (2 * (q : ℝ) ^ 2) ≤ qeval markerWeight z ∧
      qeval markerWeight z ≤ 2 / (q : ℝ) ^ 2 := by
  simp only [markerWeight, qeval_mul, rootVar, qeval_X]
  have ha := root_soft_bounds hz markerLeft
  have hb := root_soft_bounds hz markerRight
  have hl : 0 ≤ (15 : ℝ) / (16 * q) := by positivity
  have hu : 0 ≤ (17 : ℝ) / (16 * q) := by positivity
  have hlo := mul_le_mul ha.1 hb.1 hl (root_pos hz markerLeft).le
  have hhi := mul_le_mul ha.2 hb.2 (root_pos hz markerRight).le hu
  constructor
  · apply le_trans _ hlo
    rw [q_value]; norm_num
  · apply le_trans hhi
    rw [q_value]; norm_num

theorem declaringWeight_bounds {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (ν : Fin 7) :
    1 / (40 * (q : ℝ)) ≤ qeval (declaringWeight ν) z ∧
      qeval (declaringWeight ν) z ≤ 1 / (24 * (q : ℝ)) := by
  have hl : (0 : ℝ) ≤ 15 / (16 * (q : ℝ)) :=
    div_nonneg (by norm_num) (mul_nonneg (by norm_num) q_pos_real.le)
  have hu : (0 : ℝ) ≤ 17 / (16 * (q : ℝ)) :=
    div_nonneg (by norm_num) (mul_nonneg (by norm_num) q_pos_real.le)
  simp only [declaringWeight, qeval_sum, qeval_mul, rootVar, qeval_X]
  have hlo : (N : ℝ) * (15 / (16 * (q : ℝ))) ^ 2 ≤
      ∑ j : Fin N, z (Sum.inl (declaringRoot ((ν, j), 0))) *
        z (Sum.inl (declaringRoot ((ν, j), 1))) := by
    calc
      _ = ∑ _j : Fin N, (15 / (16 * (q : ℝ))) ^ 2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [pow_two] using mul_le_mul
          (root_soft_bounds hz (declaringRoot ((ν, j), 0))).1
          (root_soft_bounds hz (declaringRoot ((ν, j), 1))).1
          hl (root_pos hz _).le
  have hhi : (∑ j : Fin N, z (Sum.inl (declaringRoot ((ν, j), 0))) *
        z (Sum.inl (declaringRoot ((ν, j), 1)))) ≤
      (N : ℝ) * (17 / (16 * (q : ℝ))) ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin N, (17 / (16 * (q : ℝ))) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [pow_two] using mul_le_mul
          (root_soft_bounds hz (declaringRoot ((ν, j), 0))).2
          (root_soft_bounds hz (declaringRoot ((ν, j), 1))).2
          (root_pos hz _).le hu
      _ = _ := by simp
  constructor
  · apply le_trans _ hlo
    rw [N_value, q_value]; norm_num
  · apply le_trans hhi
    rw [N_value, q_value]; norm_num

theorem declaringWeight_sharp_bounds {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (ν : Fin 7) :
    (N : ℝ) * (1 / q - 16 / (q : ℝ) ^ 2) ^ 2 ≤ qeval (declaringWeight ν) z ∧
      qeval (declaringWeight ν) z ≤ (N : ℝ) * (1 / q + 16 / (q : ℝ) ^ 2) ^ 2 := by
  have hlo : 0 ≤ 1 / (q : ℝ) - 16 / (q : ℝ) ^ 2 := by rw [q_value]; norm_num
  have hhi : 0 ≤ 1 / (q : ℝ) + 16 / (q : ℝ) ^ 2 := by positivity
  simp only [declaringWeight, qeval_sum, qeval_mul, rootVar, qeval_X]
  constructor
  · calc
      _ = ∑ _j : Fin N, (1 / q - 16 / (q : ℝ) ^ 2) ^ 2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [pow_two] using mul_le_mul
          (hz.1 (declaringRoot ((ν, j), 0))).1
          (hz.1 (declaringRoot ((ν, j), 1))).1 hlo (root_pos hz _).le
  · calc
      _ ≤ ∑ _j : Fin N, (1 / q + 16 / (q : ℝ) ^ 2) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [pow_two] using mul_le_mul
          (hz.1 (declaringRoot ((ν, j), 0))).2
          (hz.1 (declaringRoot ((ν, j), 1))).2 (root_pos hz _).le hhi
      _ = _ := by simp

theorem declaringWeight_difference_bound {z : Coord → ℝ}
    (hz : z ∈ rootTypeDomain q) (ν μ : Fin 7) :
    qeval (declaringWeight ν) z - qeval (declaringWeight μ) z ≤
      64 * (N : ℝ) / (q : ℝ) ^ 3 := by
  have hν := (declaringWeight_sharp_bounds hz ν).2
  have hμ := (declaringWeight_sharp_bounds hz μ).1
  have he : (N : ℝ) * (1 / q + 16 / (q : ℝ) ^ 2) ^ 2 -
      (N : ℝ) * (1 / q - 16 / (q : ℝ) ^ 2) ^ 2 = 64 * N / (q : ℝ) ^ 3 := by
    field_simp [ne_of_gt q_pos_real]
    ring
  linarith

theorem declaringWeight_difference_lt {z : Coord → ℝ}
    (hz : z ∈ rootTypeDomain q) (ν μ : Fin 7) :
    qeval (declaringWeight ν) z - qeval (declaringWeight μ) z < 2 / (q : ℝ) ^ 2 := by
  apply lt_of_le_of_lt (declaringWeight_difference_bound hz ν μ)
  rw [N_value, q_value]; norm_num

noncomputable def specialWeight (z : Coord → ℝ) : ℝ :=
  (∑ b : Fin 4, qeval (matchingWeight b) z) +
    ∑ b : Fin 2, qeval (ownershipWeight b) z

theorem ownershipWeight_pos {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (b : Fin 2) : 0 < qeval (ownershipWeight b) z := by
  simp only [ownershipWeight, qeval_sum, rootVar, qeval_X]
  exact Finset.sum_pos (fun j _ => root_pos hz (ownershipRoot b j))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, κ_pos⟩⟩)

theorem matchingWeight_lower {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (b : Fin 4) : 3 * (M : ℝ) / (4 * (q : ℝ)) ≤ qeval (matchingWeight b) z := by
  simp only [matchingWeight, qeval_sum, rootVar, qeval_X]
  calc
    _ ≤ ∑ _j : Fin M, 15 / (16 * (q : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [M_value, q_value]; norm_num
    _ ≤ _ := Finset.sum_le_sum (fun j _ => (root_soft_bounds hz (matchingRoot b j)).1)

theorem matchingWeight_upper {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (b : Fin 4) : qeval (matchingWeight b) z ≤ 2 * (M : ℝ) / q := by
  simp only [matchingWeight, qeval_sum, rootVar, qeval_X]
  calc
    _ ≤ ∑ _j : Fin M, 2 / (q : ℝ) :=
      Finset.sum_le_sum (fun j _ => root_le_two_div_q hz (matchingRoot b j))
    _ = _ := by simp; ring

theorem ownershipWeight_upper {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (b : Fin 2) : qeval (ownershipWeight b) z ≤ 2 * (κ : ℝ) / q := by
  simp only [ownershipWeight, qeval_sum, rootVar, qeval_X]
  calc
    _ ≤ ∑ _j : Fin κ, 2 / (q : ℝ) :=
      Finset.sum_le_sum (fun j _ => root_le_two_div_q hz (ownershipRoot b j))
    _ = _ := by simp; ring

theorem specialWeight_bounds {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    0 ≤ specialWeight z ∧ specialWeight z ≤ 2 * (K : ℝ) / q := by
  constructor
  · exact add_nonneg
      (Finset.sum_nonneg (fun b _ => (matchingWeight_pos hz b).le))
      (Finset.sum_nonneg (fun b _ => (ownershipWeight_pos hz b).le))
  · calc
      specialWeight z ≤ (∑ _b : Fin 4, 2 * (M : ℝ) / q) +
          ∑ _b : Fin 2, 2 * (κ : ℝ) / q :=
        add_le_add (Finset.sum_le_sum (fun b _ => matchingWeight_upper hz b))
          (Finset.sum_le_sum (fun b _ => ownershipWeight_upper hz b))
      _ = 2 * (K : ℝ) / q := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [M_value, κ_value, K_value]
        push_cast
        ring

theorem generic_add_special_le_one {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    qeval genericWeight z + specialWeight z ≤ 1 := by
  have hw := (genericWeight_bounds hz).2
  have hs := (specialWeight_bounds hz).2
  have h : (1 : ℝ) / 24 + 2 * (K : ℝ) / q ≤ 1 := by
    rw [K_value, q_value]; norm_num
  linarith

theorem resistance_pos {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    0 < resistance z :=
  Finset.sum_pos (fun b _ => inv_pos.mpr (matchingWeight_pos hz b)) Finset.univ_nonempty

theorem resistance_upper {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    resistance z ≤ 6 * (q : ℝ) / M := by
  have hc : 0 ≤ 4 * (q : ℝ) / (3 * (M : ℝ)) := by
    rw [q_value, M_value]; norm_num
  have hi (b : Fin 4) : (qeval (matchingWeight b) z)⁻¹ ≤
      4 * (q : ℝ) / (3 * (M : ℝ)) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (matchingWeight_pos hz b)).2
    have h := mul_le_mul_of_nonneg_left (matchingWeight_lower hz b) hc
    have he : 4 * (q : ℝ) / (3 * (M : ℝ)) * (3 * (M : ℝ) / (4 * (q : ℝ))) = 1 := by
      rw [M_value, q_value]; norm_num
    rwa [he] at h
  calc
    resistance z ≤ ∑ _b : Fin 4, 4 * (q : ℝ) / (3 * (M : ℝ)) :=
      Finset.sum_le_sum (fun b _ => hi b)
    _ ≤ 6 * (q : ℝ) / M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [M_value, q_value]; norm_num

noncomputable def sourceConstant (g : ℝ) (z : Coord → ℝ) : ℝ :=
  qeval markerWeight z ^ 2 * g * resistance z / 2

theorem sourceConstant_upper {g : ℝ} (hg : g ≤ 1 / 2) {z : Coord → ℝ}
    (hz : z ∈ rootTypeDomain q) : sourceConstant g z ≤ 6 / ((M : ℝ) * (q : ℝ) ^ 3) := by
  have hJ := (markerWeight_bounds hz).2
  have hJ0 := (markerWeight_pos hz).le
  have hJu : 0 ≤ 2 / (q : ℝ) ^ 2 := by positivity
  have hJ2 : qeval markerWeight z ^ 2 ≤ (2 / (q : ℝ) ^ 2) ^ 2 := by nlinarith
  have hR := (resistance_pos hz).le
  have hRu := resistance_upper hz
  calc
    sourceConstant g z ≤ qeval markerWeight z ^ 2 * (1 / 2) * resistance z / 2 := by
      unfold sourceConstant
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (sq_nonneg _)) hR
    _ ≤ (2 / (q : ℝ) ^ 2) ^ 2 * (1 / 2) * (6 * (q : ℝ) / M) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hJ2 (by norm_num)) hRu hR (by positivity)
    _ = 6 / ((M : ℝ) * (q : ℝ) ^ 3) := by
      rw [M_value, q_value]; norm_num

theorem declaring_erase_bounds {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (ν : Fin 7) :
    0 ≤ ∑ μ ∈ Finset.univ.erase ν, qeval (declaringWeight μ) z ∧
      (∑ μ ∈ Finset.univ.erase ν, qeval (declaringWeight μ) z) ≤ 1 / (4 * (q : ℝ)) := by
  have hp : (0 : ℝ) ≤ 1 / (40 * (q : ℝ)) := by positivity
  constructor
  · exact Finset.sum_nonneg (fun μ _ => hp.trans (declaringWeight_bounds hz μ).1)
  · calc
      _ ≤ ∑ _μ ∈ Finset.univ.erase ν, (1 / (24 * (q : ℝ))) :=
        Finset.sum_le_sum (fun μ _ => (declaringWeight_bounds hz μ).2)
      _ = 1 / (4 * (q : ℝ)) := by simp; ring

theorem linearWeight_bounds {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (ν : Fin 7) : 1 / 4 ≤ qeval (linearWeight ν) z ∧ qeval (linearWeight ν) z ≤ 1 / 2 := by
  simp only [linearWeight, qeval_sub, qeval_sum]
  have he := e2_bounds hz
  have hJ := markerWeight_bounds hz
  have hJ0 := (markerWeight_pos hz).le
  have hF := declaring_erase_bounds hz ν
  have hscalar : (1 : ℝ) / 4 ≤ 1 / 2 - 1 / (q : ℝ) -
      2 / (q : ℝ) ^ 2 - 1 / (4 * (q : ℝ)) := by rw [q_value]; norm_num
  constructor <;> linarith

theorem linearWeight_difference_bound {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (ν μ : Fin 7) : qeval (linearWeight ν) z - qeval (linearWeight μ) z ≤ 2 / (q : ℝ) ^ 2 := by
  simp only [linearWeight, qeval_sub, qeval_sum]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ ν), Finset.sum_erase_eq_sub (Finset.mem_univ μ)]
  have h := (declaringWeight_difference_lt hz ν μ).le
  linarith

theorem linearWeight_gap {g : ℝ} (hg : g ≤ 1 / 2) {z : Coord → ℝ}
    (hz : z ∈ rootTypeDomain q) (ν : Fin 7) :
    2 / (3 * (q : ℝ)) < qeval (linearWeight ν) z -
      3 * (qeval (rootElementary 3) z + sourceConstant g z) := by
  simp only [linearWeight, qeval_sub, qeval_sum]
  have he := e2_sub_three_e3_lower hz
  have hJ := (markerWeight_bounds hz).2
  have hF := (declaring_erase_bounds hz ν).2
  have hH := sourceConstant_upper hg hz
  have hscalar : (2 : ℝ) / (3 * (q : ℝ)) <
      (1 / (q : ℝ) - 2 / (q : ℝ) ^ 2) - 2 / (q : ℝ) ^ 2 -
        1 / (4 * (q : ℝ)) - 3 * (6 / ((M : ℝ) * (q : ℝ) ^ 3)) := by
    rw [M_value, q_value]; norm_num
  linarith

theorem type_separation_bound {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    2 / (q : ℝ) ^ 2 + specialWeight z * (2 / (q : ℝ)) <
      qeval genericWeight z / (32 * (q : ℝ)) := by
  have hs := mul_le_mul_of_nonneg_right (specialWeight_bounds hz).2
    (show (0 : ℝ) ≤ 2 / (q : ℝ) by positivity)
  have hw := div_le_div_of_nonneg_right (genericWeight_bounds hz).1
    (show (0 : ℝ) ≤ 32 * (q : ℝ) by positivity)
  have hn : 2 / (q : ℝ) ^ 2 + (2 * (K : ℝ) / q) * (2 / (q : ℝ)) <
      (1 / 40 : ℝ) / (32 * (q : ℝ)) := by
    rw [K_value, q_value]; norm_num
  linarith

/-- The entire source construction fits strictly inside every type
budget supplied by the maximizer lemma. -/
theorem source_mass_upper {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    qeval markerWeight z * resistance z ≤ 12 / ((M : ℝ) * (q : ℝ)) := by
  have h := mul_le_mul (markerWeight_bounds hz).2 (resistance_upper hz)
    (resistance_pos hz).le (show (0 : ℝ) ≤ 2 / (q : ℝ) ^ 2 by positivity)
  have he : (2 / (q : ℝ) ^ 2) * (6 * (q : ℝ) / M) =
      12 / ((M : ℝ) * (q : ℝ)) := by rw [M_value, q_value]; norm_num
  rwa [he] at h

theorem source_mass_lt_budget {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    qeval markerWeight z * resistance z < 1 / (32 * (q : ℝ)) := by
  apply lt_of_le_of_lt (source_mass_upper hz)
  rw [M_value, q_value]; norm_num

/-- The numerical gain used when declaring an unlabelled vertex is
nonnegative on the entire finite optimization domain. -/
theorem declaring_gain_nonneg {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q)
    (ν : Fin 7) {x : ℝ} (hx : 0 ≤ x) (hxq : x ≤ 2 / (q : ℝ)) :
    0 ≤ qeval (declaringWeight ν) z -
      (qeval genericWeight z / 7 + specialWeight z) * x := by
  have hF := (declaringWeight_bounds hz ν).1
  have hw := (genericWeight_bounds hz).2
  have hZ := (specialWeight_bounds hz).2
  have hcoef : qeval genericWeight z / 7 + specialWeight z ≤
      1 / 168 + 2 * (K : ℝ) / q := by linarith
  have hcoef0 : (0 : ℝ) ≤ 1 / 168 + 2 * (K : ℝ) / q := by
    rw [K_value, q_value]; norm_num
  have hcost := mul_le_mul hcoef hxq hx hcoef0
  have hscalar : ((1 : ℝ) / 168 + 2 * (K : ℝ) / q) * (2 / (q : ℝ)) ≤
      1 / (40 * (q : ℝ)) := by rw [K_value, q_value]; norm_num
  linarith

end TranscendentalTuran.Optimization.Paper
