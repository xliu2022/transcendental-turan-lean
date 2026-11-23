module

public import TranscendentalTuran.Construction.Parameters
public import TranscendentalTuran.Core.Basic
public import TuranUniversality.Density.GuardSplit

@[expose] public section

/-!
# The concrete guard has a strictly smaller weighted maximum

Formalization author and responsible maintainer: Xizhi Liu.

The finite clique-hitting-set proof uses the previously formalized cubic
relaxation. This proves the manuscript's guard bound for its exact parameters,
with a coarser intermediate inequality than the manuscript's optimizing-weight
argument. The lemma `guard_cubic_gap` is copied without mathematical changes
from the supplied TuranUniversality archive, Construction/GuardNumerics.lean,
under its Apache-2.0 license.
-/

namespace TranscendentalTuran.Guard

open TuranUniversality TuranUniversality.Weighted Parameters

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

theorem guard_cubic_gap (q k δ a u : ℝ) (hq : 0 < q) (hk : 100 ≤ k)
    (hkq : k ≤ 24 * q / 25) (hδ : 6000000 / q ≤ δ)
    (ha : 0 ≤ a) (hu : 0 ≤ u) (hsum : a + u = 1) :
    6 * coeffA k * a ^ 3 + 3 * (1 - 1 / k) * a ^ 2 * u + 3 * a * u ^ 2 +
      (1 - δ) * u ^ 3 < 1 - 3 / q := by
  have hk0 : 0 < k := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hδ0 : 0 ≤ δ := (div_nonneg (by norm_num) hq.le).trans hδ
  have hiden : 6 * coeffA k * a ^ 3 + 3 * (1 - 1 / k) * a ^ 2 * u + 3 * a * u ^ 2 +
      (1 - δ) * u ^ 3 = 1 - (3 * a ^ 2 / k - 2 * a ^ 3 / k ^ 2) - δ * u ^ 3 := by
    have hueq : u = 1 - a := by linarith
    rw [hueq]
    unfold coeffA
    field_simp
    ring
  rw [hiden]
  have hid : 3 * a ^ 2 / k - 2 * a ^ 3 / k ^ 2 = (3 * k - 2 * a) * a ^ 2 / k ^ 2 := by
    field_simp
  have hnonneg : 0 ≤ 3 * a ^ 2 / k - 2 * a ^ 3 / k ^ 2 := by
    rw [hid]
    exact div_nonneg (mul_nonneg (by linarith) (sq_nonneg a)) (sq_nonneg k)
  by_cases huLarge : 1 / 100 ≤ u
  · have hcube : 1 / 1000000 ≤ u ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 100) huLarge 3
      norm_num at h
      exact h
    have hmul := mul_le_mul_of_nonneg_left hcube hδ0
    have hlow : 6 / q ≤ δ * u ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hδ (by norm_num : (0 : ℝ) ≤ 1 / 1000000)
      have heq : 6000000 / q * (1 / 1000000) = 6 / q := by ring
      rw [heq] at h
      exact h.trans hmul
    have hgap : 3 / q < 6 / q := div_lt_div_of_pos_right (by norm_num) hq
    linarith
  · have ha99 : 99 / 100 < a := by linarith
    have hfactor : (149 / 50 : ℝ) * k ≤ 3 * k - 2 * a := by linarith
    have hfactorMul := mul_le_mul_of_nonneg_right hfactor (sq_nonneg a)
    have hAlow : (149 / 50 : ℝ) * a ^ 2 / k ≤ 3 * a ^ 2 / k - 2 * a ^ 3 / k ^ 2 := by
      rw [hid]
      apply (div_le_div_iff₀ hk0 (sq_pos_of_pos hk0)).mpr
      have hmul := mul_le_mul_of_nonneg_right hfactorMul hk0.le
      nlinarith only [hmul]
    have haSq : (99 / 100 : ℝ) ^ 2 < a ^ 2 := by nlinarith
    have hnum : (29 / 10 : ℝ) < (149 / 50 : ℝ) * a ^ 2 := by nlinarith
    have hfrac : (29 / 10 : ℝ) / k < 3 * a ^ 2 / k - 2 * a ^ 3 / k ^ 2 :=
      (div_lt_div_of_pos_right hnum hk0).trans_le hAlow
    have hqfrac : 3 / q < (29 / 10 : ℝ) / k := by
      apply (div_lt_div_iff₀ hq hk0).mpr
      nlinarith
    have hdu : 0 ≤ δ * u ^ 3 := mul_nonneg hδ0 (pow_nonneg hu 3)
    linarith


/-- The exact number of guard cliques in the manuscript. -/
@[macro_inline] def copies : ℕ := 3 * q / (4 * guardBlockSize)

theorem copies_value : copies = 515396075520015 := by
  norm_num [copies, q_value, guardBlockSize]

abbrev Vertex := Fin copies × Fin guardBlockSize

noncomputable def graph : RGraph Vertex 3 := RGraph.cliquePacking copies guardBlockSize

theorem order_value : copies * guardBlockSize = 263882790666247680 := by
  rw [copies_value]
  norm_num [guardBlockSize]

theorem order_ratio : 4 * (copies * guardBlockSize) = 3 * q := by
  rw [order_value, q_value]

theorem free_polynomial_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : RGraph V 3) (hfree : ¬ ∃ f, graph.IsEmbedding G f)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    6 * G.edgePolynomial x < 1 - 3 / (q : ℝ) := by
  have ht : 3 ≤ guardBlockSize := by norm_num [guardBlockSize]
  have hk : 100 ≤ guardBlockSize * (copies - 1) := by
    rw [copies_value]; norm_num [guardBlockSize]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr q_pos
  have hδ : 6000000 / (q : ℝ) ≤ 1 / (guardBlockSize.choose 3 : ℝ) := by
    apply le_trans (b := 6 / (guardBlockSize : ℝ) ^ 3)
    · rw [q_value]
      norm_num [guardBlockSize]
    · exact RGraph.clique_deficit_lower ht
  have hkq : ((guardBlockSize * (copies - 1) : ℕ) : ℝ) ≤ 24 * (q : ℝ) / 25 := by
    rw [copies_value, q_value]
    norm_num [guardBlockSize]
  obtain ⟨a, u, ha, hu, hs, hbound⟩ :=
    G.guard_polynomial_split ht (by omega : 12 ≤ guardBlockSize * (copies - 1)) hfree x hx
  exact hbound.trans_lt (guard_cubic_gap (q : ℝ)
    (guardBlockSize * (copies - 1) : ℕ) (1 / (guardBlockSize.choose 3 : ℝ)) a u
    hq0 (by exact_mod_cast hk) hkq hδ ha hu hs)

theorem free_lambda_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : RGraph V 3) (hfree : ¬ ∃ f, graph.IsEmbedding G f) :
    6 * TranscendentalTuran.lambda G ≤ 1 - 3 / (q : ℝ) := by
  have hb : 0 ≤ (1 - 3 / (q : ℝ)) / 6 := by
    rw [q_value]
    norm_num
  have h := (TranscendentalTuran.lambda_le_iff G hb).mpr
    (fun x hx => (le_div_iff₀ (by norm_num : (0 : ℝ) < 6)).mpr
      (by simpa [mul_comm] using (free_polynomial_bound G hfree x hx).le))
  linarith

theorem class_bound :
    6 * classLambda (fun G => ¬ ∃ f, graph.IsEmbedding G.2 f) ≤ 1 - 3 / (q : ℝ) := by
  have hb : 0 ≤ (1 - 3 / (q : ℝ)) / 6 := by rw [q_value]; norm_num
  have h := (classLambda_le_iff (fun G => ¬ ∃ f, graph.IsEmbedding G.2 f) hb).mpr
    (fun G hG => (le_div_iff₀ (by norm_num : (0 : ℝ) < 6)).mpr
      (by simpa [mul_comm] using free_lambda_bound G.2 hG))
  linarith

end TranscendentalTuran.Guard
