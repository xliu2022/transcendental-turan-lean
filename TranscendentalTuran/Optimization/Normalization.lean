module

public import TranscendentalTuran.Optimization.RootLocalization
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-!
# From localized roots to the exact rational domain

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Optimization.RootLocalization

open Finset

/-- The complete numerical localization certificate, with the minimum
and maximum roots selected internally. -/
theorem localized_root_box {n : ℕ} (hn : 64 ≤ n) (r : Fin n → ℝ)
    {s t η : ℝ} (hr : ∀ i, 0 ≤ r i) (hsum : ∑ i, r i = s)
    (hs : 0 < s) (ht : 0 ≤ t) (hst : s + t = 1)
    (hb : ∀ i, r i < 2 / (n : ℝ)) (hη : η < 1 / 8)
    (hdata : 0 < t → cliqueProbability (n : ℝ) ≤
      (1 - 1 / (n : ℝ)) * s ^ 2 + 2 * η * t)
    (htransfer : ∀ i j : Fin n, (∀ k, r i ≤ r k) → (∀ k, r k ≤ r j) →
      (r j - r i) * (1 - r i - r j) ≤ t * r j + t ^ 2 / 2) :
    t / s ≤ 2 / (n : ℝ) ∧
      ∀ i, 1 / (n : ℝ) - 16 / (n : ℝ) ^ 2 ≤ r i / s ∧
        r i / s ≤ 1 / (n : ℝ) + 16 / (n : ℝ) ^ 2 := by
  have hnpos : 0 < n := by omega
  have hnr : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have hratio := data_ratio_le_two_div hnr hs ht hst hη hdata
  refine ⟨hratio, ?_⟩
  have hne : (univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hnpos⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image univ r hne
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image univ r hne
  have hmin : ∀ k, r i ≤ r k := fun k => hi k (mem_univ k)
  have hmax : ∀ k, r k ≤ r j := fun k => hj k (mem_univ k)
  have htq : t ≤ 2 * s / (n : ℝ) := by
    have h := (div_le_iff₀ hs).mp hratio
    convert h using 1 <;> ring
  have hdiam := root_diameter_le hnr hs (by linarith) ht (hr i) (hmin j)
    (hb j) htq (htransfer i j hmin hmax)
  exact normalized_root_box hnpos r hs hsum (fun k => ⟨hmin k, hmax k⟩) hdiam

noncomputable def normalizeRootTypes {n : ℕ} (r : Fin n → ℝ) (y : Fin 7 → ℝ) (s : ℝ) :
    RootTypeCoordinates n → ℝ :=
  Sum.elim (fun i => r i / s) (fun ν => y ν / s)

/-- Type masses may omit unlabelled vertices at this intermediate stage:
the weak inequality `∑ y ≤ t` is enough for domain membership. -/
theorem normalizeRootTypes_mem {n : ℕ} {r : Fin n → ℝ} {y : Fin 7 → ℝ}
    {s t : ℝ} (hs : 0 < s) (hsum : ∑ i, r i = s)
    (hy : ∀ ν, 0 ≤ y ν) (hysum : (∑ ν, y ν) ≤ t)
    (hratio : t / s ≤ 2 / (n : ℝ))
    (hbox : ∀ i, 1 / (n : ℝ) - 16 / (n : ℝ) ^ 2 ≤ r i / s ∧
      r i / s ≤ 1 / (n : ℝ) + 16 / (n : ℝ) ^ 2) :
    normalizeRootTypes r y s ∈ rootTypeDomain n := by
  refine ⟨hbox, ?_, ?_, ?_⟩
  · change (∑ i, r i / s) = 1
    rw [← Finset.sum_div, hsum, div_self (ne_of_gt hs)]
  · intro ν
    exact div_nonneg (hy ν) hs.le
  · change (∑ ν, y ν / s) ≤ 2 / (n : ℝ)
    rw [← Finset.sum_div]
    exact (div_le_div_of_nonneg_right hysum hs.le).trans hratio

end TranscendentalTuran.Optimization.RootLocalization
