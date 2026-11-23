module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace TranscendentalTuran.Source.TypeSurgery

open scoped BigOperators
variable {D : Type*} [DecidableEq D]

theorem pair_eq_of_mem (p : Finset D) (hp : p.card = 2) {a b : D}
    (ha : a ∈ p) (hb : b ∈ p) (hab : a ≠ b) : p = {a, b} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    · exact Finset.mem_singleton.mp hx ▸ hb
  · simpa only [Finset.card_pair hab, hp] using (le_refl (2 : ℕ))

/-- The total weight of any collection of pairs incident with `a` is
bounded by `w a` times the mass of the possible other endpoints. -/
theorem incident_pairs_weight_le (R : Finset (Finset D)) (a : D) (T : Finset D)
    (hcard : ∀ p ∈ R, p.card = 2) (ha : ∀ p ∈ R, a ∈ p)
    (hother : ∀ p ∈ R, ∀ d ∈ p, d ≠ a → d ∈ T)
    (w : D → ℝ) (hw : ∀ d, 0 ≤ w d) :
    (∑ p ∈ R, ∏ d ∈ p, w d) ≤ w a * ∑ d ∈ T, w d := by
  have hsub : R ⊆ (T.erase a).image (fun d => ({a, d} : Finset D)) := by
    intro p hp
    obtain ⟨u, v, huv, hpv⟩ := Finset.card_eq_two.mp (hcard p hp)
    have hap : a = u ∨ a = v := by simpa only [hpv, Finset.mem_insert, Finset.mem_singleton] using ha p hp
    rcases hap with rfl | rfl
    · refine Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨Ne.symm huv, ?_⟩, hpv.symm⟩
      exact hother p hp v (by simp [hpv]) (Ne.symm huv)
    · refine Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨huv, ?_⟩, ?_⟩
      · exact hother p hp u (by simp [hpv]) huv
      · simpa only [Finset.pair_comm] using hpv.symm
  calc
    (∑ p ∈ R, ∏ d ∈ p, w d) ≤
        ∑ p ∈ (T.erase a).image (fun d => ({a, d} : Finset D)), ∏ d ∈ p, w d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p _ _
      exact Finset.prod_nonneg (fun d _ => hw d)
    _ = ∑ d ∈ T.erase a, w a * w d := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro d hd
        exact Finset.prod_pair (Ne.symm (Finset.mem_erase.mp hd).1)
      · intro d hd e he hde
        change ({a, d} : Finset D) = {a, e} at hde
        have hm : d ∈ ({a, e} : Finset D) := by rw [← hde]; simp
        exact Finset.mem_singleton.mp
          ((Finset.mem_insert.mp hm).resolve_left (Finset.mem_erase.mp hd).1)
    _ ≤ ∑ d ∈ T, w a * w d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro d _ _
      exact mul_nonneg (hw a) (hw d)
    _ = w a * ∑ d ∈ T, w d := (Finset.mul_sum _ _ _).symm

end TranscendentalTuran.Source.TypeSurgery
