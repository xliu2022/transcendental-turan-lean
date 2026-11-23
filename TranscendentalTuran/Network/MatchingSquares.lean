module

public import TranscendentalTuran.Network.StarEnergy

@[expose] public section

/-! # Completion of partial matching squares

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Network.StarEnergy

open scoped BigOperators

variable {C B : Type*} [Fintype C] [Fintype B] [DecidableEq C] [DecidableEq B]

def IsPartialMatching (f : B → Option C) : Prop :=
  ∀ b d c, f b = some c → f d = some c → b = d

theorem fiberPairs_zero_of_matching {f : B → Option C} (hf : IsPartialMatching f)
    (y : B → ℝ) (c : C) : fiberPairs f y c = 0 := by
  classical
  by_cases he : ∃ b, f b = some c
  · obtain ⟨b, hb⟩ := he
    have hi (d : B) : f d = some c ↔ d = b :=
      ⟨fun hd => hf d b c hd hb, fun h => h ▸ hb⟩
    simp [fiberPairs, fiberMass, fiberSquareMass, hi]
  · have hi : ∀ b, f b ≠ some c := fun b hb => he ⟨b, hb⟩
    simp [fiberPairs, fiberMass, fiberSquareMass, hi]

theorem cross_sum_eq (f : B → Option C) (x : C → ℝ) (y : B → ℝ) :
    (∑ c, x c * fiberMass f y c) =
      ∑ b, (f b).elim 0 (fun c => x c * y b) := by
  simp only [fiberMass, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  cases hb : f b with
  | none => simp
  | some c => simp [eq_comm]

theorem matching_energy_expansion {f : B → Option C} (hf : IsPartialMatching f)
    (x : C → ℝ) (y : B → ℝ) :
    energy f x y = (∑ c, x c ^ 2) + (∑ b, y b ^ 2) -
      2 * ∑ b, (f b).elim 0 (fun c => x c * y b) := by
  rw [energy_expansion, cross_sum_eq]
  simp only [fiberPairs_zero_of_matching hf, Finset.sum_const_zero, mul_zero, add_zero]

/-- Completing a partial matching throughout its block can only lower energy. -/
theorem matching_energy_antitone {f g : B → Option C}
    (hf : IsPartialMatching f) (hg : IsPartialMatching g)
    (hfg : ∀ b c, f b = some c → g b = some c)
    (x : C → ℝ) (y : B → ℝ) (hx : ∀ c, 0 ≤ x c) (hy : ∀ b, 0 ≤ y b) :
    energy g x y ≤ energy f x y := by
  have hw : (∑ b, (f b).elim 0 (fun c => x c * y b)) ≤
      ∑ b, (g b).elim 0 (fun c => x c * y b) := by
    apply Finset.sum_le_sum
    intro b _
    cases hb : f b with
    | none =>
      cases hc : g b with
      | none => exact le_rfl
      | some c => exact mul_nonneg (hx c) (hy b)
    | some c => simp [hfg b c hb]
  rw [matching_energy_expansion hf, matching_energy_expansion hg]
  linarith

end TranscendentalTuran.Network.StarEnergy
