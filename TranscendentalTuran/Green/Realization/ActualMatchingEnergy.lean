module

public import TranscendentalTuran.Green.Realization.ActualEnergy
public import TranscendentalTuran.Network.MatchingSquares

@[expose] public section

/-!
# The matching-block energy of a lower template

Formalization author and responsible maintainer: Xizhi Liu.

The partial-matching condition turns the signed-star energy into the sum
of active vertex squares minus twice the actual incidence products.
-/

namespace TranscendentalTuran.Green.Realization.TypedData

open Network Encoding Parameters TuranUniversality Source
open scoped BigOperators

variable {D : Type*} [Fintype D] [DecidableEq D] (H : TypedData D)

def positiveWeight (b : Block) (w : D → ℝ) (d : D) : ℝ :=
  if sign b (H.type d) = 1 then w d else 0

def negativeWeight (b : Block) (w : D → ℝ) (d : D) : ℝ :=
  if sign b (H.type d) = -1 then w d else 0

theorem filtered_fiberMass (b : Block) (w : D → ℝ) (c : D) :
    StarEnergy.fiberMass (H.center b) (H.negativeWeight b w) c =
      ∑ l, if H.center b l = some c then w l else 0 := by
  classical
  unfold StarEnergy.fiberMass
  apply Finset.sum_congr rfl
  intro l _
  by_cases hc : H.center b l = some c
  · simp [hc, negativeWeight, (H.center_signs hc).2]
  · simp [hc]

theorem fiberMass_zero_of_not_positive (b : Block) (w : D → ℝ) (c : D)
    (hc : sign b (H.type c) ≠ 1) :
    (∑ l, if H.center b l = some c then w l else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro l _
  have hn : H.center b l ≠ some c := fun he => hc (H.center_signs he).1
  simp [hn]

theorem layerEnergy_eq_starEnergy (b : Block) (w : D → ℝ) :
    H.layerEnergy b w = StarEnergy.energy (H.center b)
      (H.positiveWeight b w) (H.negativeWeight b w) := by
  classical
  unfold layerEnergy StarEnergy.energy
  simp_rw [H.filtered_fiberMass]
  congr 1
  · apply Finset.sum_congr rfl
    intro d _
    by_cases hd : sign b (H.type d) = 1
    · simp [hd, positiveWeight]
    · simp [hd, positiveWeight, H.fiberMass_zero_of_not_positive b w d hd]
  · apply Finset.sum_congr rfl
    intro d _
    by_cases hs : sign b (H.type d) = -1 <;>
      by_cases hn : H.center b d = none <;> simp [hs, hn, negativeWeight]

theorem signed_squares_eq_active (b : Block) (w : D → ℝ) :
    (∑ d, H.positiveWeight b w d ^ 2) + (∑ d, H.negativeWeight b w d ^ 2) =
      ∑ d, if Active b (H.type d) then w d ^ 2 else 0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rcases sign_trichotomy b (H.type d) with hs | hs | hs <;>
    simp [positiveWeight, negativeWeight, Active, hs]

theorem center_products_eq (b : Block) (w : D → ℝ) :
    (∑ l, (H.center b l).elim 0
      (fun c => H.positiveWeight b w c * H.negativeWeight b w l)) =
      ∑ l, (H.center b l).elim 0 (fun c => w c * w l) := by
  apply Finset.sum_congr rfl
  intro l _
  cases hc : H.center b l with
  | none => rfl
  | some c =>
    have hs := H.center_signs hc
    simp [positiveWeight, negativeWeight, hs.1, hs.2]

theorem matching_layerEnergy_expansion (hL : H.Legal) (b : Fin 4) (w : D → ℝ) :
    H.layerEnergy (matchingBlock b) w =
      (∑ d, if Active (matchingBlock b) (H.type d) then w d ^ 2 else 0) -
        2 * ∑ l, (H.center (matchingBlock b) l).elim 0 (fun c => w c * w l) := by
  have hf : StarEnergy.IsPartialMatching (H.center (matchingBlock b)) := by
    intro l l' c hl hl'
    exact hL.matching_left b c l l' hl hl'
  rw [H.layerEnergy_eq_starEnergy, StarEnergy.matching_energy_expansion hf,
    H.signed_squares_eq_active, H.center_products_eq]

end TranscendentalTuran.Green.Realization.TypedData
