module

public import TranscendentalTuran.Green.Realization.Fillers
public import TranscendentalTuran.Green.Realization.ActualEnergy
public import TranscendentalTuran.Construction.TypedPolynomial

@[expose] public section

/-!
# Exact filler masses and vanishing filler energy

Formalization author and responsible maintainer: Xizhi Liu.

Spreading a prescribed residual type mass over n isolated vertices adds its
square divided by n to every active layer. Type masses are exact at each
positive n; only the additional quadratic energy is approximated.
-/

namespace TranscendentalTuran.Green.Realization.TypedData

open Network Encoding Parameters TuranUniversality Source
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D F : Type*} [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]
  (H : TypedData D) (τ : F → PhysicalType)

theorem filler_fiber_old (b : Block) (w : D → ℝ) (v : F → ℝ) (c : D) :
    (∑ l : D ⊕ F, if (H.withFillers τ).center b l = some (Sum.inl c)
      then Sum.elim w v l else 0) =
      ∑ l : D, if H.center b l = some c then w l else 0 := by
  classical
  simp only [Fintype.sum_sum_type, H.withFillers_center_old_old, H.withFillers_center_new,
    Sum.elim_inl, Sum.elim_inr, reduceCtorEq, ite_false, Finset.sum_const_zero, add_zero]

theorem filler_fiber_new (b : Block) (w : D → ℝ) (v : F → ℝ) (f : F) :
    (∑ l : D ⊕ F, if (H.withFillers τ).center b l = some (Sum.inr f)
      then Sum.elim w v l else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro l _
  exact if_neg (H.withFillers_center_new_target τ b l f)

theorem layerEnergy_withFillers (b : Block) (w : D → ℝ) (v : F → ℝ) :
    (H.withFillers τ).layerEnergy b (Sum.elim w v) = H.layerEnergy b w +
      ∑ f : F, if Active b (τ f) then v f ^ 2 else 0 := by
  classical
  have hp : (∑ d : D ⊕ F, if sign b ((H.withFillers τ).type d) = 1 then
      (Sum.elim w v d - ∑ l : D ⊕ F, if (H.withFillers τ).center b l = some d
        then Sum.elim w v l else 0) ^ 2 else 0) =
      (∑ d : D, if sign b (H.type d) = 1 then
        (w d - ∑ l : D, if H.center b l = some d then w l else 0) ^ 2 else 0) +
      ∑ f : F, if sign b (τ f) = 1 then v f ^ 2 else 0 := by
    rw [Fintype.sum_sum_type]
    simp only [withFillers_type_old, withFillers_type_new, Sum.elim_inl, Sum.elim_inr,
      H.filler_fiber_old, H.filler_fiber_new, sub_zero]
  have hn : (∑ l : D ⊕ F,
      if sign b ((H.withFillers τ).type l) = -1 ∧ (H.withFillers τ).center b l = none
      then Sum.elim w v l ^ 2 else 0) =
      (∑ l : D, if sign b (H.type l) = -1 ∧ H.center b l = none then w l ^ 2 else 0) +
      ∑ f : F, if sign b (τ f) = -1 then v f ^ 2 else 0 := by
    rw [Fintype.sum_sum_type]
    simp only [withFillers_type_old, withFillers_type_new, withFillers_center_old,
      withFillers_center_new, Option.map_eq_none_iff, and_true, Sum.elim_inl, Sum.elim_inr]
  have hs : (∑ f : F, if sign b (τ f) = 1 then v f ^ 2 else 0) +
      (∑ f : F, if sign b (τ f) = -1 then v f ^ 2 else 0) =
      ∑ f : F, if Active b (τ f) then v f ^ 2 else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro f _
    rcases sign_trichotomy b (τ f) with ht | ht | ht <;> simp [Active, ht]
  unfold layerEnergy
  rw [hp, hn]
  linarith

theorem typeMass_withFillers (w : D → ℝ) (v : F → ℝ) (ν : PhysicalType) :
    RootData.typeMass (H.withFillers τ).type (Sum.elim w v) ν =
      RootData.typeMass H.type w ν + ∑ f : F, if τ f = ν then v f else 0 := by
  classical
  simp only [RootData.typeMass, RootData.typedPartition, Weighted.TypePartition.mass,
    Finset.sum_filter, Fintype.sum_sum_type, withFillers_type_old, withFillers_type_new,
    Sum.elim_inl, Sum.elim_inr]
  rfl

abbrev UniformFiller (n : ℕ) := PhysicalType × Fin n

def withUniformFillers (n : ℕ) : TypedData (D ⊕ UniformFiller n) := H.withFillers Prod.fst

noncomputable def uniformFillerWeight (_H : TypedData D) (n : ℕ) (w : D → ℝ) (a : PhysicalType → ℝ) :
    D ⊕ UniformFiller n → ℝ := Sum.elim w (fun f => a f.1 / (n : ℝ))

theorem uniformFillerWeight_nonneg (n : ℕ) {w : D → ℝ} {a : PhysicalType → ℝ}
    (hw : ∀ d, 0 ≤ w d) (ha : ∀ ν, 0 ≤ a ν) (d : D ⊕ UniformFiller n) :
    0 ≤ H.uniformFillerWeight n w a d := by
  cases d with
  | inl d => exact hw d
  | inr f => exact div_nonneg (ha f.1) (Nat.cast_nonneg n)

theorem uniformFiller_typeMass {n : ℕ} (hn : 0 < n) (w : D → ℝ)
    (a : PhysicalType → ℝ) (ν : PhysicalType) :
    RootData.typeMass (H.withUniformFillers n).type (H.uniformFillerWeight n w a) ν =
      RootData.typeMass H.type w ν + a ν := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [withUniformFillers, uniformFillerWeight, H.typeMass_withFillers]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp [mul_ite]
  exact mul_div_cancel₀ _ hn'

theorem uniformFiller_typeMass_target {n : ℕ} (hn : 0 < n) (w : D → ℝ)
    (y : PhysicalType → ℝ) (ν : PhysicalType) :
    RootData.typeMass (H.withUniformFillers n).type
      (H.uniformFillerWeight n w (fun σ => y σ - RootData.typeMass H.type w σ)) ν = y ν := by
  rw [H.uniformFiller_typeMass hn]
  ring

noncomputable def fillerBlockCost (b : Block) (a : PhysicalType → ℝ) : ℝ :=
  ∑ ν : PhysicalType, if Active b ν then a ν ^ 2 else 0

theorem uniformFiller_layerEnergy {n : ℕ} (hn : 0 < n) (b : Block) (w : D → ℝ)
    (a : PhysicalType → ℝ) :
    (H.withUniformFillers n).layerEnergy b (H.uniformFillerWeight n w a) =
      H.layerEnergy b w + fillerBlockCost b a / (n : ℝ) := by
  classical
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [withUniformFillers, uniformFillerWeight, H.layerEnergy_withFillers]
  congr 1
  rw [Fintype.sum_prod_type, fillerBlockCost, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ν _
  by_cases hν : Active b ν
  · simp only [hν, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [hn'] <;> ring
  · simp [hν]

noncomputable def fillerEnergyCost (z : Root → ℝ) (a : PhysicalType → ℝ) : ℝ :=
  ∑ r : Layer, z (layerRoot r) * fillerBlockCost r.1 a

theorem uniformFiller_energy_sum {n : ℕ} (hn : 0 < n) (z : Root → ℝ) (w : D → ℝ)
    (a : PhysicalType → ℝ) :
    (∑ r : Layer, z (layerRoot r) *
      (H.withUniformFillers n).layerEnergy r.1 (H.uniformFillerWeight n w a)) =
      (∑ r : Layer, z (layerRoot r) * H.layerEnergy r.1 w) + fillerEnergyCost z a / (n : ℝ) := by
  simp only [H.uniformFiller_layerEnergy hn, mul_add, Finset.sum_add_distrib,
    mul_div, ← Finset.sum_div, fillerEnergyCost]

theorem exists_filler_count (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ C / (n : ℝ) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C / ε) 0)
  have hnpos : (0 : ℝ) < n := (le_max_right _ _).trans_lt hn
  have hdiv : C / ε < n := (le_max_left _ _).trans_lt hn
  refine ⟨n, by exact_mod_cast hnpos, (div_lt_iff₀ hnpos).mpr ?_⟩
  have hc := (div_lt_iff₀ hε).mp hdiv
  nlinarith

end TranscendentalTuran.Green.Realization.TypedData
