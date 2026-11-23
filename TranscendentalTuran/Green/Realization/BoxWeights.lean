/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.BoxData
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section

open scoped BigOperators

namespace TranscendentalTuran.Green.Realization

open Network FiniteNetwork

/-- Linear interpolation between the two endpoint weights. -/
def blend (t a b : ℝ) : ℝ := (1 - t) * a + t * b

theorem blend_nonneg {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ blend t a b :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) ha) (mul_nonneg ht0 hb)

theorem sum_blend_push {A B : Type*} [Fintype A] [Fintype B]
    (e f : A ↪ B) (x : A → ℝ) (t : ℝ) :
    (∑ b, blend t (pushWeight e x b) (pushWeight f x b)) = ∑ a, x a := by
  classical
  simp only [blend, Finset.sum_add_distrib, ← Finset.mul_sum, sum_pushWeight]
  ring

/-- The interpolation parameters are indexed by chain kind (horizontal or diagonal)
and by the three private positions (port01, center, port23). -/
abbrev Interpolation := Fin 2 → Fin 3 → ℝ

def boxWeight {n : ℕ} (X : Box n → ℝ) (θ : Interpolation) : Vertex n → ℝ
  | ⟨.base, v⟩ => X v
  | ⟨.port01, Sum.inl e⟩ => blend (θ 0 0) (pushWeight (eStart n) X e) (pushWeight (eEnd n) X e)
  | ⟨.port01, Sum.inr e⟩ => blend (θ 1 0) (pushWeight (dStart n) X e) (pushWeight (dEnd n) X e)
  | ⟨.port23, Sum.inl e⟩ => blend (θ 0 2) (pushWeight (eStart n) X e) (pushWeight (eEnd n) X e)
  | ⟨.port23, Sum.inr e⟩ => blend (θ 1 2) (pushWeight (dStart n) X e) (pushWeight (dEnd n) X e)
  | ⟨.center13, e⟩ => blend (θ 0 1) (pushWeight (eStart n) X e) (pushWeight (eEnd n) X e)
  | ⟨.center02, e⟩ => blend (θ 1 1) (pushWeight (dStart n) X e) (pushWeight (dEnd n) X e)
  | ⟨.ownerH, i⟩ => ∑ j, X (i, j)
  | ⟨.ownerV, j⟩ => ∑ i, X (i, j)

/-- The mass of a physical type, summed over its literal vertex fiber. -/
def typeMass {n : ℕ} (X : Box n → ℝ) (θ : Interpolation) (τ : PhysicalType) : ℝ :=
  ∑ v : Fiber n τ, boxWeight X θ ⟨τ, v⟩

def multiplicity : PhysicalType → ℝ
  | .port01 | .port23 => 2
  | _ => 1

theorem boxWeight_nonneg {n : ℕ} {X : Box n → ℝ} {θ : Interpolation}
    (hX : ∀ v, 0 ≤ X v) (hθ : ∀ a k, 0 ≤ θ a k ∧ θ a k ≤ 1) (v : Vertex n) :
    0 ≤ boxWeight X θ v := by
  rcases v with ⟨τ, v⟩
  cases τ
  · exact hX v
  · cases v <;> exact blend_nonneg (hθ _ _).1 (hθ _ _).2
      (pushWeight_nonneg _ hX _) (pushWeight_nonneg _ hX _)
  · cases v <;> exact blend_nonneg (hθ _ _).1 (hθ _ _).2
      (pushWeight_nonneg _ hX _) (pushWeight_nonneg _ hX _)
  · exact blend_nonneg (hθ _ _).1 (hθ _ _).2
      (pushWeight_nonneg _ hX _) (pushWeight_nonneg _ hX _)
  · exact blend_nonneg (hθ _ _).1 (hθ _ _).2
      (pushWeight_nonneg _ hX _) (pushWeight_nonneg _ hX _)
  · exact Finset.sum_nonneg fun j _ => hX (v, j)
  · exact Finset.sum_nonneg fun i _ => hX (i, v)

/-- The exact seven type masses are `s(1,2,2,1,1,1,1)`. -/
theorem typeMass_eq {n : ℕ} (X : Box n → ℝ) (θ : Interpolation) (τ : PhysicalType) :
    typeMass X θ τ = multiplicity τ * ∑ v, X v := by
  cases τ
  · simp [typeMass, boxWeight, multiplicity]
    rfl
  · change (∑ e : EAnchor n ⊕ DAnchor n, _) = _
    rw [Fintype.sum_sum_type]
    simp only [boxWeight, sum_blend_push, multiplicity]
    ring
  · change (∑ e : EAnchor n ⊕ DAnchor n, _) = _
    rw [Fintype.sum_sum_type]
    simp only [boxWeight, sum_blend_push, multiplicity]
    ring
  · exact (sum_blend_push (eStart n) (eEnd n) X (θ 0 1)).trans (one_mul _).symm
  · exact (sum_blend_push (dStart n) (dEnd n) X (θ 1 1)).trans (one_mul _).symm
  · change (∑ i, ∑ j, X (i, j)) = 1 * ∑ v, X v
    rw [one_mul]
    exact (Fintype.sum_prod_type X).symm
  · change (∑ j, ∑ i, X (i, j)) = 1 * ∑ v, X v
    rw [Finset.sum_comm, one_mul]
    exact (Fintype.sum_prod_type X).symm

theorem multiplicity_le_two (τ : PhysicalType) : multiplicity τ ≤ 2 := by
  cases τ <;> norm_num [multiplicity]

/-- The uniform type budget follows from the base mass bound. -/
theorem typeMass_le {n : ℕ} {X : Box n → ℝ} (θ : Interpolation) {B : ℝ}
    (hX : ∀ v, 0 ≤ X v) (hB : 2 * (∑ v, X v) ≤ B) (τ : PhysicalType) :
    typeMass X θ τ ≤ B := by
  rw [typeMass_eq]
  exact (mul_le_mul_of_nonneg_right (multiplicity_le_two τ)
    (Finset.sum_nonneg fun v _ => hX v)).trans hB

end TranscendentalTuran.Green.Realization
