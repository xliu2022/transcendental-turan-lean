/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.BoxMoves
public import TranscendentalTuran.Green.Realization.PushWeight

@[expose] public section

noncomputable section

open scoped BigOperators

namespace TranscendentalTuran.Green.Realization

open Network FiniteNetwork

theorem sum_physicalType (f : PhysicalType → ℝ) :
    (∑ τ, f τ) = f .base + f .port01 + f .port23 + f .center13 + f .center02 +
      f .ownerH + f .ownerV := by
  change (∑ τ ∈ ({.base, .port01, .port23, .center13, .center02, .ownerH, .ownerV} :
    Finset PhysicalType), f τ) = _
  simp
  ring

/-- Sum over the nine literal vertex families of the seven physical types. -/
theorem sum_vertex {n : ℕ} (f : Vertex n → ℝ) :
    (∑ v, f v) =
      (∑ v : Box n, f (base v)) +
      ((∑ e : EAnchor n, f (port01E e)) + (∑ e : DAnchor n, f (port01D e))) +
      ((∑ e : EAnchor n, f (port23E e)) + (∑ e : DAnchor n, f (port23D e))) +
      (∑ e : EAnchor n, f (center13 e)) + (∑ e : DAnchor n, f (center02 e)) +
      (∑ i : Fin (n + 1), f (ownerH i)) + (∑ j : Fin (n + 1), f (ownerV j)) := by
  rw [Fintype.sum_sigma, sum_physicalType]
  change (∑ v : Box n, f (base v)) +
    (∑ e : EAnchor n ⊕ DAnchor n, f ⟨.port01, e⟩) +
    (∑ e : EAnchor n ⊕ DAnchor n, f ⟨.port23, e⟩) +
    (∑ e : EAnchor n, f (center13 e)) + (∑ e : DAnchor n, f (center02 e)) +
    (∑ i : Fin (n + 1), f (ownerH i)) + (∑ j : Fin (n + 1), f (ownerV j)) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  rfl

/-- The optional base endpoint contributes its weight, extended by zero. -/
theorem center_map_base_product {n : ℕ} {A : Type*} (e : Box n ↪ A)
    (w : Vertex n → ℝ) (a : A) (t : ℝ) :
    ((partialInverse e a).map base).elim 0 (fun c => w c * t) =
      pushWeight e (fun v => w (base v)) a * t := by
  unfold pushWeight
  cases partialInverse e a <;> simp

/-- Every base in a row is a leaf of exactly that row owner. -/
theorem ownerH_fiberMass {n : ℕ} (w : Vertex n → ℝ) (i : Fin (n + 1)) :
    (∑ l : Vertex n, if center n .ownerH l = some (ownerH i) then w l else 0) =
      ∑ j, w (base (i, j)) := by
  classical
  rw [sum_vertex]
  simp only [center, base, port01E, port01D, port23E, port23D, center13, center02,
    ownerH, ownerV, Option.some.injEq, reduceCtorEq,
    ↓reduceIte, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_prod_type]
  change (∑ a, ∑ b, if ownerH a = ownerH i then w (base (a, b)) else 0) = _
  simp only [ownerH_inj]
  simp
  rfl

/-- Every base in a column is a leaf of exactly that column owner. -/
theorem ownerV_fiberMass {n : ℕ} (w : Vertex n → ℝ) (j : Fin (n + 1)) :
    (∑ l : Vertex n, if center n .ownerV l = some (ownerV j) then w l else 0) =
      ∑ i, w (base (i, j)) := by
  classical
  rw [sum_vertex]
  simp only [center, base, port01E, port01D, port23E, port23D, center13, center02,
    ownerH, ownerV, Option.some.injEq, reduceCtorEq,
    ↓reduceIte, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_prod_type]
  change (∑ a, ∑ b, if ownerV b = ownerV j then w (base (a, b)) else 0) = _
  simp only [ownerV_inj]
  simp
  rfl

end TranscendentalTuran.Green.Realization
