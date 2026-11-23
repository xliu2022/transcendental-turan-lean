module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Feasible directional derivatives for the seven-type optimization

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Optimization

open Set Filter
open scoped Topology BigOperators

theorem deriv_nonpos_of_right_max {f : ℝ → ℝ} {d δ : ℝ}
    (hd : HasDerivAt f d 0) (hδ : 0 < δ)
    (hmax : ∀ t ∈ Icc 0 δ, f t ≤ f 0) : d ≤ 0 := by
  apply le_of_tendsto hd.tendsto_slope_zero_right
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] 0, t < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hnear] with t ht hsmall
  simp only [mem_Ioi] at ht
  simp only [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le)
    (sub_nonpos.mpr (hmax t ⟨ht.le, hsmall.le⟩))

/-- Derivative of the only one-variable rational expression needed by the
type-budget argument. -/
theorem hasDerivAt_quadratic_over_cube (a b c u v : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ => (a + t * b + t ^ 2 * c) / (u + t * v) ^ 3)
      ((b * u - 3 * a * v) / u ^ 4) 0 := by
  have hn : HasDerivAt (fun t : ℝ => a + t * b + t ^ 2 * c) b 0 := by
    convert ((hasDerivAt_const (0 : ℝ) a).add
      ((hasDerivAt_id (0 : ℝ)).mul_const b)).add
        (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const c) using 1 <;> simp
    ext t
    rfl
  have hd : HasDerivAt (fun t : ℝ => (u + t * v) ^ 3) (3 * u ^ 2 * v) 0 := by
    convert ((hasDerivAt_const (0 : ℝ) u).add
      ((hasDerivAt_id (0 : ℝ)).mul_const v)).pow 3 using 1 <;> simp
    ext t
    rfl
  have hh := hn.div hd (by simpa using pow_ne_zero 3 hu)
  convert hh using 1 <;> simp only [zero_mul, add_zero, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true] <;> field_simp [hu] <;> ring

namespace QuadraticBudget

variable {I : Type*} [Fintype I]

noncomputable def mass (y : I → ℝ) : ℝ := ∑ i, y i
noncomputable def linear (L y : I → ℝ) : ℝ := ∑ i, L i * y i
noncomputable def quad (B : LinearMap.BilinForm ℝ (I → ℝ)) (y : I → ℝ) : ℝ :=
  B y y / 2
noncomputable def objective (a : ℝ) (L : I → ℝ)
    (B : LinearMap.BilinForm ℝ (I → ℝ)) (y : I → ℝ) : ℝ :=
  (a + linear L y + quad B y) / (1 + mass y) ^ 3

theorem mass_line (y d : I → ℝ) (t : ℝ) :
    mass (y + t • d) = mass y + t * mass d := by
  simp only [mass, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]

theorem linear_line (L y d : I → ℝ) (t : ℝ) :
    linear L (y + t • d) = linear L y + t * linear L d := by
  simp only [linear, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quad_line (B : LinearMap.BilinForm ℝ (I → ℝ))
    (hB : ∀ y d, B y d = B d y) (y d : I → ℝ) (t : ℝ) :
    quad B (y + t • d) = quad B y + t * B y d + t ^ 2 * quad B d := by
  simp only [quad, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hB d y]
  ring

/-- The directional derivative is computed from the actual quadratic
objective, not supplied as an extra premise. -/
theorem objective_hasDerivAt (a : ℝ) (L : I → ℝ)
    (B : LinearMap.BilinForm ℝ (I → ℝ)) (hB : ∀ y d, B y d = B d y)
    (y d : I → ℝ) (hy : 1 + mass y ≠ 0) :
    HasDerivAt (fun t : ℝ => objective a L B (y + t • d))
      (((linear L d + B y d) * (1 + mass y) -
        3 * (a + linear L y + quad B y) * mass d) / (1 + mass y) ^ 4) 0 := by
  convert hasDerivAt_quadratic_over_cube (a + linear L y + quad B y)
    (linear L d + B y d) (quad B d) (1 + mass y) (mass d) hy using 1
  funext t
  rw [objective, mass_line, linear_line, quad_line B hB]
  congr 1 <;> ring

/-- Every feasible rightward direction at a maximum obeys the first-order
inequality used in the type-budget proof. -/
theorem directional_necessary (a : ℝ) (L : I → ℝ)
    (B : LinearMap.BilinForm ℝ (I → ℝ)) (hB : ∀ y d, B y d = B d y)
    (y d : I → ℝ) (hy : 0 < 1 + mass y)
    {δ : ℝ} (hδ : 0 < δ)
    (hmax : ∀ t ∈ Icc 0 δ, objective a L B (y + t • d) ≤ objective a L B y) :
    (linear L d + B y d) * (1 + mass y) -
      3 * (a + linear L y + quad B y) * mass d ≤ 0 := by
  have hd := objective_hasDerivAt a L B hB y d (ne_of_gt hy)
  have hn := deriv_nonpos_of_right_max hd hδ (by simpa using hmax)
  have hp := mul_nonpos_of_nonpos_of_nonneg hn (le_of_lt (pow_pos hy 4))
  simpa only [div_mul_cancel₀ _ (ne_of_gt (pow_pos hy 4))] using hp

end QuadraticBudget
end TranscendentalTuran.Optimization
