module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.DenselyOrdered

@[expose] public section

/-! # Algebraicity of one-dimensional rational sign-condition boundaries

This is the one-dimensional step in Proposition 11.4. A description is
literal finite Boolean syntax over rational polynomials. Its truth value is
locally constant at every transcendental point, so every boundary point,
minimum, and uniquely described real is algebraic.

This module does not assume or claim multivariate quantifier elimination.
-/

namespace TuranUniversality.Algebraicity

open Filter Set Polynomial
open scoped Topology

/-- Finite Boolean combinations of rational polynomial sign conditions. -/
inductive UnivariateFormula where
  | top
  | eqZero (p : Polynomial ℚ)
  | ltZero (p : Polynomial ℚ)
  | neg (φ : UnivariateFormula)
  | conj (φ ψ : UnivariateFormula)
  | disj (φ ψ : UnivariateFormula)

namespace UnivariateFormula

def Holds : UnivariateFormula → ℝ → Prop
  | .top, _ => True
  | .eqZero p, x => aeval x p = 0
  | .ltZero p, x => aeval x p < 0
  | .neg φ, x => ¬ φ.Holds x
  | .conj φ ψ, x => φ.Holds x ∧ ψ.Holds x
  | .disj φ ψ, x => φ.Holds x ∨ ψ.Holds x

theorem eventually_iff_of_transcendental (φ : UnivariateFormula) (x : ℝ)
    (hx : Transcendental ℚ x) : ∀ᶠ y in 𝓝 x, φ.Holds y ↔ φ.Holds x := by
  induction φ with
  | top => exact Filter.Eventually.of_forall fun _ => Iff.rfl
  | eqZero p =>
      by_cases hp : p = 0
      · subst p
        exact Filter.Eventually.of_forall fun _ => by simp [Holds]
      · have hn : aeval x p ≠ 0 := fun h => hx ⟨p, hp, h⟩
        have he : ∀ᶠ y in 𝓝 x, aeval y p ≠ 0 := p.continuousAt_aeval.eventually_ne hn
        filter_upwards [he] with y hy
        simp [Holds, hn, hy]
  | ltZero p =>
      by_cases hp : p = 0
      · subst p
        exact Filter.Eventually.of_forall fun _ => by simp [Holds]
      · have hn : aeval x p ≠ 0 := fun h => hx ⟨p, hp, h⟩
        rcases lt_or_gt_of_ne hn with hneg | hpos
        · have he : ∀ᶠ y in 𝓝 x, aeval y p < (0 : ℝ) :=
            p.continuousAt_aeval.eventually_lt continuousAt_const hneg
          filter_upwards [he] with y hy
          simp [Holds, hneg, hy]
        · have he : ∀ᶠ y in 𝓝 x, (0 : ℝ) < aeval y p :=
            continuousAt_const.eventually_lt p.continuousAt_aeval hpos
          filter_upwards [he] with y hy
          simp [Holds, not_lt_of_ge hpos.le, not_lt_of_ge hy.le]
  | neg φ ih =>
      filter_upwards [ih] with y hy
      exact not_congr hy
  | conj φ ψ ihφ ihψ =>
      filter_upwards [ihφ, ihψ] with y hyφ hyψ
      exact and_congr hyφ hyψ
  | disj φ ψ ihφ ihψ =>
      filter_upwards [ihφ, ihψ] with y hyφ hyψ
      exact or_congr hyφ hyψ

/-- Every finite boundary point of a rational sign-condition set is algebraic. -/
theorem isAlgebraic_of_mem_frontier (φ : UnivariateFormula) (x : ℝ)
    (hx : x ∈ frontier {y | φ.Holds y}) : IsAlgebraic ℚ x := by
  by_contra ht
  have he := φ.eventually_iff_of_transcendental x ht
  rw [frontier_eq_closure_inter_closure] at hx
  by_cases hφ : φ.Holds x
  · have hf := mem_closure_iff_frequently.mp hx.2
    apply hf
    filter_upwards [he] with y hy
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] using hy.mpr hφ
  · have hf := mem_closure_iff_frequently.mp hx.1
    apply hf
    filter_upwards [he] with y hy
    exact fun h => hφ (hy.mp h)

/-- In particular the minimum of a nonempty closed bounded such set is
algebraic; the statement only needs the actual minimum, not compactness. -/
theorem isAlgebraic_of_isLeast (φ : UnivariateFormula) (x : ℝ)
    (hx : IsLeast {y | φ.Holds y} x) : IsAlgebraic ℚ x := by
  apply φ.isAlgebraic_of_mem_frontier x
  apply (mem_frontier_iff_notMem_interior hx.1).mpr
  intro hi
  have hs : {y | φ.Holds y} ⊆ Ici x := fun y hy => hx.2 hy
  have hx' := interior_mono hs hi
  simpa only [interior_Ici, mem_Ioi, lt_self_iff_false] using hx'

/-- A uniquely described real coordinate is algebraic. -/
theorem isAlgebraic_of_unique (φ : UnivariateFormula) (x : ℝ)
    (hφ : ∀ y : ℝ, φ.Holds y ↔ y = x) : IsAlgebraic ℚ x := by
  apply φ.isAlgebraic_of_isLeast x
  refine ⟨(hφ x).mpr rfl, ?_⟩
  intro y hy
  exact le_of_eq ((hφ y).mp hy).symm

end UnivariateFormula

theorem isAlgebraic_max {x y : ℝ} (hx : IsAlgebraic ℚ x) (hy : IsAlgebraic ℚ y) :
    IsAlgebraic ℚ (max x y) := by
  rcases le_total x y with h | h
  · simpa only [max_eq_right h] using hy
  · simpa only [max_eq_left h] using hx

end TuranUniversality.Algebraicity
