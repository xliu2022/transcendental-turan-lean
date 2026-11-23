module

public import TranscendentalTuran.Algebra.Legacy.RationalQuantifiers
public import Mathlib.Topology.Order.Compact

@[expose] public section

namespace TuranUniversality.Algebraicity

open Set MvPolynomial

theorem qeval_unit_eq_aeval (p : MvPolynomial Unit ℚ) (x : ℝ) :
    qeval p (fun _ => x) = Polynomial.aeval x (MvPolynomial.uniqueAlgEquiv ℚ Unit p) := by
  change MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun _ => x) p =
    Polynomial.eval₂ (algebraMap ℚ ℝ) x (MvPolynomial.uniqueAlgEquiv ℚ Unit p)
  exact MvPolynomial.eval₂_const_uniqueAlgEquiv.symm

namespace QSemialgebraic

/-- A rational semialgebraic set in one coordinate has a literal univariate
sign formula, with the same truth value at every real number. -/
theorem univariate_description {S : Set (Unit → ℝ)} (hS : QSemialgebraic S) :
    ∃ φ : UnivariateFormula, ∀ x : ℝ, φ.Holds x ↔ (fun _ : Unit => x) ∈ S := by
  induction hS with
  | zero p =>
      refine ⟨.eqZero (MvPolynomial.uniqueAlgEquiv ℚ Unit p), ?_⟩
      intro x
      simp only [UnivariateFormula.Holds, Set.mem_setOf_eq, qeval_unit_eq_aeval]
  | positive p =>
      refine ⟨.ltZero (-(MvPolynomial.uniqueAlgEquiv ℚ Unit p)), ?_⟩
      intro x
      simp only [UnivariateFormula.Holds, Set.mem_setOf_eq, qeval_unit_eq_aeval, map_neg, neg_lt_zero]
  | compl hs ih =>
      obtain ⟨φ, hφ⟩ := ih
      exact ⟨.neg φ, fun x => not_congr (hφ x)⟩
  | inter hs ht ihs iht =>
      obtain ⟨φ, hφ⟩ := ihs
      obtain ⟨ψ, hψ⟩ := iht
      exact ⟨.conj φ ψ, fun x => and_congr (hφ x) (hψ x)⟩

theorem isAlgebraic_of_isLeast {S : Set (Unit → ℝ)} (hS : QSemialgebraic S)
    (x : ℝ) (hx : IsLeast {y : ℝ | (fun _ : Unit => y) ∈ S} x) : IsAlgebraic ℚ x := by
  obtain ⟨φ, hφ⟩ := hS.univariate_description
  apply φ.isAlgebraic_of_isLeast x
  have heq : {y | φ.Holds y} = {y : ℝ | (fun _ : Unit => y) ∈ S} := by
    ext y
    exact hφ y
  rwa [heq]

theorem isAlgebraic_of_unique {S : Set (Unit → ℝ)} (hS : QSemialgebraic S)
    (x : ℝ) (hx : ∀ y : ℝ, (fun _ : Unit => y) ∈ S ↔ y = x) : IsAlgebraic ℚ x := by
  obtain ⟨φ, hφ⟩ := hS.univariate_description
  exact φ.isAlgebraic_of_unique x (fun y => (hφ y).trans (hx y))

/-- Each coordinate of the unique point of a rational semialgebraic set is
algebraic. The projection theorem used here is proved in this development. -/
theorem isAlgebraic_coordinate_of_unique {I : Type*} [Fintype I]
    {S : Set (I → ℝ)} (hS : QSemialgebraic S) (z : I → ℝ)
    (hz : z ∈ S) (hunique : ∀ w ∈ S, w = z) (i : I) : IsAlgebraic ℚ (z i) := by
  let T : Set (I ⊕ Unit → ℝ) := {v | (v ∘ Sum.inl) ∈ S ∧ v (Sum.inl i) = v (Sum.inr ())}
  have hEq : QSemialgebraic {v : I ⊕ Unit → ℝ | v (Sum.inl i) = v (Sum.inr ())} := by
    simpa only [qeval_X] using QSemialgebraic.eq (X (Sum.inl i)) (X (Sum.inr ()))
  have hT : QSemialgebraic T := by
    apply ((hS.preimage_rename Sum.inl).inter hEq).congr
    ext v
    rfl
  have hp := hT.exists_finite
  apply hp.isAlgebraic_of_unique (z i)
  intro a
  change (∃ w : I → ℝ, Sum.elim w (fun _ : Unit => a) ∈ T) ↔ a = z i
  simp only [T, Set.mem_setOf_eq, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨w, hw, hwa⟩
    have hwz := hunique w hw
    subst w
    exact hwa.symm
  · intro ha
    exact ⟨z, hz, ha.symm⟩

theorem exists_algebraic_minimum {S : Set ℝ}
    (hS : QSemialgebraic {v : Unit → ℝ | v () ∈ S})
    (hc : IsCompact S) (hne : S.Nonempty) :
    ∃ x : ℝ, IsLeast S x ∧ IsAlgebraic ℚ x := by
  obtain ⟨x, hx⟩ := hc.exists_isLeast hne
  exact ⟨x, hx, hS.isAlgebraic_of_isLeast x hx⟩

theorem sInf_isAlgebraic {S : Set ℝ}
    (hS : QSemialgebraic {v : Unit → ℝ | v () ∈ S})
    (hc : IsCompact S) (hne : S.Nonempty) : IsAlgebraic ℚ (sInf S) := by
  obtain ⟨x, hx, halg⟩ := exists_algebraic_minimum hS hc hne
  simpa only [hx.csInf_eq] using halg

end QSemialgebraic

end TuranUniversality.Algebraicity
