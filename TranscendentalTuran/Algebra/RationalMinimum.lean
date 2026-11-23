/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Algebra.AlgebraicParameter

@[expose] public section

/-!
# Algebraicity of rational minima with an algebraic parameter

The coefficient-field issue is dealt with explicitly: the parameter is
first described by a rational semialgebraic singleton and then eliminated
together with the optimization variables. Both singleton definability and
projection are proved in the imported modules.
-/

namespace TranscendentalTuran.Algebra

open Set MvPolynomial
open TuranUniversality.Algebraicity

variable {I : Type*}

/-- Evaluate a rational polynomial with one distinguished real parameter. -/
noncomputable def evalWithParameter (p : MvPolynomial (I ⊕ Unit) ℚ)
    (a : ℝ) (x : I → ℝ) : ℝ :=
  qeval p (Sum.elim x (fun _ : Unit => a))

/-- The image of a pole-free rational function on a rational semialgebraic
set remains rational semialgebraic when its distinguished parameter is
algebraic. -/
theorem qSemialgebraic_rational_image [Fintype I]
    {s : Set (I → ℝ)} (hs : QSemialgebraic s)
    (p q : MvPolynomial (I ⊕ Unit) ℚ)
    {a : ℝ} (ha : IsAlgebraic ℚ a)
    (hq : ∀ x ∈ s, evalWithParameter q a x ≠ 0) :
    QSemialgebraic {y : Unit → ℝ | ∃ x ∈ s,
      y () = evalWithParameter p a x / evalWithParameter q a x} := by
  let V := (I ⊕ Unit) ⊕ Unit
  let T : Set (V → ℝ) := {z |
    (fun i => z (Sum.inl (Sum.inl i))) ∈ s ∧
    z (Sum.inl (Sum.inr ())) = a ∧
    qeval q (fun i => z (Sum.inl i)) ≠ 0 ∧
    qeval p (fun i => z (Sum.inl i)) =
      z (Sum.inr ()) * qeval q (fun i => z (Sum.inl i))}
  have hdom := hs.preimage_rename (fun i : I => (Sum.inl (Sum.inl i) : V))
  have hparam := (qSemialgebraic_singleton ha).preimage_rename
    (fun i : Unit => (Sum.inl (Sum.inr i) : V))
  have hden := QSemialgebraic.ne (MvPolynomial.rename Sum.inl q)
    (0 : MvPolynomial V ℚ)
  have heq := QSemialgebraic.eq (MvPolynomial.rename Sum.inl p)
    (MvPolynomial.X (Sum.inr ()) * MvPolynomial.rename Sum.inl q)
  have hT : QSemialgebraic T := by
    apply (hdom.inter (hparam.inter (hden.inter heq))).congr
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
      Function.comp_def, qeval_rename, qeval_zero, qeval_mul, qeval_X, T]
    rfl
  apply hT.exists_finite.congr
  ext y
  change (∃ w : I ⊕ Unit → ℝ, Sum.elim w y ∈ T) ↔ _
  simp only [T, Set.mem_setOf_eq, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨w, hws, hwa, hwq, hwp⟩
    let x : I → ℝ := fun i => w (Sum.inl i)
    have hw : w = Sum.elim x (fun _ : Unit => a) := by
      funext i
      cases i with
      | inl i => rfl
      | inr i => cases i; exact hwa
    refine ⟨x, hws, ?_⟩
    rw [hw] at hwq hwp
    exact (eq_div_iff hwq).2 hwp.symm
  · rintro ⟨x, hxs, hy⟩
    refine ⟨Sum.elim x (fun _ : Unit => a), hxs, rfl, hq x hxs, ?_⟩
    exact ((eq_div_iff (hq x hxs)).1 hy).symm

/-- An attained minimum of the rational function is algebraic. There is
no quantifier-elimination premise: projection has already been proved.
Compactness is unnecessary once the attained minimum is supplied. -/
theorem rational_minimum_isAlgebraic [Fintype I]
    {s : Set (I → ℝ)} (hs : QSemialgebraic s)
    (p q : MvPolynomial (I ⊕ Unit) ℚ)
    {a g : ℝ} (ha : IsAlgebraic ℚ a)
    (hq : ∀ x ∈ s, evalWithParameter q a x ≠ 0)
    (hmin : IsLeast
      ((fun x => evalWithParameter p a x / evalWithParameter q a x) '' s) g) :
    IsAlgebraic ℚ g := by
  have himage := qSemialgebraic_rational_image hs p q ha hq
  apply himage.isAlgebraic_of_isLeast g
  have heq : {y : ℝ | ∃ x ∈ s,
      y = evalWithParameter p a x / evalWithParameter q a x} =
      (fun x => evalWithParameter p a x / evalWithParameter q a x) '' s := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, hxy.symm⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, hxy.symm⟩
  change IsLeast {y : ℝ | ∃ x ∈ s,
    y = evalWithParameter p a x / evalWithParameter q a x} g
  rwa [heq]

end TranscendentalTuran.Algebra
