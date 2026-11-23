/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Optimization.Envelope
public import TranscendentalTuran.Algebra.RationalMinimum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Transcendence of a rational affine envelope

This proves the arithmetic theorem used by the paper. The hypotheses state
the actual rational functions, their pole-free domain, positive slopes,
and an attained maximum. The needed algebraicity of minima is proved by
the imported rational sign-determination/projection development.

This theorem is an arithmetic component, not the main hypergraph theorem:
the concrete source class must still be shown to have this maximum.
-/

namespace TranscendentalTuran.Optimization

open Set MvPolynomial
open TuranUniversality.Algebraicity
open TranscendentalTuran.Algebra

/-- A rational function with coefficients literally in the rational field. -/
structure QRationalFunction (I : Type*) where
  numerator : MvPolynomial I ℚ
  denominator : MvPolynomial I ℚ

namespace QRationalFunction

variable {I : Type*}

noncomputable def eval (f : QRationalFunction I) (x : I → ℝ) : ℝ :=
  qeval f.numerator x / qeval f.denominator x

def RegularOn (f : QRationalFunction I) (s : Set (I → ℝ)) : Prop :=
  ∀ x ∈ s, qeval f.denominator x ≠ 0

theorem numerator_ne_zero_of_pos (f : QRationalFunction I) (x : I → ℝ)
    (h : 0 < f.eval x) : qeval f.numerator x ≠ 0 := by
  intro hzero
  simp only [eval, hzero, zero_div, lt_self_iff_false] at h

theorem continuousOn_eval (f : QRationalFunction I) {s : Set (I → ℝ)}
    (hf : f.RegularOn s) : ContinuousOn f.eval s :=
  (continuous_qeval f.numerator).continuousOn.div
    (continuous_qeval f.denominator).continuousOn hf

end QRationalFunction

/-- An attained maximum of `A + g B`, for rational functions on a rational
semialgebraic domain and strictly positive `B`, is transcendental whenever
`g` is transcendental. In particular no algebraicity of a maximizing
point, and no uniqueness of that point, is assumed. -/
theorem transcendental_rational_affine_maximum {I : Type*} [Fintype I]
    {s : Set (I → ℝ)} (hs : QSemialgebraic s)
    (A B : QRationalFunction I)
    (hA : A.RegularOn s) (hB : B.RegularOn s)
    (hBpos : ∀ x ∈ s, 0 < B.eval x)
    {g α : ℝ} (hg : Transcendental ℚ g)
    (hmax : IsGreatest ((fun x => A.eval x + g * B.eval x) '' s) α) :
    Transcendental ℚ α := by
  intro hα
  have hmin := isLeast_ratio_of_isGreatest_affine hBpos hmax
  let p : MvPolynomial (I ⊕ Unit) ℚ :=
    (MvPolynomial.X (Sum.inr ()) * MvPolynomial.rename Sum.inl A.denominator -
      MvPolynomial.rename Sum.inl A.numerator) *
      MvPolynomial.rename Sum.inl B.denominator
  let q : MvPolynomial (I ⊕ Unit) ℚ :=
    MvPolynomial.rename Sum.inl A.denominator *
      MvPolynomial.rename Sum.inl B.numerator
  have hnum (x : I → ℝ) (hx : x ∈ s) : qeval B.numerator x ≠ 0 :=
    B.numerator_ne_zero_of_pos x (hBpos x hx)
  have hq (x : I → ℝ) (hx : x ∈ s) : evalWithParameter q α x ≠ 0 := by
    simpa only [evalWithParameter, q, qeval_mul, qeval_rename,
      Function.comp_def, Sum.elim_inl] using mul_ne_zero (hA x hx) (hnum x hx)
  have heval (x : I → ℝ) (hx : x ∈ s) :
      evalWithParameter p α x / evalWithParameter q α x =
        (α - A.eval x) / B.eval x := by
    simp only [evalWithParameter, p, q, qeval_mul, qeval_sub, qeval_rename,
      qeval_X, Function.comp_def, Sum.elim_inl, Sum.elim_inr, QRationalFunction.eval]
    field_simp [hA x hx, hB x hx, hnum x hx]
    <;> ring
  have himage :
      (fun x => evalWithParameter p α x / evalWithParameter q α x) '' s =
        (fun x => (α - A.eval x) / B.eval x) '' s := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, (heval x hx).symm.trans hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, (heval x hx).trans hxy⟩
  have hmin' : IsLeast
      ((fun x => evalWithParameter p α x / evalWithParameter q α x) '' s) g := by
    rwa [himage]
  exact hg (rational_minimum_isAlgebraic hs p q hα hq hmin')

/-- The actual supremum value of the envelope. -/
noncomputable def rationalAffineMaximum {I : Type*} (s : Set (I → ℝ))
    (A B : QRationalFunction I) (g : ℝ) : ℝ :=
  sSup ((fun x => A.eval x + g * B.eval x) '' s)

/-- Compactness and regularity supply the attained maximum used above. -/
theorem isGreatest_rationalAffineMaximum {I : Type*}
    {s : Set (I → ℝ)} (hcompact : IsCompact s) (hne : s.Nonempty)
    (A B : QRationalFunction I) (hA : A.RegularOn s) (hB : B.RegularOn s)
    (g : ℝ) :
    IsGreatest ((fun x => A.eval x + g * B.eval x) '' s)
      (rationalAffineMaximum s A B g) := by
  have hc : ContinuousOn (fun x => A.eval x + g * B.eval x) s :=
    (A.continuousOn_eval hA).add (continuousOn_const.mul (B.continuousOn_eval hB))
  obtain ⟨α, hα⟩ :=
    (hcompact.image_of_continuousOn hc).exists_isGreatest (hne.image _)
  simpa only [rationalAffineMaximum, hα.csSup_eq] using hα

/-- The compact-domain arithmetic theorem, with the maximum defined as a
supremum and its attainment proved rather than assumed. -/
theorem rationalAffineMaximum_transcendental {I : Type*} [Fintype I]
    {s : Set (I → ℝ)} (hs : QSemialgebraic s)
    (hcompact : IsCompact s) (hne : s.Nonempty)
    (A B : QRationalFunction I) (hA : A.RegularOn s) (hB : B.RegularOn s)
    (hBpos : ∀ x ∈ s, 0 < B.eval x)
    {g : ℝ} (hg : Transcendental ℚ g) :
    Transcendental ℚ (rationalAffineMaximum s A B g) :=
  transcendental_rational_affine_maximum hs A B hA hB hBpos hg
    (isGreatest_rationalAffineMaximum hcompact hne A B hA hB g)

end TranscendentalTuran.Optimization
