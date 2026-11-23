module

public import TranscendentalTuran.Algebra.Legacy.Upstream.TauCeti.Geometry.RealAlgebraic.SignDetermination.WholeLine
public import TranscendentalTuran.Algebra.Legacy.Upstream.TauCeti.Algebra.Polynomial.Eval.Infinity
public import TranscendentalTuran.Algebra.Legacy.Upstream.TauCeti.FieldTheory.IsRealClosed.Real

@[expose] public section

namespace TuranUniversality.Algebraicity

open Set Polynomial Finset TauCeti.SignDetermination

noncomputable def rootBound (p : ℝ[X]) : ℝ :=
  (∑ z ∈ p.roots.toFinset, |z|) + 1

theorem root_lt_bound (p : ℝ[X]) (z : ℝ) (hz : z ∈ p.roots.toFinset) :
    -rootBound p < z ∧ z < rootBound p := by
  have habs : |z| ≤ ∑ w ∈ p.roots.toFinset, |w| :=
    Finset.single_le_sum (fun w _ => abs_nonneg w) hz
  have h₁ := neg_abs_le z
  have h₂ := le_abs_self z
  dsimp [rootBound]
  constructor <;> linarith

theorem sign_upper_sample (p q : ℝ[X]) (hp : p ≠ 0) (hdvd : q ≠ 0 → q ∣ p) :
    SignType.sign (q.eval (rootBound p)) = SignType.sign q.leadingCoeff := by
  by_cases hq : q = 0
  · simp [hq]
  obtain ⟨B, hB⟩ := q.exists_sign_atTop
  let y := max B (rootBound p) + 1
  have hyB : B < y := by dsimp [y]; linarith [le_max_left B (rootBound p)]
  have hby : rootBound p ≤ y := by dsimp [y]; linarith [le_max_right B (rootBound p)]
  have hfree : ∀ z ∈ Set.Icc (rootBound p) y, q.eval z ≠ 0 := by
    intro z hz hz0
    have hpz : p.eval z = 0 := eval_eq_zero_of_dvd_of_eval_eq_zero (hdvd hq) hz0
    have hzroot : z ∈ p.roots.toFinset := by simpa [mem_roots hp, IsRoot.def] using hpz
    exact (not_lt_of_ge hz.1) (root_lt_bound p z hzroot).2
  exact (q.sign_eval_const hby hfree).trans (hB y hyB)

theorem sign_lower_sample (p q : ℝ[X]) (hp : p ≠ 0) (hdvd : q ≠ 0 → q ∣ p) :
    SignType.sign (q.eval (-rootBound p)) =
      SignType.sign (q.leadingCoeff * (-1) ^ q.natDegree) := by
  by_cases hq : q = 0
  · simp [hq]
  obtain ⟨B, hB⟩ := q.exists_sign_atBot
  let y := min B (-rootBound p) - 1
  have hyB : y < B := by dsimp [y]; linarith [min_le_left B (-rootBound p)]
  have hyb : y ≤ -rootBound p := by dsimp [y]; linarith [min_le_right B (-rootBound p)]
  have hfree : ∀ z ∈ Set.Icc y (-rootBound p), q.eval z ≠ 0 := by
    intro z hz hz0
    have hpz : p.eval z = 0 := eval_eq_zero_of_dvd_of_eval_eq_zero (hdvd hq) hz0
    have hzroot : z ∈ p.roots.toFinset := by simpa [mem_roots hp, IsRoot.def] using hpz
    exact (not_lt_of_ge hz.2) (root_lt_bound p z hzroot).1
  exact (q.sign_eval_const hyb hfree).symm.trans (hB y hyB)

/-- Whole-line sign realizability reduces to two finite root tests and the
two asymptotic leading-coefficient sign vectors. No root coordinates enter
the parameterized output formula. -/
theorem wholeLine_sign_iff {J : Type*} [Fintype J]
    (Q : J → ℝ[X]) (s : J → SignType) :
    (∃ z : ℝ, ∀ j, SignType.sign ((Q j).eval z) = s j) ↔
      (∃ z ∈ (sampleProduct Q).roots.toFinset,
        ∀ j, SignType.sign ((Q j).eval z) = s j) ∨
      (∃ z ∈ (sampleProduct Q).derivative.roots.toFinset,
        ∀ j, SignType.sign ((Q j).eval z) = s j) ∨
      (∀ j, SignType.sign ((Q j).leadingCoeff * (-1) ^ (Q j).natDegree) = s j) ∨
      (∀ j, SignType.sign (Q j).leadingCoeff = s j) := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, hxy⟩ := exists_mem_signSamples_sign_eq Q x
    have hs : ∀ j, SignType.sign ((Q j).eval y) = s j := fun j => (hxy j).trans (hx j)
    rcases ((sampleProduct Q).mem_signSamples y).mp hy with hy | hy | hy | hy
    · exact Or.inl ⟨y, hy, hs⟩
    · exact Or.inr (Or.inl ⟨y, hy, hs⟩)
    · apply Or.inr ∘ Or.inr ∘ Or.inl
      intro j
      have h := sign_lower_sample (sampleProduct Q) (Q j) (sampleProduct_ne_zero Q)
        (fun hq => dvd_sampleProduct Q hq)
      subst y
      exact h.symm.trans (hs j)
    · apply Or.inr ∘ Or.inr ∘ Or.inr
      intro j
      have h := sign_upper_sample (sampleProduct Q) (Q j) (sampleProduct_ne_zero Q)
        (fun hq => dvd_sampleProduct Q hq)
      subst y
      exact h.symm.trans (hs j)
  · rintro (⟨z, hz, hs⟩ | ⟨z, hz, hs⟩ | hs | hs)
    · exact ⟨z, hs⟩
    · exact ⟨z, hs⟩
    · obtain ⟨B, hB⟩ := List.exists_signs_atBot (Finset.univ.toList.map Q)
      refine ⟨B - 1, fun j => (hB (Q j) ?_ (B - 1) (by linarith)).trans (hs j)⟩
      exact List.mem_map.mpr ⟨j, by simp, rfl⟩
    · obtain ⟨B, hB⟩ := List.exists_signs_atTop (Finset.univ.toList.map Q)
      refine ⟨B + 1, fun j => (hB (Q j) ?_ (B + 1) (by linarith)).trans (hs j)⟩
      exact List.mem_map.mpr ⟨j, by simp, rfl⟩

end TuranUniversality.Algebraicity
