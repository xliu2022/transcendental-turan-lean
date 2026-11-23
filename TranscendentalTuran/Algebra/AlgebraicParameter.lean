/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Algebra.Legacy.RationalOptimization
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Algebraic parameters in rational semialgebraic sets

The imported projection theorem is proved from the Sturm--Tarski and
sign-determination development, not postulated. This file isolates a real
algebraic number using a rational interval, so it can be used as a fixed
parameter without enlarging the coefficient field in the semialgebraic
syntax.
-/

namespace TranscendentalTuran.Algebra

open Set Polynomial MvPolynomial
open TuranUniversality.Algebraicity

/-- Any point can be separated from the other points of a finite set by
an interval with rational endpoints. -/
theorem exists_rat_interval_isolating (s : Finset ℝ) (x : ℝ) :
    ∃ a b : ℚ, (a : ℝ) < x ∧ x < (b : ℝ) ∧
      ∀ y ∈ s, (a : ℝ) < y → y < (b : ℝ) → y = x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      obtain ⟨a, ha⟩ := exists_rat_lt x
      obtain ⟨b, hb⟩ := exists_rat_gt x
      exact ⟨a, b, ha, hb, by simp⟩
  | @insert y s hy ih =>
      obtain ⟨a, b, ha, hb, hiso⟩ := ih
      rcases lt_trichotomy y x with hyx | rfl | hxy
      · obtain ⟨a', haa', ha'x⟩ := exists_rat_btwn (max_lt ha hyx)
        refine ⟨a', b, ha'x, hb, ?_⟩
        intro z hz haz hzb
        rcases Finset.mem_insert.mp hz with hzy | hz
        · have : y < (a' : ℝ) := lt_of_le_of_lt (le_max_right _ _) haa'
          rw [hzy] at haz
          exact False.elim (lt_asymm this haz)
        · exact hiso z hz (lt_trans (lt_of_le_of_lt (le_max_left _ _) haa') haz) hzb
      · refine ⟨a, b, ha, hb, ?_⟩
        intro z hz haz hzb
        rcases Finset.mem_insert.mp hz with rfl | hz
        · rfl
        · exact hiso z hz haz hzb
      · obtain ⟨b', hxb', hb'b⟩ := exists_rat_btwn (lt_min hb hxy)
        refine ⟨a, b', ha, hxb', ?_⟩
        intro z hz haz hzb
        rcases Finset.mem_insert.mp hz with hzy | hz
        · have : (b' : ℝ) < y := lt_of_lt_of_le hb'b (min_le_right _ _)
          rw [hzy] at hzb
          exact False.elim (lt_asymm hzb this)
        · exact hiso z hz haz (lt_trans hzb (lt_of_lt_of_le hb'b (min_le_left _ _)))

/-- Fixing an algebraic real parameter preserves the rational coefficient
field: its singleton has a literal rational sign-condition description. -/
theorem qSemialgebraic_singleton {x : ℝ} (hx : IsAlgebraic ℚ x) :
    QSemialgebraic {z : Unit → ℝ | z () = x} := by
  classical
  obtain ⟨p, hp, hpx⟩ := hx
  let pr : Polynomial ℝ := p.map (algebraMap ℚ ℝ)
  have hpr : pr ≠ 0 := Polynomial.map_ne_zero hp
  have hroot (y : ℝ) : Polynomial.aeval y p = 0 ↔ y ∈ pr.roots.toFinset := by
    simp only [Multiset.mem_toFinset, Polynomial.mem_roots hpr, Polynomial.IsRoot,
      pr, Polynomial.eval_map, Polynomial.aeval_def]
  obtain ⟨a, b, hax, hxb, hiso⟩ := exists_rat_interval_isolating pr.roots.toFinset x
  let p' : MvPolynomial Unit ℚ := (MvPolynomial.uniqueAlgEquiv ℚ Unit).symm p
  have heval (z : Unit → ℝ) : qeval p' z = Polynomial.aeval (z ()) p := by
    have hz : z = fun _ : Unit => z () := by
      funext i
      cases i
      rfl
    rw [hz, qeval_unit_eq_aeval]
    exact congrArg (Polynomial.aeval (z ()))
      ((MvPolynomial.uniqueAlgEquiv ℚ Unit).apply_symm_apply p)
  have hpoly : QSemialgebraic {z : Unit → ℝ | Polynomial.aeval (z ()) p = 0} := by
    simpa only [heval, qeval_zero] using QSemialgebraic.eq p' 0
  have hlo : QSemialgebraic {z : Unit → ℝ | (a : ℝ) < z ()} := by
    simpa only [qeval_C, qeval_X] using
      QSemialgebraic.lt (MvPolynomial.C a) (MvPolynomial.X ())
  have hhi : QSemialgebraic {z : Unit → ℝ | z () < (b : ℝ)} := by
    simpa only [qeval_C, qeval_X] using
      QSemialgebraic.lt (MvPolynomial.X ()) (MvPolynomial.C b)
  apply ((hpoly.inter hlo).inter hhi).congr
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hz, ha⟩, hb⟩
    exact hiso (z ()) ((hroot (z ())).mp hz) ha hb
  · intro hz
    simpa only [hz] using And.intro (And.intro hpx hax) hxb

end TranscendentalTuran.Algebra
