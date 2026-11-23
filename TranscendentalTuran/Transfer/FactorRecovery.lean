/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TranscendentalTuran.Transfer.ProductProfiles
public import TranscendentalTuran.Transfer.RootPlan

/-!
# Recovering a source factor from an actual product homomorphism

All hypotheses describe finite graphs, genuine ordinary rooted forbidden
patterns, a matching of root pairs, and copies of the clique-block guard.
No profile plan, selector, or transfer conclusion is assumed.
-/

@[expose] public section

namespace TranscendentalTuran.Transfer

open TuranUniversality RGraph Encoding

universe u v w z y
variable {Q : Type u} {T : Type w} [Fintype Q] [DecidableEq Q] [DecidableEq T]

theorem rooting_range_card_le (μ : Rooting Q T) : μ.range.card ≤ Fintype.card Q := by
  classical
  calc
    μ.range.card ≤ ∑ q : Q, (μ.val q).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _q : Q, 1 := by
      apply Finset.sum_le_sum
      intro q _
      cases h : μ.val q <;> simp [h]
    _ = Fintype.card Q := by simp

/-- The manuscript's factor-recovery lemma for any finite collection of
positive patterns with the verified 13-data/40-root bounds. -/
theorem pattern_factor_recovery
    {d : ℕ} {Blocks : Type z} {Positions : Type y} {X : Fin d → Type v}
    [Fintype Blocks] [DecidableEq Blocks]
    [Fintype Positions] [DecidableEq Positions] [AddCommGroup Positions]
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (hd : 0 < d) (ht : 512 ≤ Fintype.card Positions)
    (hn : 128 ≤ Fintype.card (Blocks × Positions))
    (hsize : (Fintype.card Q : ℝ) ≤ 4 * (Fintype.card (Blocks × Positions) : ℝ) / 3)
    (Γ : Finset (Finset Q))
    (hcard : ∀ e ∈ Γ, e.card = 2)
    (hmatching : ∀ e ∈ Γ, ∀ e' ∈ Γ, e ≠ e' → Disjoint e e')
    (R : Finset (RootedPattern Q))
    (hroots : ∀ p ∈ R, p.rootCount ≤ 40) (hdata : ∀ p ∈ R, p.dataCount ≤ 13)
    (hcompatible : ∀ p ∈ R, p.TransferCompatible Γ)
    (A : (i : Fin d) → RGraph (X i) 3) (target : RGraph T 3)
    (guard : (i : Fin d) → Blocks × Positions → X i)
    (hguard : ∀ i, Function.Injective (guard i))
    (hedges : ∀ i x y z, x ≠ y → x ≠ z → y ≠ z →
      x.1 = y.1 → x.1 = z.1 → {guard i x, guard i y, guard i z} ∈ (A i).edges)
    (μ : Rooting Q T) (hlegal : PatternLegal R target μ)
    (hcover : ∀ x y z, {x, y, z} ∈ target.edges →
      x ∈ μ.range ∨ y ∈ μ.range ∨ z ∈ μ.range)
    (φ : ((i : Fin d) → ExtensionVertex (X i)) → T)
    (hφ : (RGraph.product fun i => (A i).pairExtension).IsHom target φ)
    (shift : Positions) (hshift : shift ≠ 0) :
    ∃ j : Fin d, PatternClass R (A j) := by
  have hrootCount : (μ.range.card : ℝ) ≤
      4 * (Fintype.card (Blocks × Positions) : ℝ) / 3 := by
    exact (Nat.cast_le.mpr (rooting_range_card_le μ)).trans hsize
  obtain ⟨j, f, hprivate, hcross, hmixed⟩ :=
    product_private_profiles hd ht hn A target guard hguard hedges φ hφ
      μ.range hrootCount hcover shift hshift
  refine ⟨j, patternClass_of_private_profiles Γ hcard hmatching R hroots hdata hcompatible
    (A j) target μ hlegal (fun a v => f a (Sum.inl v)) ?_ hcross ?_⟩
  · intro u v w he a b c hab hac hbc
    apply hmixed _ _ _ _ a b c hab hac hbc
    simpa using (core_isHom (A j)) _ he
  · intro q a b v w hav hbw
    exact hprivate a b v w (f a (Sum.inl v))
      ((Rooting.mem_range μ _).mpr ⟨q, hav⟩) rfl
      (Option.some.inj (hbw.symm.trans hav))

/-- If every core lies outside the source class, the product of its pair
extensions admits no homomorphism into an admissibly rooted target. -/
theorem product_homFree_of_no_pattern_factor
    {d : ℕ} {Blocks : Type z} {Positions : Type y} {X : Fin d → Type v}
    [Fintype Blocks] [DecidableEq Blocks]
    [Fintype Positions] [DecidableEq Positions] [AddCommGroup Positions]
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (hd : 0 < d) (ht : 512 ≤ Fintype.card Positions)
    (hn : 128 ≤ Fintype.card (Blocks × Positions))
    (hsize : (Fintype.card Q : ℝ) ≤ 4 * (Fintype.card (Blocks × Positions) : ℝ) / 3)
    (Γ : Finset (Finset Q))
    (hcard : ∀ e ∈ Γ, e.card = 2)
    (hmatching : ∀ e ∈ Γ, ∀ e' ∈ Γ, e ≠ e' → Disjoint e e')
    (R : Finset (RootedPattern Q))
    (hroots : ∀ p ∈ R, p.rootCount ≤ 40) (hdata : ∀ p ∈ R, p.dataCount ≤ 13)
    (hcompatible : ∀ p ∈ R, p.TransferCompatible Γ)
    (A : (i : Fin d) → RGraph (X i) 3) (target : RGraph T 3)
    (houtside : ∀ j, ¬ PatternClass R (A j))
    (guard : (i : Fin d) → Blocks × Positions → X i)
    (hguard : ∀ i, Function.Injective (guard i))
    (hedges : ∀ i x y z, x ≠ y → x ≠ z → y ≠ z →
      x.1 = y.1 → x.1 = z.1 → {guard i x, guard i y, guard i z} ∈ (A i).edges)
    (μ : Rooting Q T) (hlegal : PatternLegal R target μ)
    (hcover : ∀ x y z, {x, y, z} ∈ target.edges →
      x ∈ μ.range ∨ y ∈ μ.range ∨ z ∈ μ.range)
    (shift : Positions) (hshift : shift ≠ 0) :
    (RGraph.product fun i => (A i).pairExtension).HomFree target := by
  rintro ⟨φ, hφ⟩
  obtain ⟨j, hj⟩ := pattern_factor_recovery hd ht hn hsize Γ hcard hmatching
    R hroots hdata hcompatible A target guard hguard hedges μ hlegal hcover φ hφ shift hshift
  exact houtside j hj

end TranscendentalTuran.Transfer
