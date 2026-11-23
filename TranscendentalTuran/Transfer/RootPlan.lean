/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TranscendentalTuran.Transfer.PatternTransfer
public import TranscendentalTuran.Transfer.RootOptions

/-!
# Constructing the source rooting from sixty-four profiles

Root rows are exactly the core vertices mapping to target roots in at least
two profiles. Root-label privacy makes selected labels injective. Matching
conflicts are resolved by the proved finite Hall argument. Every remaining
row has at least sixty-three data indices.
-/

@[expose] public section

namespace TranscendentalTuran.Transfer

open TuranUniversality Encoding

universe u v w
variable {Q : Type u} {V : Type v} {W : Type w}
  [Fintype Q] [DecidableEq Q] [Fintype V] [DecidableEq V] [DecidableEq W]

theorem exists_profile_rooting_plan
    (Γ : Finset (Finset Q))
    (hcard : ∀ e ∈ Γ, e.card = 2)
    (hmatching : ∀ e ∈ Γ, ∀ e' ∈ Γ, e ≠ e' → Disjoint e e')
    (μ : Rooting Q W) (f : Fin 64 → V → W)
    (hprivate : ∀ q a b v w, μ.val q = some (f a v) →
      μ.val q = some (f b w) → v = w) :
    Nonempty (ProfileRootingPlan Γ μ f) := by
  classical
  let rootIndices : V → Finset (Fin 64) := fun v =>
    Finset.univ.filter (fun a => f a v ∈ μ.range)
  let Rows := {v : V // 2 ≤ (rootIndices v).card}
  have htwo (v : Rows) : ∃ a b : Fin 64,
      a ∈ rootIndices v.val ∧ b ∈ rootIndices v.val ∧ a ≠ b :=
    Finset.one_lt_card_iff.mp (by have := v.property; omega)
  choose i₀ i₁ hi₀ hi₁ hne using htwo
  have hq₀ (v : Rows) : ∃ q, μ.val q = some (f (i₀ v) v.val) :=
    (Rooting.mem_range μ _).mp (Finset.mem_filter.mp (hi₀ v)).2
  have hq₁ (v : Rows) : ∃ q, μ.val q = some (f (i₁ v) v.val) :=
    (Rooting.mem_range μ _).mp (Finset.mem_filter.mp (hi₁ v)).2
  choose q₀ hq₀ using hq₀
  choose q₁ hq₁ using hq₁
  let optionIndex : Rows → Bool → Fin 64 := fun v b => if b then i₁ v else i₀ v
  let optionLabel : Rows → Bool → Q := fun v b => if b then q₁ v else q₀ v
  have hoption (v : Rows) (b : Bool) :
      μ.val (optionLabel v b) = some (f (optionIndex v b) v.val) := by
    cases b <;> simp [optionIndex, optionLabel, hq₀, hq₁]
  have hlabelPrivate : ∀ r s a b, optionLabel r a = optionLabel s b → r = s := by
    intro r s a b hlabel
    apply Subtype.ext
    exact hprivate (optionLabel r a) (optionIndex r a) (optionIndex s b) r.val s.val
      (hoption r a) (by rw [hlabel]; exact hoption s b)
  have hindex (r : Rows) : Function.Injective (optionIndex r) := by
    intro a b hab
    cases a <;> cases b <;> simp [optionIndex, hne r, Ne.symm (hne r)] at hab ⊢
  obtain ⟨choice, hlabelInjective, hpaired⟩ :=
    select_root_options Γ hcard hmatching optionLabel optionIndex hlabelPrivate hindex
  let selectedLabel : Rows → Q := fun r => optionLabel r (choice r)
  let selectedIndex : Rows → Fin 64 := fun r => optionIndex r (choice r)
  let reverse : Rooting V Q :=
    ⟨fun v => if hv : 2 ≤ (rootIndices v).card then some (selectedLabel ⟨v, hv⟩) else none,
      by
        intro v w q hv hw
        by_cases hv' : 2 ≤ (rootIndices v).card
        · by_cases hw' : 2 ≤ (rootIndices w).card
          · simp only [dif_pos hv'] at hv
            simp only [dif_pos hw'] at hw
            have hrows := hlabelInjective (Option.some.inj (hv.trans hw.symm))
            exact congrArg Subtype.val hrows
          · simp [hw'] at hw
        · simp [hv'] at hv⟩
  let ν : Rooting Q V := reverse.inverse
  let rootIndex : Q → Fin 64 := fun q =>
    if hq : ∃ r : Rows, selectedLabel r = q then selectedIndex hq.choose else 0
  have hindexSelected (r : Rows) : rootIndex (selectedLabel r) = selectedIndex r := by
    have hex : ∃ s : Rows, selectedLabel s = selectedLabel r := ⟨r, rfl⟩
    dsimp [rootIndex]
    rw [dif_pos hex]
    have hsr : hex.choose = r := hlabelInjective hex.choose_spec
    rw [hsr]
  have hassigned {q : Q} {v : V} (hv : ν.val q = some v) :
      ∃ hv' : 2 ≤ (rootIndices v).card, selectedLabel ⟨v, hv'⟩ = q := by
    have hr : reverse.val v = some q := (Rooting.inverse_some_iff reverse q v).mp hv
    by_cases hv' : 2 ≤ (rootIndices v).card
    · exact ⟨hv', Option.some.inj (by simpa [reverse, hv'] using hr)⟩
    · simp [reverse, hv'] at hr
  have hrowAssigned (r : Rows) : ν.val (selectedLabel r) = some r.val := by
    apply (Rooting.inverse_some_iff reverse (selectedLabel r) r.val).mpr
    simp [reverse, r.property]
  refine ⟨⟨ν, rootIndex, ?_, ?_, ?_⟩⟩
  · intro q v hv
    obtain ⟨hv', hq⟩ := hassigned hv
    rw [← hq, hindexSelected]
    exact hoption ⟨v, hv'⟩ (choice ⟨v, hv'⟩)
  · intro v hv
    have hsmall : (rootIndices v).card ≤ 1 := by
      by_contra h
      have hv' : 2 ≤ (rootIndices v).card := by omega
      exact hv ((Rooting.mem_range ν v).mpr ⟨selectedLabel ⟨v, hv'⟩, hrowAssigned ⟨v, hv'⟩⟩)
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 64))) (fun a => f a v ∈ μ.range)
    have htotal : (rootIndices v).card +
        (Finset.univ.filter (fun a : Fin 64 => f a v ∉ μ.range)).card = 64 := by
      simpa [rootIndices] using hsplit
    omega
  · intro q q' v v' hv hv' hΓ
    obtain ⟨hvrow, hq⟩ := hassigned hv
    obtain ⟨hvrow', hq'⟩ := hassigned hv'
    rw [← hq, ← hq', hindexSelected, hindexSelected]
    apply hpaired ⟨v, hvrow⟩ ⟨v', hvrow'⟩
    change {selectedLabel ⟨v, hvrow⟩, selectedLabel ⟨v', hvrow'⟩} ∈ Γ
    simpa only [hq, hq'] using hΓ

/-- The entire bounded-certificate reconstruction from actual profiles.
All graph, root-label, and profile conditions are explicit. -/
theorem patternClass_of_private_profiles
    (Γ : Finset (Finset Q))
    (hcard : ∀ e ∈ Γ, e.card = 2)
    (hmatching : ∀ e ∈ Γ, ∀ e' ∈ Γ, e ≠ e' → Disjoint e e')
    (R : Finset (RootedPattern Q))
    (hroots : ∀ p ∈ R, p.rootCount ≤ 40) (hdata : ∀ p ∈ R, p.dataCount ≤ 13)
    (hcompatible : ∀ p ∈ R, p.TransferCompatible Γ)
    (G : RGraph V 3) (H : RGraph W 3) (μ : Rooting Q W)
    (hlegal : PatternLegal R H μ) (f : Fin 64 → V → W)
    (hmixed : MixedProfileEdges G H f) (hcross : CrossProfilePrivacy f)
    (hprivate : ∀ q a b v w, μ.val q = some (f a v) →
      μ.val q = some (f b w) → v = w) : PatternClass R G := by
  obtain ⟨plan⟩ := exists_profile_rooting_plan Γ hcard hmatching μ f hprivate
  exact patternClass_of_profile_plan Γ R hroots hdata hcompatible G H μ hlegal f plan hmixed hcross

end TranscendentalTuran.Transfer
