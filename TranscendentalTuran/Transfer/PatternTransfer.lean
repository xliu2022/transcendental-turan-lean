/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TranscendentalTuran.Encoding.PositivePatterns
public import TranscendentalTuran.Transfer.Choices

/-!
# Transferring actual positive certificates through mixed profiles

An explicit rooting plan supplies the choices of root labels and profile
indices. This file proves that the plan is legal: every failed source
certificate would become an injective, label-preserving failed certificate
in the target. The root plan is a separate finite construction, not an axiom.
-/

@[expose] public section

namespace TranscendentalTuran.Transfer

open TuranUniversality Encoding

universe u v w
variable {Q : Type u} {V : Type v} {W : Type w}
  [Fintype Q] [DecidableEq Q] [DecidableEq V] [DecidableEq W]

structure ProfileRootingPlan (Γ : Finset (Finset Q)) (μ : Rooting Q W)
    (f : Fin 64 → V → W) where
  source : Rooting Q V
  rootIndex : Q → Fin 64
  root_image : ∀ q v, source.val q = some v →
    μ.val q = some (f (rootIndex q) v)
  data_options : ∀ v, v ∉ source.range →
    63 ≤ (Finset.univ.filter (fun a : Fin 64 => f a v ∉ μ.range)).card
  paired_indices : ∀ q q' v v', source.val q = some v → source.val q' = some v' →
    {q, q'} ∈ Γ → rootIndex q ≠ rootIndex q'

def MixedProfileEdges (G : RGraph V 3) (H : RGraph W 3) (f : Fin 64 → V → W) : Prop :=
  ∀ u v w, {u, v, w} ∈ G.edges → ∀ a b c : Fin 64,
    a ≠ b → a ≠ c → b ≠ c → {f a u, f b v, f c w} ∈ H.edges

def CrossProfilePrivacy (f : Fin 64 → V → W) : Prop :=
  ∀ a b : Fin 64, ∀ v w : V, a ≠ b → v ≠ w → f a v ≠ f b w

theorem transfer_positive_pattern
    (Γ : Finset (Finset Q)) (G : RGraph V 3) (H : RGraph W 3)
    (μ : Rooting Q W) (f : Fin 64 → V → W)
    (plan : ProfileRootingPlan Γ μ f)
    (hmixed : MixedProfileEdges G H f) (hprivate : CrossProfilePrivacy f)
    (p : RootedPattern Q) (hroots : p.rootCount ≤ 40) (hdata : p.dataCount ≤ 13)
    (hcompatible : p.TransferCompatible Γ)
    {g : p.Vertices → V} (hg : p.Matches G plan.source g) : p.Realizes H μ := by
  classical
  let forbidden : Finset (Fin 64) :=
    Finset.univ.image (fun i : Fin p.rootCount => plan.rootIndex (p.rootLabels i))
  let allowed : Fin p.dataCount → Finset (Fin 64) := fun j =>
    Finset.univ.filter fun a => f a (g (Sum.inr j)) ∉ μ.range
  have hfcard : forbidden.card ≤ 40 := by
    have h : forbidden.card ≤ p.rootCount := by
      exact Finset.card_image_le.trans (by simp)
    exact h.trans hroots
  have hacard (j : Fin p.dataCount) : 63 ≤ (allowed j).card :=
    plan.data_options (g (Sum.inr j)) (hg.data_out j)
  obtain ⟨chooseData, hchooseInjective, hchoose⟩ := select_certificate_indices
    (R := Fin p.dataCount) (by simpa using hdata) allowed forbidden hfcard hacard
  let index : p.Vertices → Fin 64 :=
    Sum.elim (fun i => plan.rootIndex (p.rootLabels i)) chooseData
  let g' : p.Vertices → W := fun v => f (index v) (g v)
  have hroot (i : Fin p.rootCount) : μ.val (p.rootLabels i) = some (g' (Sum.inl i)) :=
    plan.root_image _ _ (hg.root_eq i)
  have hout (j : Fin p.dataCount) : g' (Sum.inr j) ∉ μ.range :=
    (Finset.mem_filter.mp (hchoose j).1).2
  have hrootData (i : Fin p.rootCount) (j : Fin p.dataCount) :
      index (Sum.inl i) ≠ index (Sum.inr j) := by
    intro heq
    apply (hchoose j).2
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩
  have hdataData {i j : Fin p.dataCount} (hij : i ≠ j) :
      index (Sum.inr i) ≠ index (Sum.inr j) := fun h => hij (hchooseInjective h)
  have hinj : Function.Injective g' := by
    intro a b hab
    cases a with
    | inl r =>
        cases b with
        | inl s =>
            have hlabels := μ.property (p.rootLabels r) (p.rootLabels s)
              (g' (Sum.inl r)) (hroot r) ((hroot s).trans (congrArg some hab.symm))
            exact congrArg Sum.inl (p.rootLabels.injective hlabels)
        | inr j =>
            have hrange : g' (Sum.inl r) ∈ μ.range :=
              (Rooting.mem_range μ _).mpr ⟨p.rootLabels r, hroot r⟩
            exact False.elim (hout j (hab ▸ hrange))
    | inr i =>
        cases b with
        | inl r =>
            have hrange : g' (Sum.inl r) ∈ μ.range :=
              (Rooting.mem_range μ _).mpr ⟨p.rootLabels r, hroot r⟩
            exact False.elim (hout i (hab.symm ▸ hrange))
        | inr j =>
            have hij : i = j := by
              by_contra hij
              have hcore : g (Sum.inr i) ≠ g (Sum.inr j) :=
                fun h => hij (Sum.inr.inj (hg.embedding.1 h))
              exact hprivate _ _ _ _ (hdataData hij) hcore hab
            exact congrArg Sum.inr hij
  have htriple (a b c : p.Vertices) (he : {a, b, c} ∈ p.graph.edges)
      (hab : index a ≠ index b) (hac : index a ≠ index c) (hbc : index b ≠ index c) :
      (({a, b, c} : Finset p.Vertices).image g') ∈ H.edges := by
    have hG : {g a, g b, g c} ∈ G.edges := by
      simpa using hg.embedding.2 _ he
    simpa [g'] using hmixed (g a) (g b) (g c) hG (index a) (index b) (index c) hab hac hbc
  have hedge : p.graph.IsHom H g' := by
    intro e he
    rcases hcompatible e he with h | h | h
    · obtain ⟨a, b, c, rfl⟩ := h
      have hne := Finset.card_triple_eq_three_iff.mp (p.graph.uniform _ he)
      apply htriple _ _ _ he
      · exact hdataData (fun h => hne.1 (congrArg Sum.inr h))
      · exact hdataData (fun h => hne.2.1 (congrArg Sum.inr h))
      · exact hdataData (fun h => hne.2.2 (congrArg Sum.inr h))
    · obtain ⟨r, a, b, rfl⟩ := h
      have hne := Finset.card_triple_eq_three_iff.mp (p.graph.uniform _ he)
      exact htriple _ _ _ he (hrootData r a) (hrootData r b)
        (hdataData (fun h => hne.2.2 (congrArg Sum.inr h)))
    · obtain ⟨r, s, a, rfl, hrs⟩ := h
      exact htriple _ _ _ he
        (plan.paired_indices _ _ _ _ (hg.root_eq r) (hg.root_eq s) hrs)
        (hrootData r a) (hrootData s a)
  exact ⟨g', ⟨hinj, hedge⟩, hroot, hout⟩

/-- All bounded positive certificates transfer, hence the source rooting
in the explicit plan is admissible. -/
theorem patternLegal_of_profile_plan
    (Γ : Finset (Finset Q)) (R : Finset (RootedPattern Q))
    (hroots : ∀ p ∈ R, p.rootCount ≤ 40) (hdata : ∀ p ∈ R, p.dataCount ≤ 13)
    (hcompatible : ∀ p ∈ R, p.TransferCompatible Γ)
    (G : RGraph V 3) (H : RGraph W 3) (μ : Rooting Q W)
    (hlegal : PatternLegal R H μ) (f : Fin 64 → V → W)
    (plan : ProfileRootingPlan Γ μ f)
    (hmixed : MixedProfileEdges G H f) (hprivate : CrossProfilePrivacy f) :
    PatternLegal R G plan.source := by
  intro p hp hreal
  obtain ⟨g, hg⟩ := hreal
  exact hlegal p hp (transfer_positive_pattern Γ G H μ f plan hmixed hprivate
    p (hroots p hp) (hdata p hp) (hcompatible p hp) hg)

theorem patternClass_of_profile_plan
    (Γ : Finset (Finset Q)) (R : Finset (RootedPattern Q))
    (hroots : ∀ p ∈ R, p.rootCount ≤ 40) (hdata : ∀ p ∈ R, p.dataCount ≤ 13)
    (hcompatible : ∀ p ∈ R, p.TransferCompatible Γ)
    (G : RGraph V 3) (H : RGraph W 3) (μ : Rooting Q W)
    (hlegal : PatternLegal R H μ) (f : Fin 64 → V → W)
    (plan : ProfileRootingPlan Γ μ f)
    (hmixed : MixedProfileEdges G H f) (hprivate : CrossProfilePrivacy f) :
    PatternClass R G :=
  ⟨plan.source, patternLegal_of_profile_plan Γ R hroots hdata hcompatible
    G H μ hlegal f plan hmixed hprivate⟩

end TranscendentalTuran.Transfer
