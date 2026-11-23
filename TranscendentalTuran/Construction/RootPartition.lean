module

public import TranscendentalTuran.Encoding.Layout
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

namespace TranscendentalTuran.Encoding

open Parameters Network
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

theorem layerRoot_injective : Function.Injective layerRoot := by
  rintro ⟨b, i⟩ ⟨c, j⟩ h
  have hi := i.isLt
  have hj := j.isLt
  have hv := congrArg Fin.val h
  cases b <;> cases c
  all_goals
    simp only [layerRoot, matchingRoot, ownershipRoot, repetitions, M, κ] at hv hi hj
  all_goals first
    | (congr 1; apply Fin.ext; omega)
    | omega

theorem genericRoot_injective : Function.Injective genericRoot := by
  intro a b h
  have hv := congrArg Fin.val h
  apply Fin.ext
  change K + a.val = K + b.val at hv
  omega

theorem layerRoot_exists {r : Root} (hr : r.val < K) : ∃ a : Layer, layerRoot a = r := by
  have hk : K = 10240 := K_value
  by_cases h0 : r.val < 512
  · refine ⟨⟨.match0, ⟨r.val, h0⟩⟩, ?_⟩
    apply Fin.ext
    simp [layerRoot, matchingRoot]
  by_cases h1 : r.val < 1024
  · refine ⟨⟨.match1, ⟨r.val - 512, by change r.val - 512 < 512; omega⟩⟩, ?_⟩
    apply Fin.ext
    simp only [layerRoot, matchingRoot, Fin.val_one, one_mul, M]
    omega
  by_cases h2 : r.val < 1536
  · refine ⟨⟨.match2, ⟨r.val - 1024, by change r.val - 1024 < 512; omega⟩⟩, ?_⟩
    apply Fin.ext
    norm_num [layerRoot, matchingRoot, M]
    omega
  by_cases h3 : r.val < 2048
  · refine ⟨⟨.match3, ⟨r.val - 1536, by change r.val - 1536 < 512; omega⟩⟩, ?_⟩
    apply Fin.ext
    norm_num [layerRoot, matchingRoot, M]
    omega
  by_cases h4 : r.val < 6144
  · refine ⟨⟨.ownerH, ⟨r.val - 2048, by change r.val - 2048 < 4096; omega⟩⟩, ?_⟩
    apply Fin.ext
    norm_num [layerRoot, ownershipRoot, M, κ]
    omega
  · refine ⟨⟨.ownerV, ⟨r.val - 6144, by change r.val - 6144 < 4096; omega⟩⟩, ?_⟩
    apply Fin.ext
    norm_num [layerRoot, ownershipRoot, M, κ]
    omega

theorem genericRoot_exists {r : Root} (hr : IsGeneric r) :
    ∃ a : Fin N, genericRoot a = r := by
  refine ⟨⟨r.val - K, by have hlow := hr.1; have hhigh := hr.2; omega⟩, ?_⟩
  apply Fin.ext
  change K + (r.val - K) = r.val
  have := hr.1
  omega

theorem root_cases (r : Root) :
    (∃ a : Layer, layerRoot a = r) ∨ (∃ a : Fin N, genericRoot a = r) ∨ IsPassive r := by
  by_cases hs : r.val < K
  · exact Or.inl (layerRoot_exists hs)
  by_cases hg : r.val < K + N
  · exact Or.inr (Or.inl (genericRoot_exists ⟨by omega, hg⟩))
  · exact Or.inr (Or.inr (by unfold IsPassive; omega))

/-- Summation over active roots is exactly summation over all actual
special layers and all generic roots. -/
theorem sum_roots_of_passive_zero {A : Type*} [AddCommMonoid A] (f : Root → A)
    (hf : ∀ r, IsPassive r → f r = 0) :
    (∑ r, f r) = (∑ a : Layer, f (layerRoot a)) + ∑ a : Fin N, f (genericRoot a) := by
  classical
  have hs : Finset.univ.filter (fun r : Root => r.val < K) =
      Finset.univ.image layerRoot := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      exists_prop, and_true]
    exact ⟨fun h => by obtain ⟨a, ha⟩ := layerRoot_exists h; exact ⟨a, ha⟩,
      fun ⟨a, ha⟩ => ha ▸ layerRoot_special a⟩
  have hg : Finset.univ.filter IsGeneric = Finset.univ.image genericRoot := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      exists_prop, and_true]
    exact ⟨fun h => by obtain ⟨a, ha⟩ := genericRoot_exists h; exact ⟨a, ha⟩,
      fun ⟨a, ha⟩ => ha ▸ genericRoot_isGeneric a⟩
  calc
    (∑ r, f r) = (∑ r ∈ Finset.univ.filter (fun r : Root => r.val < K), f r) +
        ∑ r ∈ Finset.univ.filter IsGeneric, f r := by
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      by_cases h0 : r.val < K
      · have hnot : ¬ IsGeneric r := fun h => by have := h.1; omega
        simp [h0, hnot]
      · by_cases h1 : IsGeneric r
        · simp [h0, h1]
        · have hp : IsPassive r := by unfold IsGeneric at h1; unfold IsPassive; omega
          simp [h0, h1, hf r hp]
    _ = _ := by
      rw [hs, hg, Finset.sum_image, Finset.sum_image]
      · intro a _ b _ h
        exact genericRoot_injective h
      · intro a _ b _ h
        exact layerRoot_injective h

end TranscendentalTuran.Encoding
