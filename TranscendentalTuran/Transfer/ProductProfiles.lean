/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TranscendentalTuran.Transfer.GuardTables
public import TranscendentalTuran.Transfer.ThresholdSelector
public import TuranUniversality.Selector.CompatibleProfiles

/-!
# Exact profiles from a genuine product homomorphism

The guard has `n = |Blocks| |Positions|` vertices with at most `4n/3`
target roots. The selection uses the manuscript's two-dimensional tables,
and does not invoke the older selector requiring a larger guard.
-/

@[expose] public section

namespace TranscendentalTuran.Transfer

open TuranUniversality RGraph

universe u v w z
variable {d : ℕ} {Blocks : Type u} {Positions : Type z} {T : Type w}
  {X : Fin d → Type v}
  [Fintype Blocks] [DecidableEq Blocks]
  [Fintype Positions] [DecidableEq Positions] [AddCommGroup Positions]
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] [DecidableEq T]

/-- The cyclic diagonal decomposition gives the missing-cell estimate for
every actual threshold table, including its two degenerate endpoints. -/
theorem product_threshold_nonroot_bound (hd : 0 < d)
    (A : (i : Fin d) → RGraph (X i) 3) (target : RGraph T 3)
    (guard : (i : Fin d) → Blocks × Positions → X i)
    (hedges : ∀ i x y z, x ≠ y → x ≠ z → y ≠ z →
      x.1 = y.1 → x.1 = z.1 → {guard i x, guard i y, guard i z} ∈ (A i).edges)
    (φ : ((i : Fin d) → ExtensionVertex (X i)) → T)
    (hφ : (RGraph.product fun i => (A i).pairExtension).IsHom target φ)
    (roots : Finset T)
    (hcover : ∀ x y z, {x, y, z} ∈ target.edges →
      x ∈ roots ∨ y ∈ roots ∨ z ∈ roots) (k : ℕ) :
    (nonrootCells (thresholdTable (fun x => φ (fun i => Sum.inl (x i))) guard k)
      roots).card ≤ 2 * Fintype.card Blocks * Fintype.card Blocks * Fintype.card Positions := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  apply guard_table_nonroot_bound
  intro x y z x' y' z' hxy hxz hyz hxy' hxz' hyz' hbxy hbxz hbxy' hbxz'
  let a := thresholdTuple guard k x x'
  let b := thresholdTuple guard k y y'
  let c := thresholdTuple guard k z z'
  have hpoint (i : Fin d) :
      {Sum.inl (a i), Sum.inl (b i), Sum.inl (c i)} ∈ (A i).pairExtension.edges := by
    have hcore : {a i, b i, c i} ∈ (A i).edges := by
      dsimp [a, b, c, thresholdTuple]
      by_cases hi : i.val < k
      · simp only [hi, ite_true]
        exact hedges i x y z hxy hxz hyz hbxy hbxz
      · simp only [hi, ite_false]
        exact hedges i x' y' z' hxy' hxz' hyz' hbxy' hbxz'
    simpa using (core_isHom (A i)) _ hcore
  have he := Selector.triple_product_mem (fun i => (A i).pairExtension)
    (fun i => Sum.inl (a i)) (fun i => Sum.inl (b i)) (fun i => Sum.inl (c i)) hpoint
  have ht : {φ (fun i => Sum.inl (a i)), φ (fun i => Sum.inl (b i)),
      φ (fun i => Sum.inl (c i))} ∈ target.edges := by simpa using hφ _ he
  exact hcover _ _ _ ht

/-- A real product homomorphism into a graph whose roots meet every edge
has a factor admitting 64 mixed profiles. Root colours have unique core
preimages across all of them, and different indices separate different
core vertices. Private extension vertices are included in the edge claim. -/
theorem product_private_profiles (hd : 0 < d)
    (ht : 512 ≤ Fintype.card Positions)
    (hn : 128 ≤ Fintype.card (Blocks × Positions))
    (A : (i : Fin d) → RGraph (X i) 3) (target : RGraph T 3)
    (guard : (i : Fin d) → Blocks × Positions → X i)
    (hguard : ∀ i, Function.Injective (guard i))
    (hedges : ∀ i x y z, x ≠ y → x ≠ z → y ≠ z →
      x.1 = y.1 → x.1 = z.1 → {guard i x, guard i y, guard i z} ∈ (A i).edges)
    (φ : ((i : Fin d) → ExtensionVertex (X i)) → T)
    (hφ : (RGraph.product fun i => (A i).pairExtension).IsHom target φ)
    (roots : Finset T)
    (hroots : (roots.card : ℝ) ≤ 4 * (Fintype.card (Blocks × Positions) : ℝ) / 3)
    (hcover : ∀ x y z, {x, y, z} ∈ target.edges →
      x ∈ roots ∨ y ∈ roots ∨ z ∈ roots)
    (shift : Positions) (hshift : shift ≠ 0) :
    ∃ j : Fin d, ∃ f : Fin 64 → ExtensionVertex (X j) → T,
      (∀ a b v w c, c ∈ roots → f a (Sum.inl v) = c → f b (Sum.inl w) = c → v = w) ∧
      (∀ a b v w, a ≠ b → v ≠ w → f a (Sum.inl v) ≠ f b (Sum.inl w)) ∧
      ∀ x y z, {x, y, z} ∈ (A j).pairExtension.edges →
        ∀ a b c, a ≠ b → a ≠ c → b ≠ c → {f a x, f b y, f c z} ∈ target.edges := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let ψ : ((i : Fin d) → X i) → T := fun x => φ (fun i => Sum.inl (x i))
  have hψ : SeparatesCoordinates ψ := Selector.product_core_coordinateProper A target φ hφ
  let σ : Blocks × Positions → Blocks × Positions := fun a => (a.1, a.2 + shift)
  have hσinj : Function.Injective σ := by
    intro a b hab
    apply Prod.ext
    · simpa [σ] using congrArg Prod.fst hab
    · exact add_right_cancel (congrArg Prod.snd hab)
  have hσ : ∀ a, σ a ≠ a := by
    intro a ha
    have hs : a.2 + shift = a.2 + 0 := by simpa [σ] using congrArg Prod.snd ha
    exact hshift (add_left_cancel hs)
  have hmissing (k : ℕ) (_hk : k ≤ d) :
      ((nonrootCells (thresholdTable ψ guard k) roots).card : ℝ) ≤
        2 * (Fintype.card (Blocks × Positions) : ℝ) ^ 2 / Fintype.card Positions := by
    have hcount := product_threshold_nonroot_bound hd A target guard hedges φ hφ roots hcover k
    have htpos : (0 : ℝ) < Fintype.card Positions := by
      have : 0 < Fintype.card Positions := by omega
      exact_mod_cast this
    calc
      ((nonrootCells (thresholdTable ψ guard k) roots).card : ℝ) ≤
          2 * (Fintype.card Blocks : ℝ) * Fintype.card Blocks * Fintype.card Positions := by
            exact_mod_cast hcount
      _ = 2 * (Fintype.card (Blocks × Positions) : ℝ) ^ 2 / Fintype.card Positions := by
        rw [Fintype.card_prod, Nat.cast_mul]
        field_simp
        <;> ring
  obtain ⟨j, take, hsame, hprivate⟩ := select_private_profiles ψ hψ guard hguard roots
    (Fintype.card (Blocks × Positions)) (Fintype.card Positions) rfl hn ht hroots hmissing
    Prod.fst (by simp [Nat.mul_comm]) σ hσinj hσ
  let extendedGuard : (i : Fin d) → Blocks × Positions → ExtensionVertex (X i) :=
    fun i a => Sum.inl (guard i a)
  let f : Fin 64 → ExtensionVertex (X j) → T := fun a v =>
    switchMap φ extendedGuard j (take a) v (σ (take a))
  have hcore (a : Fin 64) (v : X j) :
      f a (Sum.inl v) = shiftedProfiles ψ guard j σ (take a) v := by
    dsimp [f, shiftedProfiles, switchMap, ψ]
    congr 1
    funext i
    by_cases hij : i = j
    · subst i
      simp
    · simp only [Function.update_of_ne hij]
      dsimp [thresholdTuple, extendedGuard]
      split <;> rfl
  refine ⟨j, f, ?_, ?_, ?_⟩
  · intro a b v w c hc hav hbw
    exact hprivate a b v w c hc (by rwa [← hcore]) (by rwa [← hcore])
  · intro a b v w hab hvw
    rw [hcore, hcore]
    exact switch_profiles_separated ψ hψ guard hguard j σ hσinj
      (take a) (take b) v w (fun h => hab (take.injective h)) hvw
  · intro x y z he a b c hab hac hbc
    let a' := Function.update (thresholdTuple extendedGuard j.val (take a) (σ (take a))) j x
    let b' := Function.update (thresholdTuple extendedGuard j.val (take b) (σ (take b))) j y
    let c' := Function.update (thresholdTuple extendedGuard j.val (take c) (σ (take c))) j z
    have hpoint (i : Fin d) : {a' i, b' i, c' i} ∈ (A i).pairExtension.edges := by
      by_cases hij : i = j
      · subst i
        simpa [a', b', c'] using he
      · simp only [a', b', c', Function.update_of_ne hij]
        dsimp [thresholdTuple]
        by_cases hi : i.val < j.val
        · simp only [hi, ite_true]
          have h := hedges i (take a) (take b) (take c)
            (fun h => hab (take.injective h)) (fun h => hac (take.injective h))
            (fun h => hbc (take.injective h)) (hsame a b) (hsame a c)
          simpa [extendedGuard] using (core_isHom (A i)) _ h
        · simp only [hi, ite_false]
          have h := hedges i (σ (take a)) (σ (take b)) (σ (take c))
            (fun h => hab (take.injective (hσinj h)))
            (fun h => hac (take.injective (hσinj h)))
            (fun h => hbc (take.injective (hσinj h))) (hsame a b) (hsame a c)
          simpa [extendedGuard] using (core_isHom (A i)) _ h
    have hp := Selector.triple_product_mem (fun i => (A i).pairExtension) a' b' c' hpoint
    simpa [a', b', c', f, switchMap] using hφ _ hp

end TranscendentalTuran.Transfer
