module

public import TranscendentalTuran.Algebra.Legacy.RationalProjection
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace TuranUniversality.Algebraicity.QSemialgebraic

open Set

universe u

variable {σ : Type u}

/-- Eliminate an arbitrary finite block of real coordinates, retaining an
explicit rational semialgebraic description of the parameter set. -/
theorem exists_fin (n : ℕ) {S : Set (Fin n ⊕ σ → ℝ)} (hS : QSemialgebraic S) :
    QSemialgebraic {x : σ → ℝ | ∃ y : Fin n → ℝ, Sum.elim y x ∈ S} := by
  induction n with
  | zero =>
      let f : Fin 0 ⊕ σ → σ := Sum.elim Fin.elim0 id
      apply (hS.preimage_rename f).congr
      ext x
      change (x ∘ f ∈ S) ↔ ∃ y : Fin 0 → ℝ, Sum.elim y x ∈ S
      constructor
      · intro hx
        refine ⟨Fin.elim0, ?_⟩
        convert hx using 1
        funext i
        cases i with
        | inl i => exact Fin.elim0 i
        | inr i => rfl
      · rintro ⟨y, hy⟩
        convert hy using 1
        funext i
        cases i with
        | inl i => exact Fin.elim0 i
        | inr i => rfl
  | succ n ih =>
      let f : Fin (n + 1) ⊕ σ → Option (Fin n ⊕ σ) := Sum.elim
        (Fin.cases none (fun i => some (Sum.inl i))) (fun i => some (Sum.inr i))
      have hstep := (hS.preimage_rename f).exists_one
      have hrest := ih hstep
      apply hrest.congr
      ext x
      change (∃ y : Fin n → ℝ, ∃ z : ℝ,
        ((fun i => i.elim z (Sum.elim y x)) ∘ f) ∈ S) ↔
        ∃ y : Fin (n + 1) → ℝ, Sum.elim y x ∈ S
      constructor
      · rintro ⟨y, z, hy⟩
        refine ⟨Fin.cons z y, ?_⟩
        convert hy using 1
        funext i
        cases i with
        | inl i => cases i using Fin.cases <;> simp [f, Function.comp_def]
        | inr i => rfl
      · rintro ⟨y, hy⟩
        refine ⟨Fin.tail y, y 0, ?_⟩
        convert hy using 1
        funext i
        cases i with
        | inl i => cases i using Fin.cases <;> simp [f, Function.comp_def, Fin.tail]
        | inr i => rfl

theorem forall_fin (n : ℕ) {S : Set (Fin n ⊕ σ → ℝ)} (hS : QSemialgebraic S) :
    QSemialgebraic {x : σ → ℝ | ∀ y : Fin n → ℝ, Sum.elim y x ∈ S} := by
  apply (exists_fin n hS.compl).compl.congr
  ext x
  simp

theorem exists_finite {I : Type*} [Fintype I] {S : Set (I ⊕ σ → ℝ)}
    (hS : QSemialgebraic S) :
    QSemialgebraic {x : σ → ℝ | ∃ y : I → ℝ, Sum.elim y x ∈ S} := by
  classical
  let e := Fintype.equivFin I
  have h := exists_fin (Fintype.card I) (hS.preimage_rename (Sum.map e id))
  apply h.congr
  ext x
  change (∃ y : Fin (Fintype.card I) → ℝ,
      (Sum.elim y x ∘ Sum.map e id) ∈ S) ↔ ∃ y : I → ℝ, Sum.elim y x ∈ S
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ∘ e, ?_⟩
    convert hy using 1
    funext i
    cases i <;> rfl
  · rintro ⟨y, hy⟩
    refine ⟨y ∘ e.symm, ?_⟩
    convert hy using 1
    funext i
    cases i <;> simp [Function.comp_def]

theorem forall_finite {I : Type*} [Fintype I] {S : Set (I ⊕ σ → ℝ)}
    (hS : QSemialgebraic S) :
    QSemialgebraic {x : σ → ℝ | ∀ y : I → ℝ, Sum.elim y x ∈ S} := by
  apply hS.compl.exists_finite.compl.congr
  ext x
  simp

end TuranUniversality.Algebraicity.QSemialgebraic
