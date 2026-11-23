module

public import TranscendentalTuran.Green.Realization.TemplateCore

@[expose] public section

/-!
# Isolated typed fillers preserve all ordinary structural rules

Formalization author and responsible maintainer: Xizhi Liu.

Every new data vertex has its prescribed physical type and no structural
center. The old mark and all old incidences are retained. In the full
permitted ordinary graph the fillers still receive their prescribed dense
same-sign and generic links; only the structural incidences are absent.
-/

namespace TranscendentalTuran.Green.Realization.TypedData

open Network Encoding Parameters

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D F : Type*} (H : TypedData D) (τ : F → PhysicalType)

def withFillers : TypedData (D ⊕ F) where
  type := Sum.elim H.type τ
  center b := Sum.elim (fun d => (H.center b d).map Sum.inl) (fun _ => none)
  mark := Sum.inl H.mark
  mark_base := H.mark_base
  center_allowed := by
    intro b x y h
    cases y with
    | inr f => cases h
    | inl d =>
      cases hc : H.center b d with
      | none => simp [hc] at h
      | some c =>
        have hx : Sum.inl c = x := by simpa [hc] using h
        subst x
        exact H.center_allowed b c d hc

@[simp] theorem withFillers_type_old (d : D) : (H.withFillers τ).type (Sum.inl d) = H.type d := rfl
@[simp] theorem withFillers_type_new (f : F) : (H.withFillers τ).type (Sum.inr f) = τ f := rfl
@[simp] theorem withFillers_mark : (H.withFillers τ).mark = Sum.inl H.mark := rfl

@[simp] theorem withFillers_center_old (b : Block) (d : D) :
    (H.withFillers τ).center b (Sum.inl d) = (H.center b d).map Sum.inl := rfl

@[simp] theorem withFillers_center_new (b : Block) (f : F) :
    (H.withFillers τ).center b (Sum.inr f) = none := rfl

@[simp] theorem withFillers_center_old_old (b : Block) (x y : D) :
    (H.withFillers τ).center b (Sum.inl y) = some (Sum.inl x) ↔ H.center b y = some x := by
  cases hc : H.center b y <;> simp [hc]

@[simp] theorem withFillers_center_new_target (b : Block) (x : D ⊕ F) (f : F) :
    (H.withFillers τ).center b x ≠ some (Sum.inr f) := by
  cases x with
  | inl d => cases hc : H.center b d <;> simp [hc]
  | inr g => simp

@[simp] theorem withFillers_matching_old (b : Fin 4) (x y : D) :
    (H.withFillers τ).Matching b (Sum.inl x) (Sum.inl y) ↔ H.Matching b x y := by
  exact H.withFillers_center_old_old τ _ _ _

@[simp] theorem withFillers_matching_new_left (b : Fin 4) (f : F) (y : D ⊕ F) :
    ¬ (H.withFillers τ).Matching b (Sum.inr f) y :=
  H.withFillers_center_new_target τ _ _ _

@[simp] theorem withFillers_matching_new_right (b : Fin 4) (x : D ⊕ F) (f : F) :
    ¬ (H.withFillers τ).Matching b x (Sum.inr f) := by
  simp [Matching]

@[simp] theorem withFillers_owner_old (b : Fin 2) (x o : D) :
    (H.withFillers τ).Owner b (Sum.inl x) (Sum.inl o) ↔ H.Owner b x o := by
  exact H.withFillers_center_old_old τ _ _ _

@[simp] theorem withFillers_owner_new_left (b : Fin 2) (f : F) (o : D ⊕ F) :
    ¬ (H.withFillers τ).Owner b (Sum.inr f) o := by
  simp [Owner]

@[simp] theorem withFillers_owner_new_right (b : Fin 2) (x : D ⊕ F) (f : F) :
    ¬ (H.withFillers τ).Owner b x (Sum.inr f) :=
  H.withFillers_center_new_target τ _ _ _

@[simp] theorem withFillers_completeE_old (x y : D) :
    (H.withFillers τ).CompleteE (Sum.inl x) (Sum.inl y) ↔ H.CompleteE x y := by
  simp [CompleteE, Sum.exists]

@[simp] theorem withFillers_completeD_old (x y : D) :
    (H.withFillers τ).CompleteD (Sum.inl x) (Sum.inl y) ↔ H.CompleteD x y := by
  simp [CompleteD, Sum.exists]

@[simp] theorem withFillers_completeE_new_left (f : F) (y : D ⊕ F) :
    ¬ (H.withFillers τ).CompleteE (Sum.inr f) y := by
  rintro ⟨_, _, p, c, t, _, _, _, hxp, _, _, _⟩
  exact H.withFillers_matching_new_left τ 0 f p hxp

@[simp] theorem withFillers_completeE_new_right (x : D ⊕ F) (f : F) :
    ¬ (H.withFillers τ).CompleteE x (Sum.inr f) := by
  rintro ⟨_, _, p, c, t, _, _, _, _, _, _, hyt⟩
  exact H.withFillers_matching_new_left τ 2 f t hyt

@[simp] theorem withFillers_completeD_new_left (f : F) (y : D ⊕ F) :
    ¬ (H.withFillers τ).CompleteD (Sum.inr f) y := by
  rintro ⟨_, _, p, c, t, _, _, _, hxp, _, _, _⟩
  exact H.withFillers_matching_new_left τ 1 f p hxp

@[simp] theorem withFillers_completeD_new_right (x : D ⊕ F) (f : F) :
    ¬ (H.withFillers τ).CompleteD x (Sum.inr f) := by
  rintro ⟨_, _, p, c, t, _, _, _, _, _, _, hyt⟩
  exact H.withFillers_matching_new_left τ 3 f t hyt

@[simp] theorem withFillers_parentH_old (a b : D) :
    (H.withFillers τ).ParentH (Sum.inl a) (Sum.inl b) ↔ H.ParentH a b := by
  simp [ParentH, Sum.exists]

@[simp] theorem withFillers_parentV_old (a b : D) :
    (H.withFillers τ).ParentV (Sum.inl a) (Sum.inl b) ↔ H.ParentV a b := by
  simp [ParentV, Sum.exists]

@[simp] theorem withFillers_parentH_new_left (f : F) (b : D ⊕ F) :
    ¬ (H.withFillers τ).ParentH (Sum.inr f) b := by
  rintro ⟨x, y, _, hx, _⟩
  exact H.withFillers_owner_new_right τ 0 x f hx

@[simp] theorem withFillers_parentH_new_right (a : D ⊕ F) (f : F) :
    ¬ (H.withFillers τ).ParentH a (Sum.inr f) := by
  rintro ⟨x, y, _, _, hy⟩
  exact H.withFillers_owner_new_right τ 0 y f hy

@[simp] theorem withFillers_parentV_new_left (f : F) (b : D ⊕ F) :
    ¬ (H.withFillers τ).ParentV (Sum.inr f) b := by
  rintro ⟨x, y, _, hy, _⟩
  exact H.withFillers_owner_new_right τ 1 y f hy

@[simp] theorem withFillers_parentV_new_right (a : D ⊕ F) (f : F) :
    ¬ (H.withFillers τ).ParentV a (Sum.inr f) := by
  rintro ⟨x, y, _, _, hx⟩
  exact H.withFillers_owner_new_right τ 1 x f hx

theorem withFillers_legal (hL : H.Legal) : (H.withFillers τ).Legal where
  matching_left b x y z hxy hxz := by
    cases x <;> cases y <;> cases z <;> simp_all
    exact hL.matching_left _ _ _ _ hxy hxz
  port_base_unique b c x y p hx hy hxp hyp := by
    cases x <;> cases y <;> cases p <;> simp_all
    exact hL.port_base_unique _ _ _ _ _
      (by first | rfl | assumption) (by first | rfl | assumption) hxp hyp
  port_center_unique b c x y p hx hy hxp hyp := by
    cases x <;> cases y <;> cases p <;> simp_all
    exact hL.port_center_unique _ _ _ _ _ hx hy hxp hyp
  E_preserves_vertical x y a b hxy hxa hyb := by
    cases x <;> cases y <;> cases a <;> cases b <;> simp_all
    exact hL.E_preserves_vertical _ _ _ _ hxy hxa hyb
  parentH_unique a b c hac hbc := by
    cases a <;> cases b <;> cases c <;> simp_all
    exact hL.parentH_unique _ _ _ hac hbc
  parentV_unique a b c hac hbc := by
    cases a <;> cases b <;> cases c <;> simp_all
    exact hL.parentV_unique _ _ _ hac hbc
  boundaryH x y o hmo hxo := by
    cases x <;> cases y <;> cases o <;> simp_all
    exact not_or.mp (hL.boundaryH _ _ _ hmo hxo)
  boundaryV x y o hmo hxo := by
    cases x <;> cases y <;> cases o <;> simp_all
    exact hL.boundaryV _ _ _ hmo hxo

end TranscendentalTuran.Green.Realization.TypedData
