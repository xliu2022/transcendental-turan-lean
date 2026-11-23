/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.BoxData
public import TranscendentalTuran.Green.Realization.TemplateCore

@[expose] public section

noncomputable section

namespace TranscendentalTuran.Green.Realization

open Network Encoding FiniteNetwork

private theorem type_map_base {n : ℕ} {o : Option (Box n)} {x : Vertex n}
    (h : o.map base = some x) : type x = .base := by
  cases o with
  | none => cases h
  | some v =>
      have he : base v = x := Option.some.inj h
      exact he ▸ type_base v

theorem box_center_allowed (n : ℕ) (b : Block) (x y : Vertex n)
    (h : center n b y = some x) : AllowedIncidence b (type x) (type y) := by
  rcases y with ⟨τ, v⟩
  cases b <;> cases τ
  all_goals try solve | simp [center] at h
  all_goals cases v <;> simp only [center] at h
  all_goals first
    | (have hx := type_map_base h; simp_all [type, AllowedIncidence])
    | (have hx := Option.some.inj h; subst x; trivial)

/-- The concrete finite subdivision data, before the ordinary triple encoding. -/
def boxData (n : ℕ) : TypedData (Vertex n) where
  type := type
  center := center n
  mark := mark n
  mark_base := type_mark n
  center_allowed := box_center_allowed n

/-- The opposite endpoint of an occupied matching incidence, read from a positive
vertex. This is single-valued because every block is a matching. -/
def mate (n : ℕ) : Block → Vertex n → Option (Vertex n)
  | .match0, ⟨.base, v⟩ => some (port01E (eStart n v))
  | .match0, ⟨.center02, e⟩ => some (port01D e)
  | .match1, ⟨.base, v⟩ => some (port01D (dStart n v))
  | .match1, ⟨.center13, e⟩ => some (port01E e)
  | .match2, ⟨.base, v⟩ => some (port23E (eEnd n v))
  | .match2, ⟨.center02, e⟩ => some (port23D e)
  | .match3, ⟨.base, v⟩ => some (port23D (dEnd n v))
  | .match3, ⟨.center13, e⟩ => some (port23E e)
  | _, _ => none

private theorem map_partialInverse_base {n : ℕ} {A : Type*} (e : Box n ↪ A)
    (a : A) (x : Vertex n) (h : (partialInverse e a).map base = some x) :
    ∃ v, e v = a ∧ base v = x := by
  obtain ⟨v, hv, hx⟩ := Option.map_eq_some_iff.mp h
  exact ⟨v, (partialInverse_some_iff e v a).mp hv, hx⟩

theorem matching_to_mate (n : ℕ) (b : Fin 4) (x y : Vertex n)
    (h : center n (matchingBlock b) y = some x) :
    mate n (matchingBlock b) x = some y := by
  fin_cases b <;> rcases y with ⟨τ, v⟩ <;> cases τ
  all_goals try solve | simp [matchingBlock, center] at h
  all_goals cases v <;> dsimp [matchingBlock, center] at h
  all_goals first
    | (obtain ⟨v, he, hx⟩ := map_partialInverse_base _ _ _ h
       subst x
       subst_vars
       rfl)
    | (have hx := Option.some.inj h; subst x; rfl)

/-- Every occupied matching incidence has a unique negative endpoint. -/
theorem box_matching_left (n : ℕ) (b : Fin 4) (x y z : Vertex n)
    (hy : (boxData n).Matching b x y) (hz : (boxData n).Matching b x z) : y = z := by
  have h1 := matching_to_mate n b x y hy
  have h2 := matching_to_mate n b x z hz
  exact Option.some.inj (h1.symm.trans h2)

/-- Recover a literal vertex in a specified fiber from its type. -/
theorem vertex_of_type {n : ℕ} {x : Vertex n} {τ : PhysicalType} (h : type x = τ) :
    ∃ v : Fiber n τ, x = ⟨τ, v⟩ := by
  rcases x with ⟨σ, v⟩
  change σ = τ at h
  subst τ
  exact ⟨v, rfl⟩

@[simp] theorem vertex_mk_inj {n : ℕ} {τ : PhysicalType} (v w : Fiber n τ) :
    (⟨τ, v⟩ : Vertex n) = ⟨τ, w⟩ ↔ v = w := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    exact congrArg (fun a => (⟨τ, a⟩ : Vertex n)) h


/-- A port remembers its unique possible base incidence, including its color. -/
def baseAddress (n : ℕ) : Vertex n → Option (Fin 4 × Box n)
  | ⟨.port01, Sum.inl e⟩ => (partialInverse (eStart n) e).map (fun v => (0, v))
  | ⟨.port01, Sum.inr e⟩ => (partialInverse (dStart n) e).map (fun v => (1, v))
  | ⟨.port23, Sum.inl e⟩ => (partialInverse (eEnd n) e).map (fun v => (2, v))
  | ⟨.port23, Sum.inr e⟩ => (partialInverse (dEnd n) e).map (fun v => (3, v))
  | _ => none

/-- A port also remembers its unique center incidence and its color. -/
def centerAddress (n : ℕ) : Vertex n → Option (Fin 4 × Vertex n)
  | ⟨.port01, Sum.inl e⟩ => some (1, center13 e)
  | ⟨.port01, Sum.inr e⟩ => some (0, center02 e)
  | ⟨.port23, Sum.inl e⟩ => some (3, center13 e)
  | ⟨.port23, Sum.inr e⟩ => some (2, center02 e)
  | _ => none

@[simp] theorem center02_ne_base {n : ℕ} (e : DAnchor n) (v : Box n) : center02 e ≠ base v := by
  intro h
  have ht := congrArg type h
  cases ht

@[simp] theorem center13_ne_base {n : ℕ} (e : EAnchor n) (v : Box n) : center13 e ≠ base v := by
  intro h
  have ht := congrArg type h
  cases ht

theorem center_base_address (n : ℕ) (b : Fin 4) (v : Box n) (y : Vertex n)
    (h : center n (matchingBlock b) y = some (base v)) :
    baseAddress n y = some (b, v) := by
  fin_cases b <;> rcases y with ⟨τ, a⟩ <;> cases τ
  all_goals try solve | simp [matchingBlock, center] at h
  all_goals cases a <;> dsimp [matchingBlock, center] at h
  all_goals simp only [Option.map_eq_some_iff, Option.some.injEq,
    center02_ne_base, center13_ne_base] at h
  all_goals
    obtain ⟨w, hw, hb⟩ := h
    have hv : w = v := (base_inj w v).mp hb
    subst w
    simp [baseAddress, hw]

theorem center_center_address (n : ℕ) (b : Fin 4) (x y : Vertex n)
    (hx : type x = .center13 ∨ type x = .center02)
    (h : center n (matchingBlock b) y = some x) :
    centerAddress n y = some (b, x) := by
  fin_cases b <;> rcases y with ⟨τ, a⟩ <;> cases τ
  all_goals try solve | simp [matchingBlock, center] at h
  all_goals cases a <;> dsimp [matchingBlock, center] at h
  all_goals first
    | (have ht := type_map_base h; rcases hx with hx | hx <;> rw [ht] at hx <;> cases hx)
    | (have he := Option.some.inj h; subst x; rfl)

theorem box_port_base_unique (n : ℕ) (b c : Fin 4) (x y p : Vertex n)
    (hx : (boxData n).type x = .base) (hy : (boxData n).type y = .base)
    (h1 : (boxData n).Matching b x p) (h2 : (boxData n).Matching c y p) :
    b = c ∧ x = y := by
  obtain ⟨v, rfl⟩ := vertex_of_type hx
  obtain ⟨w, rfl⟩ := vertex_of_type hy
  have hv := center_base_address n b v p h1
  have hw := center_base_address n c w p h2
  have he := Option.some.inj (hv.symm.trans hw)
  exact ⟨congrArg Prod.fst he, congrArg base (congrArg Prod.snd he)⟩

theorem box_port_center_unique (n : ℕ) (b c : Fin 4) (x y p : Vertex n)
    (hx : (boxData n).type x = .center13 ∨ (boxData n).type x = .center02)
    (hy : (boxData n).type y = .center13 ∨ (boxData n).type y = .center02)
    (h1 : (boxData n).Matching b x p) (h2 : (boxData n).Matching c y p) :
    b = c ∧ x = y := by
  have hv := center_center_address n b x p hx h1
  have hw := center_center_address n c y p hy h2
  have he := Option.some.inj (hv.symm.trans hw)
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩


end TranscendentalTuran.Green.Realization
