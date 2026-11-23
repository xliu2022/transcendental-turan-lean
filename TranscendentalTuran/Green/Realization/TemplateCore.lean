/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Encoding.Layout
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

namespace TranscendentalTuran.Green.Realization

open Network Encoding Parameters

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

/-- Concrete data for a typed source host.  The function `center` gives the unique
positive center of each negative leaf in each block.  All repetitions of a block
use these same incidences. -/
structure TypedData (D : Type*) where
  type : D → PhysicalType
  center : Block → D → Option D
  mark : D
  mark_base : type mark = .base
  center_allowed : ∀ b x y, center b y = some x → AllowedIncidence b (type x) (type y)

namespace TypedData

variable {D : Type*} (H : TypedData D)

/-- The full permitted pair set of a signed-star layer. -/
def LayerPair (b : Block) (x y : D) : Prop :=
  x ≠ y ∧ Active b (H.type x) ∧ Active b (H.type y) ∧
    (H.center b y = some x ∨ H.center b x = some y ∨
      (sign b (H.type x) = sign b (H.type y) ∧
        ¬ ∃ c, H.center b x = some c ∧ H.center b y = some c))

theorem layerPair_symm (b : Block) (x y : D) : H.LayerPair b x y ↔ H.LayerPair b y x := by
  unfold LayerPair
  constructor <;> rintro ⟨hne, hx, hy, h⟩
  · refine ⟨hne.symm, hy, hx, ?_⟩
    rcases h with h | h | ⟨hs, hc⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hs.symm, fun ⟨c, h1, h2⟩ => hc ⟨c, h2, h1⟩⟩)
  · refine ⟨hne.symm, hy, hx, ?_⟩
    rcases h with h | h | ⟨hs, hc⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hs.symm, fun ⟨c, h1, h2⟩ => hc ⟨c, h2, h1⟩⟩)

theorem center_signs {b : Block} {x y : D} (h : H.center b y = some x) :
    sign b (H.type x) = 1 ∧ sign b (H.type y) = -1 :=
  incidence_signs (H.center_allowed b x y h)

theorem center_irrefl (b : Block) (x : D) : H.center b x ≠ some x := by
  intro h
  have hs := H.center_signs h
  omega

theorem center_layerPair {b : Block} {x y : D} (h : H.center b y = some x) :
    H.LayerPair b x y := by
  have hs := H.center_signs h
  refine ⟨?_, ?_, ?_, Or.inl h⟩
  · intro he
    subst y
    exact H.center_irrefl b x h
  · unfold Active
    rw [hs.1]
    norm_num
  · unfold Active
    rw [hs.2]
    norm_num

/-- Opposite-sign links are exactly the declared structural incidences. -/
theorem layerPair_opposite {b : Block} {x y : D}
    (h : H.LayerPair b x y) (hs : sign b (H.type x) = -sign b (H.type y)) :
    H.center b y = some x ∨ H.center b x = some y := by
  rcases h.2.2.2 with h | h | ⟨he, _⟩
  · exact Or.inl h
  · exact Or.inr h
  · have hx := h.2.1
    unfold Active at hx
    omega

/-- Two leaves in a common star never form a permitted same-component pair. -/
theorem no_pair_of_shared_neighbor {b : Block} {x y c : D}
    (hx : H.center b c = some x ∨ H.center b x = some c)
    (hy : H.center b c = some y ∨ H.center b y = some c) :
    ¬ H.LayerPair b x y := by
  intro hp
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hp.1 (Option.some.inj (hx.symm.trans hy))
  · have h1 := H.center_signs hx
    have h2 := H.center_signs hy
    omega
  · have h1 := H.center_signs hx
    have h2 := H.center_signs hy
    omega
  · rcases hp.2.2.2 with h | h | ⟨_, hn⟩
    · have h1 := H.center_signs h
      have h2 := H.center_signs hx
      omega
    · have h1 := H.center_signs h
      have h2 := H.center_signs hy
      omega
    · exact hn ⟨c, hx, hy⟩

def Matching (b : Fin 4) (x y : D) : Prop := H.center (matchingBlock b) y = some x

def Owner (b : Fin 2) (x o : D) : Prop :=
  H.center (if b = 0 then .ownerH else .ownerV) x = some o

def CompleteE (x y : D) : Prop :=
  H.type x = .base ∧ H.type y = .base ∧
  ∃ p c p', H.type p = .port01 ∧ H.type c = .center13 ∧ H.type p' = .port23 ∧
    H.Matching 0 x p ∧ H.Matching 1 c p ∧ H.Matching 3 c p' ∧ H.Matching 2 y p'

def CompleteD (x y : D) : Prop :=
  H.type x = .base ∧ H.type y = .base ∧
  ∃ p c p', H.type p = .port01 ∧ H.type c = .center02 ∧ H.type p' = .port23 ∧
    H.Matching 1 x p ∧ H.Matching 0 c p ∧ H.Matching 2 c p' ∧ H.Matching 3 y p'

def ParentH (a b : D) : Prop :=
  ∃ x y, (H.CompleteE x y ∨ H.CompleteD x y) ∧ H.Owner 0 x a ∧ H.Owner 0 y b

def ParentV (a b : D) : Prop :=
  ∃ x y, H.CompleteD x y ∧ H.Owner 1 y a ∧ H.Owner 1 x b

/-- The remaining finite structural conditions of the manuscript, stated before
encoding the data into ordinary triples. -/
structure Legal : Prop where
  matching_left : ∀ b x y z, H.Matching b x y → H.Matching b x z → y = z
  port_base_unique : ∀ b c x y p, H.type x = .base → H.type y = .base →
    H.Matching b x p → H.Matching c y p → b = c ∧ x = y
  port_center_unique : ∀ b c x y p,
    (H.type x = .center13 ∨ H.type x = .center02) →
    (H.type y = .center13 ∨ H.type y = .center02) →
    H.Matching b x p → H.Matching c y p → b = c ∧ x = y
  E_preserves_vertical : ∀ x y a b, H.CompleteE x y → H.Owner 1 x a → H.Owner 1 y b → a = b
  parentH_unique : ∀ a b c, H.ParentH a c → H.ParentH b c → a = b
  parentV_unique : ∀ a b c, H.ParentV a c → H.ParentV b c → a = b
  boundaryH : ∀ x y o, H.Owner 0 H.mark o → H.Owner 0 x o →
    ¬ (H.CompleteE y x ∨ H.CompleteD y x)
  boundaryV : ∀ x y o, H.Owner 1 H.mark o → H.Owner 1 x o → ¬ H.CompleteD x y

end TypedData

/-- The unique special block of a root, or no block for generic/passive roots. -/
def rootBlock (r : Root) : Option Block :=
  if r.val < M then some .match0 else
  if r.val < 2 * M then some .match1 else
  if r.val < 3 * M then some .match2 else
  if r.val < 4 * M then some .match3 else
  if r.val < 4 * M + κ then some .ownerH else
  if r.val < K then some .ownerV else none

@[simp] theorem rootBlock_layerRoot (r : Layer) : rootBlock (layerRoot r) = some r.1 := by
  rcases r with ⟨b, j⟩
  cases b <;> have hj := j.isLt
  all_goals
    simp only [rootBlock, layerRoot, matchingRoot, ownershipRoot]
    norm_num [repetitions, M, κ, K] at hj ⊢
    split_ifs <;> simp_all <;> omega

theorem rootBlock_none_of_ge {r : Root} (h : K ≤ r.val) : rootBlock r = none := by
  change 10240 ≤ r.val at h
  have h0 : ¬ r.val < 512 := by omega
  have h1 : ¬ r.val < 1024 := by omega
  have h2 : ¬ r.val < 1536 := by omega
  have h3 : ¬ r.val < 2048 := by omega
  have h4 : ¬ r.val < 6144 := by omega
  have h5 : ¬ r.val < 10240 := by omega
  simp [rootBlock, M, κ, K, h0, h1, h2, h3, h4, h5]

theorem rootBlock_some_lt {r : Root} {b : Block} (h : rootBlock r = some b) : r.val < K := by
  by_contra hn
  have hh := rootBlock_none_of_ge (r := r) (by omega)
  rw [hh] at h
  cases h

end TranscendentalTuran.Green.Realization
