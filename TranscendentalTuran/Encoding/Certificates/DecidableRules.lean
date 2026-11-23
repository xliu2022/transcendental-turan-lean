module

public import TranscendentalTuran.Encoding.LocalRules

@[expose] public section

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000
set_option synthInstance.maxSize 4096
-- The root set is enormous. Preserve the finite decision procedures without
-- asking the compiler to precompute their closed enumeration tables.
set_option compiler.extract_closed false

variable {V : Type*} [Fintype V] [DecidableEq V]

local instance (μ : Rooting Root V) (x : V) : Decidable (x ∈ μ.range) :=
  decidable_of_iff (∃ r, μ.val r = some x) (Rooting.mem_range μ x).symm

instance (μ : Rooting Root V) (x : V) : Decidable (Data μ x) :=
  decidable_of_iff (∀ r, μ.val r ≠ some x) (by
    simp only [Data, Rooting.mem_range, not_exists])
instance (G : RGraph V 3) (μ : Rooting Root V) (r : Root) (x y : V) :
    Decidable (Link G μ r x y) := by unfold Link; infer_instance
instance (G : RGraph V 3) (μ : Rooting Root V) (r s : Root) (x : V) :
    Decidable (PairLink G μ r s x) := by unfold PairLink; infer_instance
instance (G : RGraph V 3) (μ : Rooting Root V) (x : V) :
    Decidable (Marked G μ x) := by unfold Marked; infer_instance
instance (G : RGraph V 3) (μ : Rooting Root V) (τ : PhysicalType) (x : V) :
    Decidable (Declared G μ τ x) := by unfold Declared; infer_instance
instance (G : RGraph V 3) (μ : Rooting Root V) (b : Fin 4) (x y : V) :
    Decidable (MatchingEdge G μ b x y) := by unfold MatchingEdge; infer_instance
instance (G : RGraph V 3) (μ : Rooting Root V) (b : Fin 2) (x o : V) :
    Decidable (OwnerEdge G μ b x o) := by unfold OwnerEdge; infer_instance
instance (G : RGraph V 3) (μ : Rooting Root V) (x : V) :
    Decidable (IsCenter G μ x) := by unfold IsCenter; infer_instance
instance (G : RGraph V 3) (μ : Rooting Root V) (x y : V) :
    Decidable (CompleteE G μ x y) := by unfold CompleteE; infer_instance
instance (G : RGraph V 3) (μ : Rooting Root V) (x y : V) :
    Decidable (CompleteD G μ x y) := by unfold CompleteD; infer_instance
instance (G : RGraph V 3) (μ : Rooting Root V) (a b : V) :
    Decidable (ParentH G μ a b) := by unfold ParentH; infer_instance
instance (G : RGraph V 3) (μ : Rooting Root V) (a b : V) :
    Decidable (ParentV G μ a b) := by unfold ParentV; infer_instance
instance (G : RGraph V 3) (μ : Rooting Root V) (r : Layer) (x y : V) :
    Decidable (StructuralAt G μ r x y) := by unfold StructuralAt; infer_instance

def LegalConditions (G : RGraph V 3) (μ : Rooting Root V) : Prop :=
  (∀ e ∈ G.edges, ∃ v ∈ e, v ∈ μ.range) ∧
  (∀ r, IsPassive r → ∀ x y, ¬ Link G μ r x y) ∧
  (∀ x τ σ, Declared G μ τ x → Declared G μ σ x → τ = σ) ∧
  (∀ r, IsGeneric r → ∀ x y τ σ,
    Declared G μ τ x → Declared G μ σ y → Link G μ r x y → τ ≠ σ) ∧
  (∀ r x y τ σ,
    Declared G μ τ x → Declared G μ σ y → Link G μ (layerRoot r) x y →
    Active r.1 τ ∧ Active r.1 σ ∧
      (sign r.1 τ = sign r.1 σ ∨ AllowedIncidence r.1 τ σ ∨ AllowedIncidence r.1 σ τ)) ∧
  (∀ b x y z, MatchingEdge G μ b x y → MatchingEdge G μ b x z → y = z) ∧
  (∀ b x y z, MatchingEdge G μ b x z → MatchingEdge G μ b y z → x = y) ∧
  (∀ b c x y p, Declared G μ .base x → Declared G μ .base y →
    MatchingEdge G μ b x p → MatchingEdge G μ c y p → b = c ∧ x = y) ∧
  (∀ b c x y p, IsCenter G μ x → IsCenter G μ y →
    MatchingEdge G μ b x p → MatchingEdge G μ c y p → b = c ∧ x = y) ∧
  (∀ b x a a', OwnerEdge G μ b x a → OwnerEdge G μ b x a' → a = a') ∧
  (∀ r x y c, StructuralAt G μ r x c → StructuralAt G μ r y c →
    ¬ Link G μ (layerRoot r) x y) ∧
  (∀ x y, Marked G μ x → Marked G μ y → x = y) ∧
  (∀ x y a b, CompleteE G μ x y → OwnerEdge G μ 1 x a → OwnerEdge G μ 1 y b → a = b) ∧
  (∀ a b c, ParentH G μ a c → ParentH G μ b c → a = b) ∧
  (∀ a b c, ParentV G μ a c → ParentV G μ b c → a = b) ∧
  (∀ m x y o, Marked G μ m → OwnerEdge G μ 0 m o → OwnerEdge G μ 0 x o →
    ¬ (CompleteE G μ y x ∨ CompleteD G μ y x)) ∧
  (∀ m x y o, Marked G μ m → OwnerEdge G μ 1 m o → OwnerEdge G μ 1 x o →
    ¬ CompleteD G μ x y)

theorem rootedLegal_iff_conditions (G : RGraph V 3) (μ : Rooting Root V) :
    RootedLegal G μ ↔ LegalConditions G μ := by
  constructor
  · intro h
    exact ⟨h.covers_edges, h.passive_empty, h.declarations_unique, h.generic_different,
      h.special_allowed, h.matching_left, h.matching_right, h.port_base_unique,
      h.port_center_unique, h.owner_functional, h.same_component_forbidden,
      h.marks_unique, h.E_preserves_vertical, h.parentH_unique, h.parentV_unique,
      h.boundaryH, h.boundaryV⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩

instance (G : RGraph V 3) (μ : Rooting Root V) : Decidable (LegalConditions G μ) := by
  unfold LegalConditions IsPassive IsGeneric
  infer_instance

instance (G : RGraph V 3) (μ : Rooting Root V) : Decidable (RootedLegal G μ) :=
  decidable_of_iff (LegalConditions G μ) (rootedLegal_iff_conditions G μ).symm

instance (G : RGraph V 3) : Decidable (Admissible G) := by
  unfold Admissible
  infer_instance

end TranscendentalTuran.Source
