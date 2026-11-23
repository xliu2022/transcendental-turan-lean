module

public import TranscendentalTuran.Network.StageMaps
public import TranscendentalTuran.Network.RelationEnergy

@[expose] public section

/-!
# Exact partition of actual matching blocks into path stages

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network
open scoped BigOperators
attribute [local irreducible] Parameters.q Parameters.N
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

def matchingCenterType : Fin 4 → PhysicalType
  | 0 => .center02 | 1 => .center13 | 2 => .center02 | 3 => .center13
def matchingPortType : Fin 4 → PhysicalType
  | 0 => .port01 | 1 => .port01 | 2 => .port23 | 3 => .port23

theorem matchingCenterType_ne_base (b : Fin 4) : matchingCenterType b ≠ .base := by
  fin_cases b <;> decide

theorem positive_matching_iff (b : Fin 4) (x : V) :
    PositiveAt G μ (matchingBlock b) x ↔
      Declared G μ .base x ∨ Declared G μ (matchingCenterType b) x := by
  constructor
  · rintro ⟨τ, hτ, ht⟩
    fin_cases b <;> cases τ <;> simp_all [matchingBlock, matchingCenterType, sign]
  · rintro (hx | hx)
    · exact ⟨.base, hx, by fin_cases b <;> rfl⟩
    · exact ⟨matchingCenterType b, hx, by fin_cases b <;> rfl⟩

theorem negative_matching_iff (b : Fin 4) (x : V) :
    NegativeAt G μ (matchingBlock b) x ↔ Declared G μ (matchingPortType b) x := by
  constructor
  · rintro ⟨τ, hτ, ht⟩
    fin_cases b <;> cases τ <;> simp_all [matchingBlock, matchingPortType, sign]
  · intro hx
    exact ⟨matchingPortType b, hx, by fin_cases b <;> rfl⟩

def matchingPositiveMap (b : Fin 4) :
    BaseVertex G μ ⊕ TypedVertex G μ (matchingCenterType b) →
      PositiveVertex G μ (matchingBlock b)
  | .inl x => ⟨x.val, (positive_matching_iff b x.val).mpr (Or.inl x.property)⟩
  | .inr x => ⟨x.val, (positive_matching_iff b x.val).mpr (Or.inr x.property)⟩

noncomputable def matchingPositiveEquiv (h : RootedLegal G μ) (b : Fin 4) :
    BaseVertex G μ ⊕ TypedVertex G μ (matchingCenterType b) ≃
      PositiveVertex G μ (matchingBlock b) :=
  Equiv.ofBijective (matchingPositiveMap (G := G) (μ := μ) b) (by
    constructor
    · intro a c he
      have hv := congrArg Subtype.val he
      cases a with
      | inl x =>
        cases c with
        | inl y => exact congrArg Sum.inl (Subtype.ext hv)
        | inr y =>
          change x.val = y.val at hv
          have hh := h.declarations_unique x.val (matchingCenterType b) .base
            (hv ▸ y.property) x.property
          exact False.elim (matchingCenterType_ne_base b hh)
      | inr x =>
        cases c with
        | inl y =>
          change x.val = y.val at hv
          have hh := h.declarations_unique y.val (matchingCenterType b) .base
            (hv ▸ x.property) y.property
          exact False.elim (matchingCenterType_ne_base b hh)
        | inr y => exact congrArg Sum.inr (Subtype.ext hv)
    · intro x
      rcases (positive_matching_iff b x.val).mp x.property with hx | hx
      · exact ⟨.inl ⟨x.val, hx⟩, rfl⟩
      · exact ⟨.inr ⟨x.val, hx⟩, rfl⟩)

def matchingNegativeEquiv (b : Fin 4) :
    TypedVertex G μ (matchingPortType b) ≃ NegativeVertex G μ (matchingBlock b) :=
  Equiv.subtypeEquivRight (fun x => (negative_matching_iff b x).symm)

noncomputable def port01Equiv : EPort01 G μ ⊕ DPort01 G μ ≃ TypedVertex G μ .port01 :=
  Equiv.sumCompl (fun x : TypedVertex G μ .port01 => Port01E G μ x.val)
noncomputable def port23Equiv : EPort23 G μ ⊕ DPort23 G μ ≃ TypedVertex G μ .port23 :=
  Equiv.sumCompl (fun x : TypedVertex G μ .port23 => Port23E G μ x.val)

theorem unionMatchingEnergy_relation (h : RootedLegal G μ) (b : Fin 4) (w : V → ℝ) :
    unionMatchingEnergy (G := G) (μ := μ) b w =
      relationEnergy (fun (c : PositiveVertex G μ (matchingBlock b))
        (l : NegativeVertex G μ (matchingBlock b)) => MatchingEdge G μ b c.val l.val)
        (fun c => w c.val) (fun l => w l.val) := by
  unfold unionMatchingEnergy
  rw [StarEnergy.energy_expansion]
  simp only [StarEnergy.fiberPairs_zero_of_matching (unionLeafCenter_matching h b),
    Finset.sum_const_zero, mul_zero, add_zero]
  simp only [StarEnergy.fiberMass, Finset.mul_sum, mul_ite, mul_zero,
    unionLeafCenter_some_iff h b]
  simp only [relationEnergy, Finset.mul_sum, mul_ite, mul_zero]

end TranscendentalTuran.Source
