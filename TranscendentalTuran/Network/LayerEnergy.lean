module

public import TranscendentalTuran.Network.ActualStars
public import TranscendentalTuran.Network.StarEnergy

@[expose] public section

/-!
# The actual individual-layer energy

Formalization author and responsible maintainer: Xizhi Liu.

All components are obtained from the link at the given root. Repetition-block
unions occur only when ruling out an owner, and are not substituted for the
actual layer's components.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

abbrev PositiveVertex (G : RGraph V 3) (μ : Rooting Root V) (b : Block) :=
  {x : V // PositiveAt G μ b x}

abbrev NegativeVertex (G : RGraph V 3) (μ : Rooting Root V) (b : Block) :=
  {x : V // NegativeAt G μ b x}

noncomputable instance (b : Block) : Fintype (PositiveVertex G μ b) := Fintype.ofFinite _
noncomputable instance (b : Block) : Fintype (NegativeVertex G μ b) := Fintype.ofFinite _

noncomputable def leafCenter (r : Layer) (l : NegativeVertex G μ r.1) :
    Option (PositiveVertex G μ r.1) := by
  classical
  exact if h : ∃ c : PositiveVertex G μ r.1, CrossAt G μ r c.val l.val then
    some h.choose else none

theorem leafCenter_some_iff (h : RootedLegal G μ) (r : Layer)
    (l : NegativeVertex G μ r.1) (c : PositiveVertex G μ r.1) :
    leafCenter r l = some c ↔ CrossAt G μ r c.val l.val := by
  classical
  by_cases he : ∃ c : PositiveVertex G μ r.1, CrossAt G μ r c.val l.val
  · rw [leafCenter, dite_eq_left he, Option.some.injEq]
    constructor
    · intro hc
      exact hc ▸ he.choose_spec
    · intro hc
      apply Subtype.ext
      exact crossAt_unique_center h r he.choose_spec hc
  · rw [leafCenter, dite_eq_right he]
    constructor
    · intro hc; cases hc
    · intro hc; exact False.elim (he ⟨c, hc⟩)

theorem leafCenter_none_iff (h : RootedLegal G μ) (r : Layer)
    (l : NegativeVertex G μ r.1) :
    leafCenter r l = none ↔ ∀ c : PositiveVertex G μ r.1, ¬ CrossAt G μ r c.val l.val := by
  classical
  constructor
  · intro hn c hc
    have hs := (leafCenter_some_iff h r l c).mpr hc
    rw [hn] at hs
    cases hs
  · intro hall
    cases he : leafCenter r l with
    | none => rfl
    | some c => exact False.elim (hall c ((leafCenter_some_iff h r l c).mp he))

noncomputable def actualLayerEnergy (r : Layer) (w : V → ℝ) : ℝ :=
  StarEnergy.energy (leafCenter (G := G) (μ := μ) r)
    (fun c => w c.val) (fun l => w l.val)

noncomputable def actualEnergy (z : Root → ℝ) (w : V → ℝ) : ℝ :=
  ∑ r : Layer, z (layerRoot r) * actualLayerEnergy (G := G) (μ := μ) r w

theorem actualLayerEnergy_nonneg (r : Layer) (w : V → ℝ) :
    0 ≤ actualLayerEnergy (G := G) (μ := μ) r w := StarEnergy.energy_nonneg _ _ _

theorem actualEnergy_nonneg (z : Root → ℝ) (w : V → ℝ) (hz : ∀ r, 0 ≤ z r) :
    0 ≤ actualEnergy (G := G) (μ := μ) z w :=
  Finset.sum_nonneg fun r _ => mul_nonneg (hz _) (actualLayerEnergy_nonneg r w)

theorem actualLayer_square_identity (r : Layer) (w : V → ℝ) :
    StarEnergy.permittedPairWeight (leafCenter (G := G) (μ := μ) r)
        (fun c => w c.val) (fun l => w l.val) =
      ((∑ c : PositiveVertex G μ r.1, w c.val) ^ 2 +
        (∑ l : NegativeVertex G μ r.1, w l.val) ^ 2 -
          actualLayerEnergy (G := G) (μ := μ) r w) / 2 :=
  StarEnergy.square_identity _ _ _

theorem leafCenter_ownerH_missing (h : RootedLegal G μ) (j : Fin Parameters.κ)
    (l : NegativeVertex G μ .ownerH) (hl : ¬ ∃ c, OwnerEdge G μ 0 l.val c) :
    leafCenter (G := G) (μ := μ) ⟨.ownerH, j⟩ l = none := by
  apply (leafCenter_none_iff (G := G) (μ := μ) h ⟨.ownerH, j⟩ l).mpr
  intro c hc
  exact hl ⟨c.val, hc.ownerH h j⟩

theorem leafCenter_ownerV_missing (h : RootedLegal G μ) (j : Fin Parameters.κ)
    (l : NegativeVertex G μ .ownerV) (hl : ¬ ∃ c, OwnerEdge G μ 1 l.val c) :
    leafCenter (G := G) (μ := μ) ⟨.ownerV, j⟩ l = none := by
  apply (leafCenter_none_iff (G := G) (μ := μ) h ⟨.ownerV, j⟩ l).mpr
  intro c hc
  exact hl ⟨c.val, hc.ownerV h j⟩

theorem singleton_square_le_layer (r : Layer) (w : V → ℝ)
    (l : NegativeVertex G μ r.1) (hl : leafCenter r l = none) :
    w l.val ^ 2 ≤ actualLayerEnergy (G := G) (μ := μ) r w := by
  classical
  have hu := StarEnergy.unmatched_penalty (leafCenter (G := G) (μ := μ) r)
    (fun c => w c.val) (fun a => w a.val)
  have hs : (if leafCenter r l = none then w l.val ^ 2 else 0) ≤
      ∑ a : NegativeVertex G μ r.1, if leafCenter r a = none then w a.val ^ 2 else 0 := by
    apply Finset.single_le_sum (s := Finset.univ) (a := l)
      (f := fun a : NegativeVertex G μ r.1 =>
        if leafCenter (G := G) (μ := μ) r a = none then w a.val ^ 2 else 0)
    · intro a _
      split_ifs <;> first | exact sq_nonneg _ | exact le_rfl
    · exact Finset.mem_univ _
  rw [ite_eq_left hl] at hs
  exact hs.trans hu

end TranscendentalTuran.Source
