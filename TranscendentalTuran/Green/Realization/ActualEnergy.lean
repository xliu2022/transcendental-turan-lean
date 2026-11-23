module

public import TranscendentalTuran.Green.Realization.TemplateGraph
public import TranscendentalTuran.Network.LayerEnergy

@[expose] public section

/-!
# Actual layer energies of the ordinary lower realization

Formalization author and responsible maintainer: Xizhi Liu.

The star assignment in the literal ordinary graph is the supplied `center`
function. The final formula sums over the original data type, so the box
construction can evaluate its fibers without rebuilding subtype equivalences.
-/

namespace TranscendentalTuran.Green.Realization.TypedData

open Network Encoding Parameters TuranUniversality Source
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D] (H : TypedData D)

abbrev PositiveData (b : Block) := {d : D // sign b (H.type d) = 1}
abbrev NegativeData (b : Block) := {d : D // sign b (H.type d) = -1}

noncomputable instance (b : Block) : Fintype (H.PositiveData b) := Fintype.ofFinite _
noncomputable instance (b : Block) : Fintype (H.NegativeData b) := Fintype.ofFinite _

theorem graph_positive_iff (b : Block) (d : D) :
    PositiveAt H.graph (sumRooting D) b (Sum.inr d) ↔ sign b (H.type d) = 1 := by
  constructor
  · rintro ⟨τ, ht, hs⟩
    exact (H.graph_declared τ d).mp ht ▸ hs
  · intro hs
    exact ⟨H.type d, (H.graph_declared _ _).mpr rfl, hs⟩

theorem graph_negative_iff (b : Block) (d : D) :
    NegativeAt H.graph (sumRooting D) b (Sum.inr d) ↔ sign b (H.type d) = -1 := by
  constructor
  · rintro ⟨τ, ht, hs⟩
    exact (H.graph_declared τ d).mp ht ▸ hs
  · intro hs
    exact ⟨H.type d, (H.graph_declared _ _).mpr rfl, hs⟩

def positiveInr (b : Block) (d : H.PositiveData b) :
    PositiveVertex H.graph (sumRooting D) b :=
  ⟨Sum.inr d.val, (H.graph_positive_iff b d.val).mpr d.property⟩

def negativeInr (b : Block) (d : H.NegativeData b) :
    NegativeVertex H.graph (sumRooting D) b :=
  ⟨Sum.inr d.val, (H.graph_negative_iff b d.val).mpr d.property⟩

theorem positiveInr_bijective (b : Block) : Function.Bijective (H.positiveInr b) := by
  constructor
  · intro x y h
    exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
  · intro c
    obtain ⟨τ, ht, hs⟩ := c.property
    obtain ⟨d, hd⟩ := sumRooting_data_exists ht.1
    have hsign : sign b (H.type d) = 1 := by
      apply (H.graph_positive_iff b d).mp
      exact hd ▸ c.property
    exact ⟨⟨d, hsign⟩, Subtype.ext hd.symm⟩

theorem negativeInr_bijective (b : Block) : Function.Bijective (H.negativeInr b) := by
  constructor
  · intro x y h
    exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
  · intro c
    obtain ⟨τ, ht, hs⟩ := c.property
    obtain ⟨d, hd⟩ := sumRooting_data_exists ht.1
    have hsign : sign b (H.type d) = -1 := by
      apply (H.graph_negative_iff b d).mp
      exact hd ▸ c.property
    exact ⟨⟨d, hsign⟩, Subtype.ext hd.symm⟩

noncomputable def positiveEquiv (b : Block) :
    H.PositiveData b ≃ PositiveVertex H.graph (sumRooting D) b :=
  Equiv.ofBijective (H.positiveInr b) (H.positiveInr_bijective b)

noncomputable def negativeEquiv (b : Block) :
    H.NegativeData b ≃ NegativeVertex H.graph (sumRooting D) b :=
  Equiv.ofBijective (H.negativeInr b) (H.negativeInr_bijective b)

theorem graph_cross_iff (r : Layer) (c : H.PositiveData r.1) (l : H.NegativeData r.1) :
    CrossAt H.graph (sumRooting D) r (Sum.inr c.val) (Sum.inr l.val) ↔
      H.center r.1 l.val = some c.val := by
  constructor
  · rintro ⟨_, _, he⟩
    have hp := (H.dataPair_layerRoot r c.val l.val).mp ((H.graph_link _ _ _).mp he)
    have hs : sign r.1 (H.type c.val) = -sign r.1 (H.type l.val) := by
      rw [c.property, l.property]
      norm_num
    rcases H.layerPair_opposite hp hs with hl | hc
    · exact hl
    · have hc' := (H.center_signs hc).2
      have hc'' := c.property
      omega
  · intro he
    exact ⟨(H.positiveInr r.1 c).property, (H.negativeInr r.1 l).property,
      (H.graph_link _ _ _).mpr ((H.dataPair_layerRoot r c.val l.val).mpr (H.center_layerPair he))⟩

theorem leafCenter_some_iff_center (h : RootedLegal H.graph (sumRooting D))
    (r : Layer) (l : H.NegativeData r.1) (c : H.PositiveData r.1) :
    leafCenter (G := H.graph) (μ := sumRooting D) r (H.negativeInr r.1 l) =
      some (H.positiveInr r.1 c) ↔ H.center r.1 l.val = some c.val := by
  rw [leafCenter_some_iff h]
  exact H.graph_cross_iff r c l

theorem leafCenter_none_iff_center (h : RootedLegal H.graph (sumRooting D))
    (r : Layer) (l : H.NegativeData r.1) :
    leafCenter (G := H.graph) (μ := sumRooting D) r (H.negativeInr r.1 l) = none ↔
      H.center r.1 l.val = none := by
  constructor
  · intro hn
    cases hc : H.center r.1 l.val with
    | none => rfl
    | some c =>
      let c' : H.PositiveData r.1 := ⟨c, (H.center_signs hc).1⟩
      have he := (H.leafCenter_some_iff_center h r l c').mpr hc
      rw [hn] at he
      cases he
  · intro hn
    cases he : leafCenter (G := H.graph) (μ := sumRooting D) r (H.negativeInr r.1 l) with
    | none => rfl
    | some c =>
      obtain ⟨c', rfl⟩ := (H.positiveInr_bijective r.1).2 c
      have hc := (H.leafCenter_some_iff_center h r l c').mp he
      rw [hn] at hc
      cases hc

theorem sum_positive_subtype (b : Block) (f : D → ℝ) :
    (∑ d : H.PositiveData b, f d.val) = ∑ d : D, if sign b (H.type d) = 1 then f d else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun d => sign b (H.type d) = 1))
    (by intro d; simp) f, Finset.sum_filter]

theorem sum_negative_subtype (b : Block) (f : D → ℝ) :
    (∑ d : H.NegativeData b, f d.val) = ∑ d : D, if sign b (H.type d) = -1 then f d else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun d => sign b (H.type d) = -1))
    (by intro d; simp) f, Finset.sum_filter]

theorem leaf_fiberMass_eq (h : RootedLegal H.graph (sumRooting D))
    (r : Layer) (w : D → ℝ) (c : H.PositiveData r.1) :
    StarEnergy.fiberMass (leafCenter (G := H.graph) (μ := sumRooting D) r)
      (fun l => Sum.elim (fun _ : Root => (0 : ℝ)) w l.val) (H.positiveInr r.1 c) =
      ∑ l : D, if H.center r.1 l = some c.val then w l else 0 := by
  classical
  have he : StarEnergy.fiberMass (leafCenter (G := H.graph) (μ := sumRooting D) r)
      (fun l => Sum.elim (fun _ : Root => (0 : ℝ)) w l.val) (H.positiveInr r.1 c) =
      ∑ l : H.NegativeData r.1, if H.center r.1 l.val = some c.val then w l.val else 0 := by
    symm
    apply Fintype.sum_equiv (H.negativeEquiv r.1)
    intro l
    change (if H.center r.1 l.val = some c.val then w l.val else 0) =
      if leafCenter r (H.negativeInr r.1 l) = some (H.positiveInr r.1 c) then w l.val else 0
    simp only [H.leafCenter_some_iff_center h r l c]
  rw [he, H.sum_negative_subtype r.1
    (fun l => if H.center r.1 l = some c.val then w l else 0)]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hc : H.center r.1 l = some c.val
  · simp [hc, (H.center_signs hc).2]
  · simp [hc]

noncomputable def layerEnergy (b : Block) (w : D → ℝ) : ℝ := by
  classical
  exact (∑ d : D, if sign b (H.type d) = 1 then
    (w d - ∑ l : D, if H.center b l = some d then w l else 0) ^ 2 else 0) +
    ∑ l : D, if sign b (H.type l) = -1 ∧ H.center b l = none then w l ^ 2 else 0

theorem actualLayerEnergy_eq_layerEnergy (h : RootedLegal H.graph (sumRooting D))
    (r : Layer) (w : D → ℝ) :
    actualLayerEnergy (G := H.graph) (μ := sumRooting D) r
      (Sum.elim (fun _ : Root => 0) w) = H.layerEnergy r.1 w := by
  classical
  unfold actualLayerEnergy StarEnergy.energy layerEnergy
  congr 1
  · have he : (∑ c : PositiveVertex H.graph (sumRooting D) r.1,
        (Sum.elim (fun _ : Root => (0 : ℝ)) w c.val -
          StarEnergy.fiberMass (leafCenter r)
            (fun l => Sum.elim (fun _ : Root => (0 : ℝ)) w l.val) c) ^ 2) =
        ∑ c : H.PositiveData r.1,
          (w c.val - ∑ l : D, if H.center r.1 l = some c.val then w l else 0) ^ 2 := by
      symm
      apply Fintype.sum_equiv (H.positiveEquiv r.1)
      intro c
      change (w c.val - _) ^ 2 =
        (w c.val - StarEnergy.fiberMass (leafCenter r)
          (fun l => Sum.elim (fun _ : Root => (0 : ℝ)) w l.val) (H.positiveInr r.1 c)) ^ 2
      rw [H.leaf_fiberMass_eq h]
    rw [he, H.sum_positive_subtype r.1
      (fun c => (w c - ∑ l : D, if H.center r.1 l = some c then w l else 0) ^ 2)]
  · have he : (∑ l : NegativeVertex H.graph (sumRooting D) r.1,
        if leafCenter r l = none then (Sum.elim (fun _ : Root => (0 : ℝ)) w l.val) ^ 2 else 0) =
        ∑ l : H.NegativeData r.1,
          if H.center r.1 l.val = none then w l.val ^ 2 else 0 := by
      symm
      apply Fintype.sum_equiv (H.negativeEquiv r.1)
      intro l
      change (if H.center r.1 l.val = none then w l.val ^ 2 else 0) =
        if leafCenter r (H.negativeInr r.1 l) = none then w l.val ^ 2 else 0
      simp only [H.leafCenter_none_iff_center h r l]
    rw [he, H.sum_negative_subtype r.1
      (fun l => if H.center r.1 l = none then w l ^ 2 else 0)]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hs : sign r.1 (H.type l) = -1 <;>
      by_cases hn : H.center r.1 l = none <;> simp [hs, hn]

end TranscendentalTuran.Green.Realization.TypedData
