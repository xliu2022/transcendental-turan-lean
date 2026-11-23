module

public import TranscendentalTuran.Network.PortRoles

@[expose] public section

/-!
# Actual four-stage path maps

Formalization author and responsible maintainer: Xizhi Liu.

All eight stage maps are extracted from matching incidences in the ordinary
host. Their two fourfold composites are exactly the inferred E and D moves.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network
attribute [local irreducible] Parameters.q Parameters.N
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

noncomputable def matchingIso {A B : Type*} (h : RootedLegal G μ) (b : Fin 4)
    (av : A → V) (bv : B → V) (ha : Function.Injective av) (hb : Function.Injective bv) :
    PartialIso A B :=
  PartialIso.ofRel (fun a p => MatchingEdge G μ b (av a) (bv p))
    (fun a p q hp hq => hb (h.matching_left b (av a) (bv p) (bv q) hp hq))
    (fun a c p ha' hc => ha (h.matching_right b (av a) (av c) (bv p) ha' hc))

theorem matchingIso_forward {A B : Type*} (h : RootedLegal G μ) (b : Fin 4)
    (av : A → V) (bv : B → V) (ha hb) (a : A) (p : B) :
    (matchingIso h b av bv ha hb).forward a = some p ↔ MatchingEdge G μ b (av a) (bv p) :=
  PartialIso.ofRel_forward _ _ _ _ _

noncomputable def stageE0 (h : RootedLegal G μ) : PartialIso (BaseVertex G μ) (EPort01 G μ) :=
  matchingIso h 0 Subtype.val (fun p => p.val.val)
    Subtype.val_injective (Subtype.val_injective.comp Subtype.val_injective)
noncomputable def stageE1 (h : RootedLegal G μ) :
    PartialIso (TypedVertex G μ .center13) (EPort01 G μ) :=
  matchingIso h 1 Subtype.val (fun p => p.val.val)
    Subtype.val_injective (Subtype.val_injective.comp Subtype.val_injective)
noncomputable def stageE2 (h : RootedLegal G μ) :
    PartialIso (TypedVertex G μ .center13) (EPort23 G μ) :=
  matchingIso h 3 Subtype.val (fun p => p.val.val)
    Subtype.val_injective (Subtype.val_injective.comp Subtype.val_injective)
noncomputable def stageE3 (h : RootedLegal G μ) : PartialIso (BaseVertex G μ) (EPort23 G μ) :=
  matchingIso h 2 Subtype.val (fun p => p.val.val)
    Subtype.val_injective (Subtype.val_injective.comp Subtype.val_injective)

noncomputable def stageD0 (h : RootedLegal G μ) : PartialIso (BaseVertex G μ) (DPort01 G μ) :=
  matchingIso h 1 Subtype.val (fun p => p.val.val)
    Subtype.val_injective (Subtype.val_injective.comp Subtype.val_injective)
noncomputable def stageD1 (h : RootedLegal G μ) :
    PartialIso (TypedVertex G μ .center02) (DPort01 G μ) :=
  matchingIso h 0 Subtype.val (fun p => p.val.val)
    Subtype.val_injective (Subtype.val_injective.comp Subtype.val_injective)
noncomputable def stageD2 (h : RootedLegal G μ) :
    PartialIso (TypedVertex G μ .center02) (DPort23 G μ) :=
  matchingIso h 2 Subtype.val (fun p => p.val.val)
    Subtype.val_injective (Subtype.val_injective.comp Subtype.val_injective)
noncomputable def stageD3 (h : RootedLegal G μ) : PartialIso (BaseVertex G μ) (DPort23 G μ) :=
  matchingIso h 3 Subtype.val (fun p => p.val.val)
    Subtype.val_injective (Subtype.val_injective.comp Subtype.val_injective)

noncomputable def eastIso (h : RootedLegal G μ) : PartialIso (BaseVertex G μ) (BaseVertex G μ) :=
  (((stageE0 h).comp (stageE1 h).symm).comp (stageE2 h)).comp (stageE3 h).symm

noncomputable def diagonalIso (h : RootedLegal G μ) : PartialIso (BaseVertex G μ) (BaseVertex G μ) :=
  (((stageD0 h).comp (stageD1 h).symm).comp (stageD2 h)).comp (stageD3 h).symm

theorem eastIso_forward (h : RootedLegal G μ) (x y : BaseVertex G μ) :
    (eastIso h).forward x = some y ↔ CompleteE G μ x.val y.val := by
  simp only [eastIso, PartialIso.comp_forward_iff, PartialIso.symm_forward_iff,
    stageE0, stageE1, stageE2, stageE3, matchingIso_forward]
  constructor
  · rintro ⟨t, ⟨c, ⟨p, h₀, h₁⟩, h₂⟩, h₃⟩
    exact ⟨x.property, y.property, p.val.val, c.val, t.val.val,
      p.val.property, c.property, t.val.property, h₀, h₁, h₂, h₃⟩
  · rintro ⟨_, _, p, c, t, hp, hc, ht, h₀, h₁, h₂, h₃⟩
    let pe : EPort01 G μ := ⟨⟨p, hp⟩, port01E_of_base x.property h₀⟩
    let te : EPort23 G μ := ⟨⟨t, ht⟩, port23E_of_base y.property h₃⟩
    exact ⟨te, ⟨⟨c, hc⟩, ⟨pe, h₀, h₁⟩, h₂⟩, h₃⟩

theorem diagonalIso_forward (h : RootedLegal G μ) (x y : BaseVertex G μ) :
    (diagonalIso h).forward x = some y ↔ CompleteD G μ x.val y.val := by
  simp only [diagonalIso, PartialIso.comp_forward_iff, PartialIso.symm_forward_iff,
    stageD0, stageD1, stageD2, stageD3, matchingIso_forward]
  constructor
  · rintro ⟨t, ⟨c, ⟨p, h₀, h₁⟩, h₂⟩, h₃⟩
    exact ⟨x.property, y.property, p.val.val, c.val, t.val.val,
      p.val.property, c.property, t.val.property, h₀, h₁, h₂, h₃⟩
  · rintro ⟨_, _, p, c, t, hp, hc, ht, h₀, h₁, h₂, h₃⟩
    let pe : DPort01 G μ := ⟨⟨p, hp⟩, not_port01E_of_base h x.property h₀⟩
    let te : DPort23 G μ := ⟨⟨t, ht⟩, not_port23E_of_base h y.property h₃⟩
    exact ⟨te, ⟨⟨c, hc⟩, ⟨pe, h₀, h₁⟩, h₂⟩, h₃⟩

end TranscendentalTuran.Source
