module

public import TranscendentalTuran.Network.MatchingPartition

@[expose] public section

/-!
# Every matching square belongs to one path family

Formalization author and responsible maintainer: Xizhi Liu.

This is an exact identity, including isolated ports and interrupted paths.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network
open scoped BigOperators
attribute [local irreducible] Parameters.q Parameters.N
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

theorem block0_stage_energy (h : RootedLegal G μ) (w : V → ℝ) :
    unionMatchingEnergy (G := G) (μ := μ) 0 w =
      (stageE0 h).defect (fun x => w x.val) (fun p => w p.val.val) +
      (stageD1 h).defect (fun c => w c.val) (fun p => w p.val.val) := by
  rw [unionMatchingEnergy_relation h 0]
  rw [← relationEnergy_reindex (matchingPositiveEquiv h 0)
    ((port01Equiv (G := G) (μ := μ)).trans (matchingNegativeEquiv 0))]
  rw [relationEnergy_sum_any]
  · simp only [stageE0, stageD1, matchingIso, PartialIso.ofRel_defect, Sum.elim_inl, Sum.elim_inr]
    rfl
  · intro x p he
    exact p.property (port01E_of_base x.property he)
  · intro c p he
    exact not_port01E_of_center h c.property he p.property

theorem block1_stage_energy (h : RootedLegal G μ) (w : V → ℝ) :
    unionMatchingEnergy (G := G) (μ := μ) 1 w =
      (stageD0 h).defect (fun x => w x.val) (fun p => w p.val.val) +
      (stageE1 h).defect (fun c => w c.val) (fun p => w p.val.val) := by
  rw [unionMatchingEnergy_relation h 1]
  rw [← relationEnergy_reindex (matchingPositiveEquiv h 1)
    (((Equiv.sumComm _ _).trans (port01Equiv (G := G) (μ := μ))).trans (matchingNegativeEquiv 1))]
  rw [relationEnergy_sum_any]
  · simp only [stageD0, stageE1, matchingIso, PartialIso.ofRel_defect, Sum.elim_inl, Sum.elim_inr]
    rfl
  · intro x p he
    exact not_port01E_of_base h x.property he p.property
  · intro c p he
    exact p.property (port01E_of_center c.property he)

theorem block2_stage_energy (h : RootedLegal G μ) (w : V → ℝ) :
    unionMatchingEnergy (G := G) (μ := μ) 2 w =
      (stageE3 h).defect (fun x => w x.val) (fun p => w p.val.val) +
      (stageD2 h).defect (fun c => w c.val) (fun p => w p.val.val) := by
  rw [unionMatchingEnergy_relation h 2]
  rw [← relationEnergy_reindex (matchingPositiveEquiv h 2)
    ((port23Equiv (G := G) (μ := μ)).trans (matchingNegativeEquiv 2))]
  rw [relationEnergy_sum_any]
  · simp only [stageE3, stageD2, matchingIso, PartialIso.ofRel_defect, Sum.elim_inl, Sum.elim_inr]
    rfl
  · intro x p he
    exact p.property (port23E_of_base x.property he)
  · intro c p he
    exact not_port23E_of_center h c.property he p.property

theorem block3_stage_energy (h : RootedLegal G μ) (w : V → ℝ) :
    unionMatchingEnergy (G := G) (μ := μ) 3 w =
      (stageD3 h).defect (fun x => w x.val) (fun p => w p.val.val) +
      (stageE2 h).defect (fun c => w c.val) (fun p => w p.val.val) := by
  rw [unionMatchingEnergy_relation h 3]
  rw [← relationEnergy_reindex (matchingPositiveEquiv h 3)
    (((Equiv.sumComm _ _).trans (port23Equiv (G := G) (μ := μ))).trans (matchingNegativeEquiv 3))]
  rw [relationEnergy_sum_any]
  · simp only [stageD3, stageE2, matchingIso, PartialIso.ofRel_defect, Sum.elim_inl, Sum.elim_inr]
    rfl
  · intro x p he
    exact not_port23E_of_base h x.property he p.property
  · intro c p he
    exact p.property (port23E_of_center c.property he)

end TranscendentalTuran.Source
