module

public import TranscendentalTuran.Network.StageEnergy
public import TranscendentalTuran.Network.BaseEnergy
public import TranscendentalTuran.Network.MarkedSourceGain

@[expose] public section

/-!
# Series reduction of the actual rooted host

Formalization author and responsible maintainer: Xizhi Liu.

The four block unions partition into E and D paths. Each path is a composite
of four actual partial bijections, so the grounded series inequality applies
to complete chains, broken chains, and isolated ports simultaneously.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network Parameters
open scoped BigOperators
attribute [local irreducible] Parameters.q Parameters.N
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

theorem east_series_energy (h : RootedLegal G μ) (w : V → ℝ)
    (W : Fin 4 → ℝ) (hW : ∀ b, 0 < W b) :
    conductance W * (eastIso h).defect (fun x => w x.val) (fun x => w x.val) ≤
      W 0 * (stageE0 h).defect (fun x => w x.val) (fun p => w p.val.val) +
      W 1 * (stageE1 h).defect (fun c => w c.val) (fun p => w p.val.val) +
      W 3 * (stageE2 h).defect (fun c => w c.val) (fun p => w p.val.val) +
      W 2 * (stageE3 h).defect (fun x => w x.val) (fun p => w p.val.val) := by
  have hh := PartialIso.four_defect_resistance
    (stageE0 h) (stageE1 h).symm (stageE2 h) (stageE3 h).symm
    (fun x => w x.val) (fun p => w p.val.val) (fun c => w c.val)
    (fun p => w p.val.val) (fun x => w x.val)
    (one_div_pos.mpr (hW 0)) (one_div_pos.mpr (hW 1))
    (one_div_pos.mpr (hW 3)) (one_div_pos.mpr (hW 2))
  have hc : 1 / (1 / W 0 + 1 / W 1 + 1 / W 3 + 1 / W 2) = conductance W := by
    unfold conductance resistance
    rw [Fin.sum_univ_four]
    congr 1
    ring
  rw [hc] at hh
  simpa only [eastIso, one_div_one_div, PartialIso.defect_symm] using hh

theorem diagonal_series_energy (h : RootedLegal G μ) (w : V → ℝ)
    (W : Fin 4 → ℝ) (hW : ∀ b, 0 < W b) :
    conductance W * (diagonalIso h).defect (fun x => w x.val) (fun x => w x.val) ≤
      W 1 * (stageD0 h).defect (fun x => w x.val) (fun p => w p.val.val) +
      W 0 * (stageD1 h).defect (fun c => w c.val) (fun p => w p.val.val) +
      W 2 * (stageD2 h).defect (fun c => w c.val) (fun p => w p.val.val) +
      W 3 * (stageD3 h).defect (fun x => w x.val) (fun p => w p.val.val) := by
  have hh := PartialIso.four_defect_resistance
    (stageD0 h) (stageD1 h).symm (stageD2 h) (stageD3 h).symm
    (fun x => w x.val) (fun p => w p.val.val) (fun c => w c.val)
    (fun p => w p.val.val) (fun x => w x.val)
    (one_div_pos.mpr (hW 1)) (one_div_pos.mpr (hW 0))
    (one_div_pos.mpr (hW 2)) (one_div_pos.mpr (hW 3))
  have hc : 1 / (1 / W 1 + 1 / W 0 + 1 / W 2 + 1 / W 3) = conductance W := by
    unfold conductance resistance
    rw [Fin.sum_univ_four]
    congr 1
    ring
  rw [hc] at hh
  simpa only [diagonalIso, one_div_one_div, PartialIso.defect_symm] using hh

theorem union_matching_energy_reduction (h : RootedLegal G μ) (w : V → ℝ)
    (W : Fin 4 → ℝ) (hW : ∀ b, 0 < W b) :
    conductance W * (baseNetwork h).energy (fun x => w x.val) ≤
      ∑ b : Fin 4, W b * unionMatchingEnergy (G := G) (μ := μ) b w := by
  have hE := east_series_energy h w W hW
  have hD := diagonal_series_energy h w W hW
  rw [baseNetwork_energy_eq_defects, Fin.sum_univ_four,
    block0_stage_energy h, block1_stage_energy h, block2_stage_energy h, block3_stage_energy h]
  nlinarith only [hE, hD]

theorem matching_energy_reduction (h : RootedLegal G μ) (z : Root → ℝ) (w : V → ℝ)
    (hz : ∀ r, 0 ≤ z r) (hw : ∀ x, 0 ≤ w x)
    (hW : ∀ b, 0 < matchingBlockWeight z b) :
    conductance (matchingBlockWeight z) * (baseNetwork h).energy (fun x => w x.val) ≤
      matchingEnergy (G := G) (μ := μ) z w :=
  (union_matching_energy_reduction h w (matchingBlockWeight z) hW).trans
    (completing_blocks_decreases_energy h z w hz hw)

end TranscendentalTuran.Source
