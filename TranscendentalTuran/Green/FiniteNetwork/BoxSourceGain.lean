/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.FiniteNetwork.SourceGain
public import TranscendentalTuran.Green.FiniteNetwork.BoxApproximation

@[expose] public section

noncomputable section

open scoped BigOperators Topology
open Filter

namespace TranscendentalTuran.Green.FiniteNetwork

/-- Source gain of the actual scaled finite-box Green vector. -/
def boxSourceGain (J R : ℝ) (N : ℕ) : ℝ :=
  J * ((J * R) * (boxNetwork N).green (boxRoot N) (boxRoot N)) -
    ((1 / R) * (boxNetwork N).energy
      (fun v => (J * R) * (boxNetwork N).green (boxRoot N) v)) / 2

theorem boxSourceGain_eq (J R : ℝ) (hR : R ≠ 0) (N : ℕ) :
    boxSourceGain J R N = (J ^ 2 * R / 2) * boxGreenValue N :=
  (boxNetwork N).scaled_green_gain (boxProjection N) J R hR

/-- Matching lower source gains are approached by genuine finite boxes, while their
base mass remains bounded by `JR/2`. -/
theorem tendsto_boxSourceGain (J R : ℝ) (hR : R ≠ 0) :
    Tendsto (boxSourceGain J R) atTop (𝓝 ((J ^ 2 * R / 2) * cornerGreen)) := by
  have hc : Tendsto (fun _ : ℕ => J ^ 2 * R / 2) atTop (𝓝 (J ^ 2 * R / 2)) :=
    tendsto_const_nhds
  have h := hc.mul tendsto_boxGreenValue
  exact Filter.Tendsto.congr (fun N => (boxSourceGain_eq J R hR N).symm) h

end TranscendentalTuran.Green.FiniteNetwork
