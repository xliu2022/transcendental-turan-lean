module

public import TranscendentalTuran.Network.PartialIso
public import TranscendentalTuran.Network.Conductance

@[expose] public section

/-!
# Four grounded partial bijections in series

Formalization author and responsible maintainer: Xizhi Liu.

Missing intermediate incidences are already represented by the defect of a
partial bijection; the endpoint inequality therefore includes every stub.
-/

namespace TranscendentalTuran.Network.PartialIso

open scoped BigOperators

variable {A B C D E : Type*}

theorem compose_defect_resistance [Fintype A] [Fintype B] [Fintype C]
    (f : PartialIso A B) (g : PartialIso B C) (x : A → ℝ) (y : B → ℝ) (z : C → ℝ)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (1 / (r + s)) * (f.comp g).defect x z ≤
      (1 / r) * f.defect x y + (1 / s) * g.defect y z := by
  have h := compose_defect f g x y z (one_div_pos.mpr hr) (one_div_pos.mpr hs)
  have he : (1 / r * (1 / s)) / (1 / r + 1 / s) = 1 / (r + s) := by
    field_simp
    ring
  rwa [he] at h

theorem four_defect_resistance [Fintype A] [Fintype B] [Fintype C]
    [Fintype D] [Fintype E]
    (f : PartialIso A B) (g : PartialIso B C) (h : PartialIso C D) (k : PartialIso D E)
    (x : A → ℝ) (y : B → ℝ) (z : C → ℝ) (t : D → ℝ) (v : E → ℝ)
    {r s u v' : ℝ} (hr : 0 < r) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v') :
    (1 / (r + s + u + v')) * (((f.comp g).comp h).comp k).defect x v ≤
      (1 / r) * f.defect x y + (1 / s) * g.defect y z +
        (1 / u) * h.defect z t + (1 / v') * k.defect t v := by
  have h₀ := compose_defect_resistance f g x y z hr hs
  have h₁ := compose_defect_resistance (f.comp g) h x z t (add_pos hr hs) hu
  have h₂ := compose_defect_resistance ((f.comp g).comp h) k x t v
    (add_pos (add_pos hr hs) hu) hv
  linarith

theorem four_defect [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    (f : PartialIso A B) (g : PartialIso B C) (h : PartialIso C D) (k : PartialIso D E)
    (x : A → ℝ) (y : B → ℝ) (z : C → ℝ) (t : D → ℝ) (v : E → ℝ)
    (W : Fin 4 → ℝ) (hW : ∀ i, 0 < W i) :
    conductance W * (((f.comp g).comp h).comp k).defect x v ≤
      W 0 * f.defect x y + W 1 * g.defect y z +
        W 2 * h.defect z t + W 3 * k.defect t v := by
  have hh := four_defect_resistance f g h k x y z t v
    (one_div_pos.mpr (hW 0)) (one_div_pos.mpr (hW 1))
    (one_div_pos.mpr (hW 2)) (one_div_pos.mpr (hW 3))
  simpa only [conductance, resistance, Fin.sum_univ_four, one_div_one_div] using hh

end TranscendentalTuran.Network.PartialIso
