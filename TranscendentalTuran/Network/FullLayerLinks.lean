module

public import TranscendentalTuran.Network.LayerLinks

@[expose] public section

/-!
# Equality for a full permitted signed-star link

Formalization author and responsible maintainer: Xizhi Liu.

If every permitted pair is present in the actual ordinary link, the upper
bound becomes an exact identity. No positivity of the weights is needed.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

theorem actualLink_ordered_eq (h : RootedLegal G μ)
    (ht : ∀ x, Data μ x → ∃ τ, Declared G μ τ x)
    (r : Layer) (w : V → ℝ)
    (hfull : ∀ a b : LayerVertex G μ r.1,
      StarEnergy.PermittedPair (leafCenter (G := G) (μ := μ) r) a b →
        Link G μ (layerRoot r) (layerVertexVal r.1 a) (layerVertexVal r.1 b)) :
    (∑ x, ∑ y, if Link G μ (layerRoot r) x y then w x * w y else 0) =
      (∑ c : PositiveVertex G μ r.1, w c.val) ^ 2 +
      (∑ l : NegativeVertex G μ r.1, w l.val) ^ 2 -
        actualLayerEnergy (G := G) (μ := μ) r w := by
  classical
  let e : LayerVertex G μ r.1 → V := layerVertexVal r.1
  let F : V → V → ℝ := fun x y =>
    if Link G μ (layerRoot r) x y then w x * w y else 0
  have he : Function.Injective e := layerVertexVal_injective h r.1
  have hsecond (x : V) : (∑ b, F x (e b)) = ∑ y, F x y := by
    apply Fintype.sum_of_injective e he _ _ _ (fun _ => rfl)
    intro y hy
    have hn : ¬ Link G μ (layerRoot r) x y :=
      fun hl => hy (link_active_endpoints h ht r hl).2
    simp [F, hn]
  have hsum : (∑ a, ∑ b, F (e a) (e b)) = ∑ x, ∑ y, F x y := by
    simp_rw [hsecond]
    apply Fintype.sum_of_injective e he
      (fun a => ∑ y, F (e a) y) (fun x => ∑ y, F x y) _ (fun _ => rfl)
    intro x hx
    apply Finset.sum_eq_zero
    intro y _
    have hn : ¬ Link G μ (layerRoot r) x y :=
      fun hl => hx (link_active_endpoints h ht r hl).1
    simp [F, hn]
  change (∑ x, ∑ y, F x y) = _
  rw [← hsum]
  have hiff (a b : LayerVertex G μ r.1) : Link G μ (layerRoot r) (e a) (e b) ↔
      StarEnergy.PermittedPair (leafCenter (G := G) (μ := μ) r) a b :=
    ⟨link_permitted h r a b, hfull a b⟩
  have heval (a : LayerVertex G μ r.1) : w (e a) =
      Sum.elim (fun c => w c.val) (fun l => w l.val) a := by
    cases a <;> rfl
  simp only [F, hiff]
  simp_rw [heval]
  rw [StarEnergy.permitted_ordered_sum, actualLayer_square_identity]
  ring

theorem actualLink_polynomial_eq (h : RootedLegal G μ)
    (ht : ∀ x, Data μ x → ∃ τ, Declared G μ τ x)
    (r : Layer) (w : V → ℝ)
    (hfull : ∀ a b : LayerVertex G μ r.1,
      StarEnergy.PermittedPair (leafCenter (G := G) (μ := μ) r) a b →
        Link G μ (layerRoot r) (layerVertexVal r.1 a) (layerVertexVal r.1 b)) :
    (dataPairGraph (G := G) (μ := μ) (layerRoot r)).edgePolynomial w =
      ((∑ c : PositiveVertex G μ r.1, w c.val) ^ 2 +
        (∑ l : NegativeVertex G μ r.1, w l.val) ^ 2 -
          actualLayerEnergy (G := G) (μ := μ) r w) / 2 := by
  classical
  have hlink := actualLink_ordered_eq h ht r w hfull
  have hpairs := pairGraph_ordered_sum (dataPairGraph (G := G) (μ := μ) (layerRoot r)) w
  simp only [dataPairGraph_mem_pair] at hpairs
  linarith

end TranscendentalTuran.Source
