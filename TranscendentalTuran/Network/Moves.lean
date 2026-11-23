module

public import TranscendentalTuran.Encoding.LocalRules

@[expose] public section

/-!
# Deterministic four-edge moves in the actual rooted host

Formalization author and responsible maintainer: Xizhi Liu.

The arguments use the four actual matching-block relations. No deterministic
move or walk-lifting assumption is added to the source class.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

theorem completeE_right_unique (h : RootedLegal G μ) {x y z : V}
    (hy : CompleteE G μ x y) (hz : CompleteE G μ x z) : y = z := by
  obtain ⟨_, _, p, c, t, _, _, _, hxp, hcp, hct, hyt⟩ := hy
  obtain ⟨_, _, p', c', t', _, _, _, hxp', hcp', hct', hzt'⟩ := hz
  have hp := h.matching_left 0 x p p' hxp hxp'
  subst p'
  have hc := h.matching_right 1 c c' p hcp hcp'
  subst c'
  have ht := h.matching_left 3 c t t' hct hct'
  subst t'
  exact h.matching_right 2 y z t hyt hzt'

theorem completeE_left_unique (h : RootedLegal G μ) {x y z : V}
    (hx : CompleteE G μ x z) (hy : CompleteE G μ y z) : x = y := by
  obtain ⟨_, _, p, c, t, _, _, _, hxp, hcp, hct, hzt⟩ := hx
  obtain ⟨_, _, p', c', t', _, _, _, hyp', hcp', hct', hzt'⟩ := hy
  have ht := h.matching_left 2 z t t' hzt hzt'
  subst t'
  have hc := h.matching_right 3 c c' t hct hct'
  subst c'
  have hp := h.matching_left 1 c p p' hcp hcp'
  subst p'
  exact h.matching_right 0 x y p hxp hyp'

theorem completeD_right_unique (h : RootedLegal G μ) {x y z : V}
    (hy : CompleteD G μ x y) (hz : CompleteD G μ x z) : y = z := by
  obtain ⟨_, _, p, c, t, _, _, _, hxp, hcp, hct, hyt⟩ := hy
  obtain ⟨_, _, p', c', t', _, _, _, hxp', hcp', hct', hzt'⟩ := hz
  have hp := h.matching_left 1 x p p' hxp hxp'
  subst p'
  have hc := h.matching_right 0 c c' p hcp hcp'
  subst c'
  have ht := h.matching_left 2 c t t' hct hct'
  subst t'
  exact h.matching_right 3 y z t hyt hzt'

theorem completeD_left_unique (h : RootedLegal G μ) {x y z : V}
    (hx : CompleteD G μ x z) (hy : CompleteD G μ y z) : x = y := by
  obtain ⟨_, _, p, c, t, _, _, _, hxp, hcp, hct, hzt⟩ := hx
  obtain ⟨_, _, p', c', t', _, _, _, hyp', hcp', hct', hzt'⟩ := hy
  have ht := h.matching_left 3 z t t' hzt hzt'
  subst t'
  have hc := h.matching_right 2 c c' t hct hct'
  subst c'
  have hp := h.matching_left 0 c p p' hcp hcp'
  subst p'
  exact h.matching_right 1 x y p hxp hyp'

/-- Directions agree with the Green-kernel interface: E, W, U, D. -/
def LogicalMove (G : RGraph V 3) (μ : Rooting Root V) : Fin 4 → V → V → Prop
  | 0 => CompleteE G μ
  | 1 => fun x y => CompleteE G μ y x
  | 2 => fun x y => CompleteD G μ y x
  | 3 => CompleteD G μ

def reversePort : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2

theorem reversePort_involutive : Function.Involutive reversePort := by
  intro d
  fin_cases d <;> rfl

theorem logicalMove_reverse (d : Fin 4) (x y : V) :
    LogicalMove G μ (reversePort d) y x ↔ LogicalMove G μ d x y := by
  fin_cases d <;> rfl

theorem logicalMove_deterministic (h : RootedLegal G μ) (d : Fin 4) {x y z : V}
    (hy : LogicalMove G μ d x y) (hz : LogicalMove G μ d x z) : y = z := by
  fin_cases d
  · exact completeE_right_unique h hy hz
  · exact completeE_left_unique h hy hz
  · exact completeD_left_unique h hy hz
  · exact completeD_right_unique h hy hz

theorem logicalMove_endpoints (d : Fin 4) {x y : V} (he : LogicalMove G μ d x y) :
    Declared G μ .base x ∧ Declared G μ .base y := by
  fin_cases d
  · exact ⟨he.1, he.2.1⟩
  · exact ⟨he.2.1, he.1⟩
  · exact ⟨he.2.1, he.1⟩
  · exact ⟨he.1, he.2.1⟩

end TranscendentalTuran.Source
