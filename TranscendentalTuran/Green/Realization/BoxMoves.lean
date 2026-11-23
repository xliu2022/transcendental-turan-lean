/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.BoxStructure

@[expose] public section

noncomputable section

namespace TranscendentalTuran.Green.Realization

open Network Encoding FiniteNetwork

/-- Every complete horizontal chain is one of the literal private chains. -/
theorem completeE_data {n : ℕ} {x y : Vertex n} (h : (boxData n).CompleteE x y) :
    ∃ v w : Box n, x = base v ∧ y = base w ∧ eStart n v = eEnd n w := by
  obtain ⟨v, rfl⟩ := vertex_of_type h.1
  obtain ⟨w, rfl⟩ := vertex_of_type h.2.1
  obtain ⟨p, c, q, _, _, _, h0, h1, h3, h2⟩ := h.2.2
  have hp := matching_to_mate n 0 (base v) p h0
  change some (port01E (eStart n v)) = some p at hp
  have hpe := (Option.some.inj hp).symm
  subst p
  change some (center13 (eStart n v)) = some c at h1
  have hce := (Option.some.inj h1).symm
  subst c
  have hq := matching_to_mate n 3 (center13 (eStart n v)) q h3
  change some (port23E (eStart n v)) = some q at hq
  have hqe := (Option.some.inj hq).symm
  subst q
  have he := (center_m2_p23E (eStart n v) w).mp h2
  exact ⟨v, w, rfl, rfl, he.symm⟩

/-- Every complete diagonal chain is one of the literal private chains. -/
theorem completeD_data {n : ℕ} {x y : Vertex n} (h : (boxData n).CompleteD x y) :
    ∃ v w : Box n, x = base v ∧ y = base w ∧ dStart n v = dEnd n w := by
  obtain ⟨v, rfl⟩ := vertex_of_type h.1
  obtain ⟨w, rfl⟩ := vertex_of_type h.2.1
  obtain ⟨p, c, q, _, _, _, h1, h0, h2, h3⟩ := h.2.2
  have hp := matching_to_mate n 1 (base v) p h1
  change some (port01D (dStart n v)) = some p at hp
  have hpe := (Option.some.inj hp).symm
  subst p
  change some (center02 (dStart n v)) = some c at h0
  have hce := (Option.some.inj h0).symm
  subst c
  have hq := matching_to_mate n 2 (center02 (dStart n v)) q h2
  change some (port23D (dStart n v)) = some q at hq
  have hqe := (Option.some.inj hq).symm
  subst q
  have he := (center_m3_p23D (dStart n v) w).mp h3
  exact ⟨v, w, rfl, rfl, he.symm⟩

theorem complete_first_coordinates {n : ℕ} {x y : Vertex n}
    (h : (boxData n).CompleteE x y ∨ (boxData n).CompleteD x y) :
    ∃ v w : Box n, x = base v ∧ y = base w ∧ w.1.val = v.1.val + 1 := by
  rcases h with h | h
  · obtain ⟨v, w, rfl, rfl, he⟩ := completeE_data h
    exact ⟨v, w, rfl, rfl, (e_endpoint_coordinates he).1⟩
  · obtain ⟨v, w, rfl, rfl, he⟩ := completeD_data h
    exact ⟨v, w, rfl, rfl, (d_endpoint_coordinates he).1⟩

theorem ownerH_data {n : ℕ} {x o : Vertex n} (h : (boxData n).Owner 0 x o) :
    ∃ v : Box n, x = base v ∧ o = ownerH v.1 := by
  change center n .ownerH x = some o at h
  rcases x with ⟨τ, v⟩
  cases τ
  · exact ⟨v, rfl, (Option.some.inj h).symm⟩
  all_goals cases h

theorem ownerV_data {n : ℕ} {x o : Vertex n} (h : (boxData n).Owner 1 x o) :
    ∃ v : Box n, x = base v ∧ o = ownerV v.2 := by
  change center n .ownerV x = some o at h
  rcases x with ⟨τ, v⟩
  cases τ
  · exact ⟨v, rfl, (Option.some.inj h).symm⟩
  all_goals cases h

@[simp] theorem ownerH_base {n : ℕ} (v : Box n) (o : Vertex n) :
    (boxData n).Owner 0 (base v) o ↔ ownerH v.1 = o := by
  change some (ownerH v.1) = some o ↔ _
  simp

@[simp] theorem ownerV_base {n : ℕ} (v : Box n) (o : Vertex n) :
    (boxData n).Owner 1 (base v) o ↔ ownerV v.2 = o := by
  change some (ownerV v.2) = some o ↔ _
  simp

@[simp] theorem ownerH_inj {n : ℕ} (i j : Fin (n + 1)) : ownerH i = ownerH j ↔ i = j :=
  vertex_mk_inj (n := n) (τ := .ownerH) i j

@[simp] theorem ownerV_inj {n : ℕ} (i j : Fin (n + 1)) : ownerV i = ownerV j ↔ i = j :=
  vertex_mk_inj (n := n) (τ := .ownerV) i j

theorem box_E_preserves_vertical {n : ℕ} {x y a b : Vertex n}
    (h : (boxData n).CompleteE x y) (ha : (boxData n).Owner 1 x a)
    (hb : (boxData n).Owner 1 y b) : a = b := by
  obtain ⟨v, w, rfl, rfl, he⟩ := completeE_data h
  have hva := (ownerV_base v a).mp ha
  have hwb := (ownerV_base w b).mp hb
  rw [← hva, ← hwb, (e_endpoint_coordinates he).2]

theorem parentH_data {n : ℕ} {a b : Vertex n} (h : (boxData n).ParentH a b) :
    ∃ i j : Fin (n + 1), a = ownerH i ∧ b = ownerH j ∧ j.val = i.val + 1 := by
  obtain ⟨x, y, hm, ha, hb⟩ := h
  obtain ⟨v, w, rfl, rfl, he⟩ := complete_first_coordinates hm
  exact ⟨v.1, w.1, ((ownerH_base v a).mp ha).symm,
    ((ownerH_base w b).mp hb).symm, he⟩

theorem parentV_data {n : ℕ} {a b : Vertex n} (h : (boxData n).ParentV a b) :
    ∃ i j : Fin (n + 1), a = ownerV i ∧ b = ownerV j ∧ j.val = i.val + 1 := by
  obtain ⟨x, y, hm, ha, hb⟩ := h
  obtain ⟨v, w, rfl, rfl, he⟩ := completeD_data hm
  exact ⟨w.2, v.2, ((ownerV_base w a).mp ha).symm,
    ((ownerV_base v b).mp hb).symm, (d_endpoint_coordinates he).2⟩

theorem box_parentH_unique {n : ℕ} {a b c : Vertex n}
    (ha : (boxData n).ParentH a c) (hb : (boxData n).ParentH b c) : a = b := by
  obtain ⟨i, j, rfl, hc, hi⟩ := parentH_data ha
  obtain ⟨k, l, rfl, hc', hk⟩ := parentH_data hb
  have hj : j = l := (ownerH_inj j l).mp (hc.symm.trans hc')
  have hik : i = k := by apply Fin.ext; have hv := congrArg Fin.val hj; omega
  exact congrArg ownerH hik

theorem box_parentV_unique {n : ℕ} {a b c : Vertex n}
    (ha : (boxData n).ParentV a c) (hb : (boxData n).ParentV b c) : a = b := by
  obtain ⟨i, j, rfl, hc, hi⟩ := parentV_data ha
  obtain ⟨k, l, rfl, hc', hk⟩ := parentV_data hb
  have hj : j = l := (ownerV_inj j l).mp (hc.symm.trans hc')
  have hik : i = k := by apply Fin.ext; have hv := congrArg Fin.val hj; omega
  exact congrArg ownerV hik

theorem box_boundaryH {n : ℕ} {x y o : Vertex n}
    (hm : (boxData n).Owner 0 (boxData n).mark o) (hx : (boxData n).Owner 0 x o) :
    ¬ ((boxData n).CompleteE y x ∨ (boxData n).CompleteD y x) := by
  intro h
  obtain ⟨v, w, rfl, rfl, he⟩ := complete_first_coordinates h
  have h0 : ownerH (0 : Fin (n + 1)) = o := (ownerH_base (boxRoot n) o).mp hm
  have hw := (ownerH_base w o).mp hx
  have hi : w.1 = 0 := (ownerH_inj w.1 0).mp (hw.trans h0.symm)
  have hv := congrArg Fin.val hi
  simp only [Fin.val_zero] at hv
  omega

theorem box_boundaryV {n : ℕ} {x y o : Vertex n}
    (hm : (boxData n).Owner 1 (boxData n).mark o) (hx : (boxData n).Owner 1 x o) :
    ¬ (boxData n).CompleteD x y := by
  intro h
  obtain ⟨v, w, rfl, rfl, he⟩ := completeD_data h
  have h0 : ownerV (0 : Fin (n + 1)) = o := (ownerV_base (boxRoot n) o).mp hm
  have hv := (ownerV_base v o).mp hx
  have hi : v.2 = 0 := (ownerV_inj v.2 0).mp (hv.trans h0.symm)
  have hz := congrArg Fin.val hi
  have hd := (d_endpoint_coordinates he).2
  simp only [Fin.val_zero] at hz
  omega

/-- The literal subdivided finite box obeys every typed structural rule. -/
theorem boxData_legal (n : ℕ) : (boxData n).Legal where
  matching_left := box_matching_left n
  port_base_unique := box_port_base_unique n
  port_center_unique := box_port_center_unique n
  E_preserves_vertical _ _ _ _ := box_E_preserves_vertical
  parentH_unique _ _ _ := box_parentH_unique
  parentV_unique _ _ _ := box_parentV_unique
  boundaryH _ _ _ := box_boundaryH
  boundaryV _ _ _ := box_boundaryV

end TranscendentalTuran.Green.Realization
