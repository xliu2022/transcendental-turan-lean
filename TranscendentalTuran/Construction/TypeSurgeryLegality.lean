module

public import TranscendentalTuran.Construction.TypeSurgeryCore

@[expose] public section

namespace TranscendentalTuran.Source.TypeSurgery

open TuranUniversality TuranUniversality.Weighted Encoding Network RootData

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (G : RGraph (Root ⊕ D) 3) (a : D) (τ : PhysicalType)

theorem matchingRoot_special (b : Fin 4) (j : Fin Parameters.M) :
    (matchingRoot b j).val < Parameters.K := by
  have hb := b.isLt
  have hj := j.isLt
  norm_num [matchingRoot, Parameters.M, Parameters.K] at *
  omega

theorem ownershipRoot_special (b : Fin 2) (j : Fin Parameters.κ) :
    (ownershipRoot b j).val < Parameters.K := by
  have hb := b.isLt
  have hj := j.isLt
  norm_num [ownershipRoot, Parameters.κ, Parameters.M, Parameters.K] at *
  omega

theorem matchingEdge_ne {b : Fin 4} {x y : Root ⊕ D}
    (h : MatchingEdge (graph G a τ) (sumRooting D) b x y) :
    x ≠ Sum.inr a ∧ y ≠ Sum.inr a := by
  obtain ⟨_, _, _, _, _, j, he⟩ := h
  exact special_link_ne G a τ (matchingRoot_special b j) he

theorem ownerEdge_ne {b : Fin 2} {x y : Root ⊕ D}
    (h : OwnerEdge (graph G a τ) (sumRooting D) b x y) :
    x ≠ Sum.inr a ∧ y ≠ Sum.inr a := by
  obtain ⟨_, _, j, he⟩ := h
  exact special_link_ne G a τ (ownershipRoot_special b j) he

theorem matchingEdge_old {b : Fin 4} {x y : Root ⊕ D}
    (h : MatchingEdge (graph G a τ) (sumRooting D) b x y) :
    MatchingEdge G (sumRooting D) b x y := by
  have hn := matchingEdge_ne G a τ h
  obtain ⟨σ, ρ, hx, hy, hi, j, he⟩ := h
  exact ⟨σ, ρ, declared_old_of_ne G a τ hn.1 hx, declared_old_of_ne G a τ hn.2 hy,
    hi, j, link_old G a τ he⟩

theorem ownerEdge_old {b : Fin 2} {x y : Root ⊕ D}
    (h : OwnerEdge (graph G a τ) (sumRooting D) b x y) : OwnerEdge G (sumRooting D) b x y := by
  have hn := ownerEdge_ne G a τ h
  obtain ⟨hx, hy, j, he⟩ := h
  exact ⟨declared_old_of_ne G a τ hn.1 hx, declared_old_of_ne G a τ hn.2 hy,
    j, link_old G a τ he⟩

theorem isCenter_old_of_ne {x : Root ⊕ D} (hx : x ≠ Sum.inr a)
    (h : IsCenter (graph G a τ) (sumRooting D) x) : IsCenter G (sumRooting D) x :=
  h.imp (declared_old_of_ne G a τ hx) (declared_old_of_ne G a τ hx)

theorem completeE_old {x y : Root ⊕ D}
    (h : CompleteE (graph G a τ) (sumRooting D) x y) : CompleteE G (sumRooting D) x y := by
  obtain ⟨hx, hy, p, c, p', hp, hc, hp', h0, h1, h3, h2⟩ := h
  have hn0 := matchingEdge_ne G a τ h0
  have hn1 := matchingEdge_ne G a τ h1
  have hn3 := matchingEdge_ne G a τ h3
  have hn2 := matchingEdge_ne G a τ h2
  exact ⟨declared_old_of_ne G a τ hn0.1 hx, declared_old_of_ne G a τ hn2.1 hy,
    p, c, p', declared_old_of_ne G a τ hn0.2 hp, declared_old_of_ne G a τ hn1.1 hc,
    declared_old_of_ne G a τ hn3.2 hp', matchingEdge_old G a τ h0,
    matchingEdge_old G a τ h1, matchingEdge_old G a τ h3, matchingEdge_old G a τ h2⟩

theorem completeD_old {x y : Root ⊕ D}
    (h : CompleteD (graph G a τ) (sumRooting D) x y) : CompleteD G (sumRooting D) x y := by
  obtain ⟨hx, hy, p, c, p', hp, hc, hp', h1, h0, h2, h3⟩ := h
  have hn1 := matchingEdge_ne G a τ h1
  have hn0 := matchingEdge_ne G a τ h0
  have hn2 := matchingEdge_ne G a τ h2
  have hn3 := matchingEdge_ne G a τ h3
  exact ⟨declared_old_of_ne G a τ hn1.1 hx, declared_old_of_ne G a τ hn3.1 hy,
    p, c, p', declared_old_of_ne G a τ hn1.2 hp, declared_old_of_ne G a τ hn0.1 hc,
    declared_old_of_ne G a τ hn2.2 hp', matchingEdge_old G a τ h1,
    matchingEdge_old G a τ h0, matchingEdge_old G a τ h2, matchingEdge_old G a τ h3⟩

theorem parentH_old {x y : Root ⊕ D}
    (h : ParentH (graph G a τ) (sumRooting D) x y) : ParentH G (sumRooting D) x y := by
  obtain ⟨b, c, hm, hb, hc⟩ := h
  exact ⟨b, c, hm.imp (completeE_old G a τ) (completeD_old G a τ),
    ownerEdge_old G a τ hb, ownerEdge_old G a τ hc⟩

theorem parentV_old {x y : Root ⊕ D}
    (h : ParentV (graph G a τ) (sumRooting D) x y) : ParentV G (sumRooting D) x y := by
  obtain ⟨b, c, hm, hb, hc⟩ := h
  exact ⟨b, c, completeD_old G a τ hm, ownerEdge_old G a τ hb, ownerEdge_old G a τ hc⟩

theorem structuralAt_old {r : Layer} {x y : Root ⊕ D}
    (h : StructuralAt (graph G a τ) (sumRooting D) r x y) : StructuralAt G (sumRooting D) r x y := by
  obtain ⟨σ, ρ, hx, hy, hax, hay, hs, he⟩ := h
  have hn := special_link_ne G a τ (layerRoot_special r) he
  exact ⟨σ, ρ, declared_old_of_ne G a τ hn.1 hx, declared_old_of_ne G a τ hn.2 hy,
    hax, hay, hs, link_old G a τ he⟩

theorem no_equal_type_link_at_new (hu : Undeclared G a) {r : Root} {d : D} {σ : PhysicalType}
    (ha : Declared (graph G a τ) (sumRooting D) σ (Sum.inr a))
    (hd : Declared (graph G a τ) (sumRooting D) σ (Sum.inr d))
    (hl : Link (graph G a τ) (sumRooting D) r (Sum.inr a) (Sum.inr d)) : False := by
  have hσ : σ = τ := by
    rcases (graph_declared G a τ σ a).mp ha with hold | hnew
    · exact False.elim (hu σ hold)
    · exact hnew.2
  subst σ
  have hda : d ≠ a := by
    intro h
    subst d
    exact Source.link_ne hl rfl
  have hdold := declared_old_of_ne G a τ (by
    intro he
    exact hda (Sum.inr.inj he)) hd
  have hk := ((graph_link G a τ r a d).mp hl).2
  have hsecond := hk.resolve_left (fun hn => hn (by simp))
  exact hsecond.2 d (by simp) hda hdold

/-- Declaring one unlabelled vertex and deleting the specified links
preserves all seventeen concrete ordinary rooted rules. -/
theorem rootedLegal (hG : RootedLegal G (sumRooting D)) (hu : Undeclared G a) :
    RootedLegal (graph G a τ) (sumRooting D) := by
  classical
  constructor
  · intro e he
    have hmodel : (e.toLeft, e.toRight) ∈ (model (graph G a τ)).edges :=
      (mem_model _ _ _).mpr (by simpa only [Finset.toLeft_disjSum_toRight] using he)
    have hleft : e.toLeft.Nonempty := by
      by_contra hn
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
      have hd : e.toRight ∈ (model (graph G a τ)).dataTriples :=
        ((model (graph G a τ)).mem_dataTriples _).mpr (by simpa only [hempty] using hmodel)
      rw [dataTriples_unchanged, RootData.dataTriples_empty G hG] at hd
      exact Finset.notMem_empty _ hd
    obtain ⟨r, hr⟩ := hleft
    exact ⟨Sum.inl r, Finset.mem_toLeft.mp hr, (Rooting.mem_range _ _).mpr ⟨r, rfl⟩⟩
  · intro r hr x y hl
    exact hG.passive_empty r hr x y (link_old G a τ hl)
  · intro x σ ρ hσ hρ
    obtain ⟨d, rfl⟩ := sumRooting_data_exists hσ.1
    rcases (graph_declared G a τ σ d).mp hσ with hσ | ⟨hd, hs⟩
    · rcases (graph_declared G a τ ρ d).mp hρ with hρ | ⟨hd, _⟩
      · exact hG.declarations_unique _ _ _ hσ hρ
      · subst d; exact False.elim (hu σ hσ)
    · rcases (graph_declared G a τ ρ d).mp hρ with hρ | ⟨_, hr⟩
      · subst d; exact False.elim (hu ρ hρ)
      · exact hs.trans hr.symm
  · intro r hr x y σ ρ hx hy hl heq
    subst ρ
    obtain ⟨d, rfl⟩ := sumRooting_data_exists hx.1
    obtain ⟨e, rfl⟩ := sumRooting_data_exists hy.1
    by_cases hd : d = a
    · subst d
      exact no_equal_type_link_at_new G a τ hu hx hy hl
    by_cases he : e = a
    · subst e
      exact no_equal_type_link_at_new G a τ hu hy hx (link_symm hl)
    exact hG.generic_different r hr _ _ σ σ
      (declared_old_of_ne G a τ (fun h => hd (Sum.inr.inj h)) hx)
      (declared_old_of_ne G a τ (fun h => he (Sum.inr.inj h)) hy) (link_old G a τ hl) rfl
  · intro r x y σ ρ hx hy hl
    have hn := special_link_ne G a τ (layerRoot_special r) hl
    exact hG.special_allowed r x y σ ρ (declared_old_of_ne G a τ hn.1 hx)
      (declared_old_of_ne G a τ hn.2 hy) (link_old G a τ hl)
  · intro b x y z hxy hxz
    exact hG.matching_left b x y z (matchingEdge_old G a τ hxy) (matchingEdge_old G a τ hxz)
  · intro b x y z hxz hyz
    exact hG.matching_right b x y z (matchingEdge_old G a τ hxz) (matchingEdge_old G a τ hyz)
  · intro b c x y p hx hy hxp hyp
    exact hG.port_base_unique b c x y p
      (declared_old_of_ne G a τ (matchingEdge_ne G a τ hxp).1 hx)
      (declared_old_of_ne G a τ (matchingEdge_ne G a τ hyp).1 hy)
      (matchingEdge_old G a τ hxp) (matchingEdge_old G a τ hyp)
  · intro b c x y p hx hy hxp hyp
    exact hG.port_center_unique b c x y p
      (isCenter_old_of_ne G a τ (matchingEdge_ne G a τ hxp).1 hx)
      (isCenter_old_of_ne G a τ (matchingEdge_ne G a τ hyp).1 hy)
      (matchingEdge_old G a τ hxp) (matchingEdge_old G a τ hyp)
  · intro b x o o' hxo hxo'
    exact hG.owner_functional b x o o' (ownerEdge_old G a τ hxo) (ownerEdge_old G a τ hxo')
  · intro r x y c hxc hyc hxy
    exact hG.same_component_forbidden r x y c (structuralAt_old G a τ hxc)
      (structuralAt_old G a τ hyc) (link_old G a τ hxy)
  · intro x y hx hy
    exact hG.marks_unique x y (marked_old G a τ hx) (marked_old G a τ hy)
  · intro x y o p hxy hxo hyp
    exact hG.E_preserves_vertical x y o p (completeE_old G a τ hxy)
      (ownerEdge_old G a τ hxo) (ownerEdge_old G a τ hyp)
  · intro x y z hxz hyz
    exact hG.parentH_unique x y z (parentH_old G a τ hxz) (parentH_old G a τ hyz)
  · intro x y z hxz hyz
    exact hG.parentV_unique x y z (parentV_old G a τ hxz) (parentV_old G a τ hyz)
  · intro m x y o hm hmo hxo hxy
    exact hG.boundaryH m x y o (marked_old G a τ hm) (ownerEdge_old G a τ hmo)
      (ownerEdge_old G a τ hxo) (hxy.imp (completeE_old G a τ) (completeD_old G a τ))
  · intro m x y o hm hmo hxo hxy
    exact hG.boundaryV m x y o (marked_old G a τ hm) (ownerEdge_old G a τ hmo)
      (ownerEdge_old G a τ hxo) (completeD_old G a τ hxy)

theorem root_edge_preserved {p : Finset Root} (hp : p.image (Sum.inl : Root → Root ⊕ D) ∈ G.edges) :
    p.image (Sum.inl : Root → Root ⊕ D) ∈ (graph G a τ).edges := by
  have hm : p ∈ (model G).rootTriples := by
    apply ((model G).mem_rootTriples p).mpr
    apply (mem_model G p ∅).mpr
    rw [Finset.disjSum_empty, Finset.map_eq_image]
    exact hp
  rw [← rootTriples_unchanged G a τ] at hm
  have hh := (mem_model (graph G a τ) p ∅).mp (((model _).mem_rootTriples p).mp hm)
  rw [Finset.disjSum_empty, Finset.map_eq_image] at hh
  exact hh

theorem two_root_edge_preserved {p : Finset Root} {d : D}
    (hp : insert (Sum.inr d) (p.image Sum.inl) ∈ G.edges) :
    insert (Sum.inr d) (p.image Sum.inl) ∈ (graph G a τ).edges := by
  have heq : p.disjSum ({d} : Finset D) = insert (Sum.inr d) (p.image Sum.inl) := by
    ext (r | x) <;> simp
  have hm : p ∈ (model G).rootLink d := by
    apply ((model G).mem_rootLink d p).mpr
    apply (mem_model G p {d}).mpr
    simpa only [heq] using hp
  have hm' : p ∈ (model (graph G a τ)).rootLink d := by
    rw [rootLink_unchanged]
    exact Finset.mem_union_left _ hm
  have hh := (mem_model (graph G a τ) p {d}).mp (((model _).mem_rootLink d p).mp hm')
  simpa only [heq] using hh

theorem completed (hG : Completed G) (hu : Undeclared G a) : Completed (graph G a τ) where
  legal := rootedLegal G a τ hG.legal hu
  root_clique := fun p hp => root_edge_preserved G a τ (hG.root_clique p hp)
  neutral_pairs := fun p hp hn d => two_root_edge_preserved G a τ (hG.neutral_pairs p hp hn d)

end TranscendentalTuran.Source.TypeSurgery
