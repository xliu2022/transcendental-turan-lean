module

public import TranscendentalTuran.Construction.GuardedBasis
public import TranscendentalTuran.Construction.RootLower
public import TranscendentalTuran.Transfer.OrdinaryDensity
public import Mathlib.Algebra.Group.Fin.Basic

@[expose] public section

/-!
# One actual forbidden three-graph realizing the source supremum

Every component of the transfer is discharged for the manuscript's concrete
local rules. The only subsequent input needed to identify the value is the
separate variational computation of `classLambda Source.finiteClass`.

The product uses the proved private extension which adds a private vertex
for every core pair, including already covered pairs. This finite construction
variant preserves both properties used in the proof.
-/

namespace TranscendentalTuran.Construction

open TuranUniversality Encoding Parameters Source.Certificates

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

abbrev ProductVertex := (i : Fin guardedBasis.card) → RGraph.ExtensionVertex (Fin (factor i).1)

/-- The categorical product of the actual guarded obstructions' private
pair-covering extensions. -/
@[macro_inline] def productGraph : RGraph ProductVertex 3 :=
  Effective.product fun i => Effective.pairExtension (factor i).2

theorem productGraph_eq : productGraph =
    RGraph.product (fun i : Fin guardedBasis.card => (factor i).2.pairExtension) := by
  calc
    productGraph = RGraph.product
        (fun i : Fin guardedBasis.card => Effective.pairExtension (factor i).2) :=
      Effective.product_eq _
    _ = RGraph.product (fun i : Fin guardedBasis.card => (factor i).2.pairExtension) :=
      congrArg RGraph.product (funext (fun i => Effective.pairExtension_eq (factor i).2))

/-- The actual finite single forbidden graph, relabeled by a finite interval. -/
@[macro_inline] def singleGraph : FiniteGraph 3 := Effective.ofRGraph productGraph

noncomputable def guardMap (i : Fin guardedBasis.card) : Guard.Vertex → Fin (factor i).1 :=
  (factor_contains_guard i).choose

theorem guardMap_embedding (i : Fin guardedBasis.card) :
    Guard.graph.IsEmbedding (factor i).2 (guardMap i) :=
  (factor_contains_guard i).choose_spec

theorem guardMap_triples (i : Fin guardedBasis.card) (x y z : Guard.Vertex)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hbxy : x.1 = y.1) (hbxz : x.1 = z.1) :
    {guardMap i x, guardMap i y, guardMap i z} ∈ (factor i).2.edges := by
  rcases x with ⟨b, a⟩
  rcases y with ⟨c, d⟩
  rcases z with ⟨e, f⟩
  dsimp only at hbxy hbxz
  subst c
  subst e
  have had : a ≠ d := fun h => hxy (by cases h; rfl)
  have haf : a ≠ f := fun h => hxz (by cases h; rfl)
  have hdf : d ≠ f := fun h => hyz (by cases h; rfl)
  simpa only [Finset.image_insert, Finset.image_singleton] using
    (guardMap_embedding i).2 _ (RGraph.cliquePacking_triple b a d f had haf hdf)

/-- The concrete local-rule transfer for a symbolic finite core family.
Keeping the family symbolic prevents elaboration from evaluating its explicit
finite enumeration when constructing the actual witness. -/
theorem family_product_homFree_of_admissible {d : ℕ} (hd : 0 < d)
    (A : Fin d → FiniteGraph 3) (houtside : ∀ i, ¬ Source.finiteClass (A i))
    (guard : (i : Fin d) → Guard.Vertex → Fin (A i).1)
    (hinj : ∀ i, Function.Injective (guard i))
    (hedges : ∀ (i : Fin d) (x y z : Guard.Vertex), x ≠ y → x ≠ z → y ≠ z →
      x.1 = y.1 → x.1 = z.1 → {guard i x, guard i y, guard i z} ∈ (A i).2.edges)
    {V : Type*} [DecidableEq V] (G : RGraph V 3) (hG : Source.Admissible G) :
    (RGraph.product fun i : Fin d => (A i).2.pairExtension).HomFree G := by
  classical
  obtain ⟨μ, hμ⟩ := hG
  letI : NeZero guardBlockSize := ⟨by norm_num [guardBlockSize]⟩
  have hn : 128 ≤ Fintype.card Guard.Vertex := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    rw [Guard.order_value]
    norm_num
  have hsize : (Fintype.card Root : ℝ) ≤ 4 * (Fintype.card Guard.Vertex : ℝ) / 3 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    have hr : (4 : ℝ) * ((Guard.copies * guardBlockSize : ℕ) : ℝ) = 3 * (q : ℝ) := by
      exact_mod_cast Guard.order_ratio
    exact le_of_eq (by linarith)
  apply Transfer.product_homFree_of_no_pattern_factor
    hd
    (by simp only [Fintype.card_fin]; norm_num [guardBlockSize]) hn hsize
    Γ (fun _ he => Γ_card_two he) (fun _ he _ hf hne => Γ_matching he hf hne)
    forbiddenPatterns (fun _ hp => forbiddenPatterns_roots hp)
    (fun _ hp => forbiddenPatterns_data hp) (fun _ hp => forbiddenPatterns_compatible hp)
    (fun i => (A i).2) G
    (fun i hi => houtside i ((admissible_iff_patternClass _).mpr hi))
    guard hinj hedges μ
    ((rootedLegal_iff_patternLegal G μ).mp hμ) ?_ (1 : Fin guardBlockSize)
    (by decide)
  intro x y z he
  obtain ⟨v, hv, hroot⟩ := hμ.covers_edges _ he
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact Or.inl hroot
  · exact Or.inr (Or.inl hroot)
  · exact Or.inr (Or.inr hroot)


theorem productGraph_homFree_of_admissible {V : Type*} [DecidableEq V]
    (G : RGraph V 3) (hG : Source.Admissible G) : productGraph.HomFree G := by
  rw [productGraph_eq]
  exact family_product_homFree_of_admissible (Finset.card_pos.mpr guardedBasis_nonempty)
    factor factor_outside guardMap (fun i => (guardMap_embedding i).1)
    guardMap_triples G hG

theorem singleGraph_homFree_of_admissible {V : Type*} [DecidableEq V]
    (G : RGraph V 3) (hG : Source.Admissible G) : singleGraph.2.HomFree G :=
  (Effective.ofRGraph_homFree productGraph G).mpr (productGraph_homFree_of_admissible G hG)

/-- The guarded basis has the same weighted maximum as the source, proved
directly for every core-free finite probability weighting. -/
theorem core_free_polynomial_bound (n : ℕ) (G : RGraph (Fin n) 3) (x : Fin n → ℝ)
    (hx : ProbabilityWeights x)
    (hfree : ∀ i : Fin guardedBasis.card, ¬ ∃ f, (factor i).2.IsEmbedding G f) :
    6 * G.edgePolynomial x ≤ 6 * classLambda Source.finiteClass := by
  have hclass : Source.finiteClass ⟨n, G⟩ ∨ ¬ Guard.finiteGraph.Contains ⟨n, G⟩ := by
    apply (guardedBasis_spec ⟨n, G⟩).mpr
    intro A hA hAG
    obtain ⟨i, rfl⟩ := factor_surjective hA
    exact hfree i hAG
  rcases hclass with hsource | hguard
  · exact mul_le_mul_of_nonneg_left
      (edgePolynomial_le_classLambda Source.finiteClass G hsource x hx) (by norm_num)
  · have hfreeGuard : ¬ ∃ f, Guard.graph.IsEmbedding G f := fun h =>
      hguard ((Guard.contains_iff ⟨n, G⟩).mpr h)
    exact ((Guard.free_polynomial_bound G hfreeGuard x hx).trans
      Source.root_clique_classLambda_gap).le

theorem singleGraph_has_edges : singleGraph.2.edges.Nonempty := by
  letI : Nonempty (Fin guardedBasis.card) :=
    ⟨⟨0, Finset.card_pos.mpr guardedBasis_nonempty⟩⟩
  apply Effective.ofRGraph_edges_nonempty productGraph
  rw [productGraph_eq]
  exact RGraph.product_edges_nonempty _ (fun i =>
    (factor i).2.pairExtension_edges_nonempty (factor_has_edges i))

theorem singleGraph_turanDensity_upper :
    turanDensity singleGraph.2 ≤ 6 * classLambda Source.finiteClass := by
  letI : Nonempty (Fin guardedBasis.card) :=
    ⟨⟨0, Finset.card_pos.mpr guardedBasis_nonempty⟩⟩
  have hc : 0 ≤ 6 * classLambda Source.finiteClass :=
    mul_nonneg (by norm_num) (classLambda_nonneg _)
  apply turanDensity_upper_of_homFree singleGraph.2
    (Finset.card_pos.mpr singleGraph_has_edges) _ hc
  intro n G hfree
  have hp := (Effective.ofRGraph_homFree productGraph G).mp hfree
  rw [productGraph_eq] at hp
  exact product_homFree_uniform_bound (fun i => (factor i).2)
    (6 * classLambda Source.finiteClass) hc core_free_polynomial_bound n G hp

/-- The complete ordinary-containment transfer for this paper's actual
source class and its actual finite single forbidden three-graph. -/
theorem singleGraph_turanDensity :
    turanDensity singleGraph.2 = 6 * classLambda Source.finiteClass := by
  apply le_antisymm singleGraph_turanDensity_upper
  exact Transfer.classLambda_lower_of_homFree singleGraph Source.finiteClass
    (fun G hG => singleGraph_homFree_of_admissible G.2 hG)

/-- Only the variational source computation is needed after the graph
construction and ordinary-density transfer have been established. -/
theorem singleGraph_turanDensity_of_source_value (a : ℝ)
    (hsource : classLambda Source.finiteClass = a) : turanDensity singleGraph.2 = 6 * a := by
  rw [singleGraph_turanDensity, hsource]

end TranscendentalTuran.Construction
