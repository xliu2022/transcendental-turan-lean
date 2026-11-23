module

public import TranscendentalTuran.Network.PartialIso

@[expose] public section

/-!
# Partial bijections obtained from functional relations

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Network.PartialIso

attribute [local instance] Classical.propDecidable

variable {A B : Type*}

theorem comp_forward_iff {C : Type*} (f : PartialIso A B) (g : PartialIso B C)
    (a : A) (c : C) :
    (f.comp g).forward a = some c ↔ ∃ b, f.forward a = some b ∧ g.forward b = some c :=
  Option.bind_eq_some_iff

theorem symm_forward_iff (f : PartialIso A B) (a : A) (b : B) :
    f.symm.forward b = some a ↔ f.forward a = some b := (f.reverse a b).symm

noncomputable def relationMap (R : A → B → Prop) (a : A) : Option B := by
  classical
  exact if h : ∃ b, R a b then some h.choose else none

theorem relationMap_some_iff (R : A → B → Prop)
    (hR : ∀ a b c, R a b → R a c → b = c) (a : A) (b : B) :
    relationMap R a = some b ↔ R a b := by
  classical
  by_cases h : ∃ b, R a b
  · rw [relationMap, dif_pos h, Option.some.injEq]
    constructor
    · intro he; exact he ▸ h.choose_spec
    · exact fun hb => hR a _ b h.choose_spec hb
  · rw [relationMap, dif_neg h]
    constructor
    · intro he; cases he
    · exact fun hb => False.elim (h ⟨b, hb⟩)

noncomputable def ofRel (R : A → B → Prop)
    (hf : ∀ a b c, R a b → R a c → b = c)
    (hb : ∀ a b c, R a c → R b c → a = b) : PartialIso A B where
  forward := relationMap R
  backward := relationMap (fun b a => R a b)
  reverse a b := by
    rw [relationMap_some_iff R hf,
      relationMap_some_iff (fun b a => R a b) (fun c a b => hb a b c)]

theorem ofRel_forward (R : A → B → Prop) (hf hb) (a : A) (b : B) :
    (ofRel R hf hb).forward a = some b ↔ R a b := relationMap_some_iff R hf a b

theorem ofRel_backward (R : A → B → Prop) (hf hb) (a : A) (b : B) :
    (ofRel R hf hb).backward b = some a ↔ R a b :=
  relationMap_some_iff (fun b a => R a b) (fun c a b => hb a b c) b a

theorem dot_push_eq_sum [Fintype A] [Fintype B] (f : PartialIso A B)
    (x : A → ℝ) (y : B → ℝ) :
    dot x (f.push y) = ∑ a, ∑ b, if f.forward a = some b then x a * y b else 0 := by
  classical
  unfold dot
  apply Finset.sum_congr rfl
  intro a _
  cases h : f.forward a <;> simp [push, h]

theorem ofRel_dot [Fintype A] [Fintype B] (R : A → B → Prop) (hf hb)
    (x : A → ℝ) (y : B → ℝ) :
    dot x ((ofRel R hf hb).push y) = ∑ a, ∑ b, if R a b then x a * y b else 0 := by
  classical
  rw [dot_push_eq_sum]
  simp only [ofRel_forward]

end TranscendentalTuran.Network.PartialIso
