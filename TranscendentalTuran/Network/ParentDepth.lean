module

public import Mathlib.Data.Nat.Find
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Depth in a relation with unique parents

Formalization author and responsible maintainer: Xizhi Liu.

Self-arrows and cycles are permitted away from the marked component. A root
with no incoming arrow and uniqueness of incoming parents suffice to give
an unambiguous depth on every vertex reachable from that root.
-/

namespace TranscendentalTuran.Network.ParentDepth

variable {V : Type*}

inductive Path (R : V → V → Prop) (root : V) : ℕ → V → Prop
  | here : Path R root 0 root
  | step {n : ℕ} {x y : V} : Path R root n x → R x y → Path R root (n + 1) y

def Reachable (R : V → V → Prop) (root x : V) : Prop := ∃ n, Path R root n x

variable {R : V → V → Prop} {root : V}

theorem length_unique (hroot : ∀ x, ¬ R x root)
    (hparent : ∀ x y z, R x z → R y z → x = y)
    {n m : ℕ} {x : V} (hn : Path R root n x) (hm : Path R root m x) : n = m := by
  induction hn generalizing m with
  | here =>
    cases hm with
    | here => rfl
    | step h hrel => exact (hroot _ hrel).elim
  | @step n x y hn hxy ih =>
    cases hm with
    | here => exact (hroot _ hxy).elim
    | @step m z _ hm hzy =>
      have hxz := hparent x z y hxy hzy
      subst z
      exact congrArg (fun k => k + 1) (ih hm)

theorem predecessor (hroot : ∀ x, ¬ R x root)
    (hparent : ∀ x y z, R x z → R y z → x = y)
    {n : ℕ} {x y : V} (hy : Path R root n y) (hxy : R x y) :
    ∃ m, Path R root m x ∧ n = m + 1 := by
  cases hy with
  | here => exact (hroot _ hxy).elim
  | @step m z y hz hzy =>
    have hxz := hparent x z y hxy hzy
    exact ⟨m, hxz ▸ hz, rfl⟩

theorem reachable_forward {x y : V} (hx : Reachable R root x) (hxy : R x y) :
    Reachable R root y := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n + 1, hn.step hxy⟩

theorem reachable_backward (hroot : ∀ x, ¬ R x root)
    (hparent : ∀ x y z, R x z → R y z → x = y)
    {x y : V} (hy : Reachable R root y) (hxy : R x y) : Reachable R root x := by
  obtain ⟨n, hn⟩ := hy
  obtain ⟨m, hm, _⟩ := predecessor hroot hparent hn hxy
  exact ⟨m, hm⟩

noncomputable def depth (R : V → V → Prop) (root x : V) : ℕ := by
  classical
  exact if h : Reachable R root x then Nat.find h else 0

theorem depth_eq (hroot : ∀ x, ¬ R x root)
    (hparent : ∀ x y z, R x z → R y z → x = y)
    {n : ℕ} {x : V} (hx : Path R root n x) : depth R root x = n := by
  classical
  have hr : Reachable R root x := ⟨n, hx⟩
  rw [depth, dif_pos hr]
  exact length_unique hroot hparent (Nat.find_spec hr) hx

theorem depth_root (hroot : ∀ x, ¬ R x root)
    (hparent : ∀ x y z, R x z → R y z → x = y) : depth R root root = 0 :=
  depth_eq hroot hparent Path.here

theorem depth_step (hroot : ∀ x, ¬ R x root)
    (hparent : ∀ x y z, R x z → R y z → x = y)
    {x y : V} (hx : Reachable R root x) (hxy : R x y) :
    depth R root y = depth R root x + 1 := by
  obtain ⟨n, hn⟩ := hx
  rw [depth_eq hroot hparent hn, depth_eq hroot hparent (hn.step hxy)]

theorem depth_step_back (hroot : ∀ x, ¬ R x root)
    (hparent : ∀ x y z, R x z → R y z → x = y)
    {x y : V} (hy : Reachable R root y) (hxy : R x y) :
    depth R root y = depth R root x + 1 :=
  depth_step hroot hparent (reachable_backward hroot hparent hy hxy) hxy

end TranscendentalTuran.Network.ParentDepth
