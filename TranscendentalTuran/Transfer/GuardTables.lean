/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TranscendentalTuran.Transfer.TableCounting
public import Mathlib.Algebra.Group.Basic

/-!
# The cyclic diagonal partition of a guard table

The positions in a clique block are a finite additive group. Fixing the two
blocks and the difference of positions partitions their Cartesian square
into diagonal cliques. Every such clique has at most two nonroot entries.
-/

@[expose] public section

namespace TranscendentalTuran.Transfer

universe u v w
variable {B : Type u} {K : Type v} {C : Type w} [AddCommGroup K]

def cyclicPart (p : (B × K) × (B × K)) : B × B × K :=
  (p.1.1, p.2.1, p.2.2 - p.1.2)

theorem cyclicPart_fst_injective {p q : (B × K) × (B × K)}
    (hpart : cyclicPart p = cyclicPart q) (hfirst : p.1 = q.1) : p = q := by
  apply Prod.ext hfirst
  apply Prod.ext
  · exact congrArg (fun x : B × B × K => x.2.1) hpart
  · have hdiff := congrArg (fun x : B × B × K => x.2.2) hpart
    change p.2.2 - p.1.2 = q.2.2 - q.1.2 at hdiff
    rw [congrArg Prod.snd hfirst] at hdiff
    exact sub_left_inj.mp hdiff

theorem cyclicPart_snd_injective {p q : (B × K) × (B × K)}
    (hpart : cyclicPart p = cyclicPart q) (hsecond : p.2 = q.2) : p = q := by
  apply Prod.ext _ hsecond
  apply Prod.ext
  · exact congrArg (fun x : B × B × K => x.1) hpart
  · have hdiff := congrArg (fun x : B × B × K => x.2.2) hpart
    change p.2.2 - p.1.2 = q.2.2 - q.1.2 at hdiff
    rw [congrArg Prod.snd hsecond] at hdiff
    exact sub_right_inj.mp hdiff

/-- The hypothesis says that three entries in distinct rows and columns
of a pair of clique blocks contain a root entry. It follows directly from
a product homomorphism and the fact that target roots meet every edge. -/
theorem guard_table_nonroot_bound [Fintype B] [Fintype K]
    [DecidableEq B] [DecidableEq K] [DecidableEq C]
    (f : (B × K) → (B × K) → C) (roots : Finset C)
    (htriples : ∀ x y z x' y' z' : B × K,
      x ≠ y → x ≠ z → y ≠ z → x' ≠ y' → x' ≠ z' → y' ≠ z' →
      x.1 = y.1 → x.1 = z.1 → x'.1 = y'.1 → x'.1 = z'.1 →
      f x x' ∈ roots ∨ f y y' ∈ roots ∨ f z z' ∈ roots) :
    (nonrootCells f roots).card ≤
      2 * Fintype.card B * Fintype.card B * Fintype.card K := by
  classical
  have h := nonroot_partition_bound (fun p => f p.1 p.2) roots cyclicPart (by
    intro p q r hpq hpr hpq' hpr' hqr'
    have hqr : cyclicPart q = cyclicPart r := hpq.symm.trans hpr
    exact htriples p.1 q.1 r.1 p.2 q.2 r.2
      (fun he => hpq' (cyclicPart_fst_injective hpq he))
      (fun he => hpr' (cyclicPart_fst_injective hpr he))
      (fun he => hqr' (cyclicPart_fst_injective hqr he))
      (fun he => hpq' (cyclicPart_snd_injective hpq he))
      (fun he => hpr' (cyclicPart_snd_injective hpr he))
      (fun he => hqr' (cyclicPart_snd_injective hqr he))
      (congrArg (fun x : B × B × K => x.1) hpq)
      (congrArg (fun x : B × B × K => x.1) hpr)
      (congrArg (fun x : B × B × K => x.2.1) hpq)
      (congrArg (fun x : B × B × K => x.2.1) hpr))
  have hsets : (Finset.univ.filter (fun p : (B × K) × (B × K) =>
      f p.1 p.2 ∉ roots)) = nonrootCells f roots := by
    ext p
    simp [nonrootCells]
  rw [hsets] at h
  simpa [Fintype.card_prod, Nat.mul_assoc] using h

end TranscendentalTuran.Transfer
