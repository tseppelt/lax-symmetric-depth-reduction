import Lax461425Proofs.PathRefinementSchedule
import Lax461425Proofs.PatternsLabelledBasic

/-!
A linear schedule of the nodes of Tim's root-exact decomposition yields graph bags of
size at most twice the old width. The interval proof uses the existing connectedness
axiom of that decomposition. No new homomorphism-polynomial semantics are introduced.
-/

namespace Lax461425Proofs.PathRefinementDecomposition

open PatternsLabelledBasic PathRefinementSchedule
open scoped Classical

/-- Every nonempty predicate on a finite-depth parent tree has an entry node. -/
theorem exists_entry {A : Type*} (parent : A → A) (root : A) (depth : ℕ)
    (hdepth : ∀ a, parent^[depth] a = root) (P : A → Prop) (hne : ∃ a, P a) :
    ∃ a, P a ∧ (a = root ∨ ¬ P (parent a)) := by
  by_contra hn
  have hstep : ∀ a, P a → a ≠ root ∧ P (parent a) := by
    intro a ha
    constructor
    · exact fun he => hn ⟨a, ha, Or.inl he⟩
    · by_contra hp
      exact hn ⟨a, ha, Or.inr hp⟩
  obtain ⟨a, ha⟩ := hne
  have hi : ∀ m, P (parent^[m] a) := by
    intro m
    induction m with
    | zero => exact ha
    | succ m ih => simpa only [Function.iterate_succ_apply'] using (hstep _ ih).2
  have hr : P root := by rw [← hdepth a]; exact hi depth
  exact (hstep root hr).1 rfl

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The additional certificate attached to an existing root-exact decomposition. -/
structure LinearDecomposition {ℓ r : ℕ} (G : LabelledPattern ℓ r) (depth width : ℕ) where
  tree : RootExactDecomposition G depth width
  schedule : Schedule tree.parent tree.root

noncomputable section

variable {ℓ r depth width : ℕ} {G : LabelledPattern ℓ r}
variable (D : RootExactDecomposition G depth width) (S : Schedule D.parent D.root)

def composedBag (i : Fin (S.length + 1)) : Finset (G.F.A ⊕ G.F.B) :=
  (S.bag i).biUnion D.bag

theorem mem_composedBag {v : G.F.A ⊕ G.F.B} {i : Fin (S.length + 1)} :
    v ∈ composedBag D S i ↔ ∃ t, t ∈ S.bag i ∧ v ∈ D.bag t := by
  simp [composedBag]

theorem composedBag_card (i : Fin (S.length + 1)) :
    (composedBag D S i).card ≤ 2 * width := by
  calc
    _ ≤ ∑ t ∈ S.bag i, (D.bag t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ S.bag i, width := Finset.sum_le_sum (fun t _ => D.card_bag_le t)
    _ = (S.bag i).card * width := by simp
    _ ≤ 2 * width := Nat.mul_le_mul_right width (S.card i)

theorem composedBag_cover (v : G.F.A ⊕ G.F.B) (hv : ¬ isIsolated G.F v) :
    ∃ i, v ∈ composedBag D S i := by
  obtain ⟨t, ht⟩ := D.exists_mem_bag v hv
  obtain ⟨i, hi⟩ := S.cover t
  exact ⟨i, (mem_composedBag D S).mpr ⟨t, hi, ht⟩⟩

theorem composedBag_edge (a : G.F.A) (b : G.F.B) (hab : G.F.mult a b ≠ 0) :
    ∃ i, Sum.inl a ∈ composedBag D S i ∧ Sum.inr b ∈ composedBag D S i := by
  obtain ⟨t, ha, hb⟩ := D.exists_edge_mem_bag a b hab
  obtain ⟨i, hi⟩ := S.cover t
  exact ⟨i, (mem_composedBag D S).mpr ⟨t, hi, ha⟩, (mem_composedBag D S).mpr ⟨t, hi, hb⟩⟩

/-- Connected old graph bags remain intervals after composing with the node schedule. -/
theorem composedBag_interval (v : G.F.A ⊕ G.F.B) (i j l : Fin (S.length + 1))
    (hij : i ≤ j) (hjl : j ≤ l)
    (hi : v ∈ composedBag D S i) (hl : v ∈ composedBag D S l) :
    v ∈ composedBag D S j := by
  by_contra hn
  have hgap : ∀ t, v ∈ D.bag t → t ∉ S.bag j := by
    intro t ht hs
    exact hn ((mem_composedBag D S).mpr ⟨t, hs, ht⟩)
  let L : D.Node → Prop := fun t => v ∈ D.bag t ∧ ∃ q, q < j ∧ t ∈ S.bag q
  let R : D.Node → Prop := fun t => v ∈ D.bag t ∧ ∃ q, j < q ∧ t ∈ S.bag q
  have hclass : ∀ t, v ∈ D.bag t → L t ∨ R t := by
    intro t ht
    obtain ⟨q, hq⟩ := S.cover t
    rcases lt_trichotomy q j with hlt | he | hgt
    · exact Or.inl ⟨ht, q, hlt, hq⟩
    · subst q; exact (hgap t ht hq).elim
    · exact Or.inr ⟨ht, q, hgt, hq⟩
  have hcross : ∀ a b, L a → R b →
      (∃ q, a ∈ S.bag q ∧ b ∈ S.bag q) → False := by
    rintro a b ⟨ha, qa, hqa, hma⟩ ⟨hb, qb, hqb, hmb⟩ ⟨q, hq₁, hq₂⟩
    by_cases hq : q ≤ j
    · exact hgap b hb (S.interval b q j qb hq (le_of_lt hqb) hq₂ hmb)
    · exact hgap a ha (S.interval a qa j q (le_of_lt hqa) (le_of_not_ge hq) hma hq₁)
  have hL : ∃ t, L t := by
    obtain ⟨t, ht, hv⟩ := (mem_composedBag D S).mp hi
    refine ⟨t, hv, i, ?_, ht⟩
    exact lt_of_le_of_ne hij (fun he => hn (he ▸ hi))
  have hR : ∃ t, R t := by
    obtain ⟨t, ht, hv⟩ := (mem_composedBag D S).mp hl
    refine ⟨t, hv, l, ?_, ht⟩
    exact lt_of_le_of_ne hjl (fun he => hn (he.symm ▸ hl))
  obtain ⟨a, ha, hea⟩ := exists_entry D.parent D.root depth D.depth_le L hL
  obtain ⟨b, hb, heb⟩ := exists_entry D.parent D.root depth D.depth_le R hR
  have hea' : a = D.root ∨ v ∉ D.bag (D.parent a) := by
    rcases hea with he | he
    · exact Or.inl he
    · apply Or.inr
      intro hp
      rcases hclass (D.parent a) hp with hleft | hright
      · exact he hleft
      · exact hcross a (D.parent a) ha hright (S.edge a)
  have heb' : b = D.root ∨ v ∉ D.bag (D.parent b) := by
    rcases heb with he | he
    · exact Or.inl he
    · apply Or.inr
      intro hp
      rcases hclass (D.parent b) hp with hleft | hright
      · obtain ⟨q, hqb, hqp⟩ := S.edge b
        exact hcross (D.parent b) b hleft hb ⟨q, hqp, hqb⟩
      · exact he hright
  have he : a = b := D.connected v a b ha.1 hea' hb.1 heb'
  subst b
  obtain ⟨q, hq⟩ := S.cover a
  exact hcross a a ha hb ⟨q, hq, hq⟩

end

end Lax461425Proofs.PathRefinementDecomposition
