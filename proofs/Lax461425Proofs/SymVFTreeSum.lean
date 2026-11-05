import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
Sums over assignments that agree with a fixed assignment outside a finite set. Such sums
split over disjoint sets when the summands only read the values on disjoint regions. This is
the bookkeeping behind the elimination-forest formulas for homomorphism polynomials.
-/

namespace Lax461425Proofs.SymVFTreeSum

open scoped Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [CommSemiring R]

/-- The assignments agreeing with `h` outside `D`. -/
noncomputable def agree (D : Finset α) (h : α → β) : Finset (α → β) :=
  Finset.univ.filter fun g => ∀ w ∉ D, g w = h w

/-- The sum of `f` over all assignments agreeing with `h` outside `D`. -/
noncomputable def sm (D : Finset α) (h : α → β) (f : (α → β) → R) : R :=
  ∑ g ∈ agree D h, f g

/-- `f` only reads the values on `S`. -/
def DependsOn (f : (α → β) → R) (S : Set α) : Prop :=
  ∀ g g' : α → β, (∀ w ∈ S, g w = g' w) → f g = f g'

theorem mem_agree {D : Finset α} {h g : α → β} : g ∈ agree D h ↔ ∀ w ∉ D, g w = h w := by
  simp [agree]

theorem sm_empty (h : α → β) (f : (α → β) → R) : sm ∅ h f = f h := by
  unfold sm
  have : agree (∅ : Finset α) h = {h} := by
    ext g
    simp only [mem_agree, Finset.notMem_empty, not_false_eq_true, forall_const,
      Finset.mem_singleton]
    exact ⟨fun hg => funext hg, fun hg => by simp [hg]⟩
  rw [this, Finset.sum_singleton]

/-- Summing over one more coordinate. -/
theorem sm_insert {v : α} {D : Finset α} (hv : v ∉ D) (h : α → β) (f : (α → β) → R) :
    sm (insert v D) h f = ∑ i, sm D (Function.update h v i) f := by
  unfold sm
  simp only [agree, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  have hiff : ∀ i, (∀ w ∉ D, g w = Function.update h v i w) ↔
      (g v = i ∧ ∀ w ∉ insert v D, g w = h w) := by
    intro i
    constructor
    · intro H
      refine ⟨?_, ?_⟩
      · simpa using H v hv
      · intro w hw
        have hwv : w ≠ v := fun e => hw (e ▸ Finset.mem_insert_self _ _)
        have hwD : w ∉ D := fun e => hw (Finset.mem_insert_of_mem e)
        simpa [Function.update_of_ne hwv] using H w hwD
    · rintro ⟨rfl, H⟩ w hw
      by_cases hwv : w = v
      · subst hwv; simp
      · rw [Function.update_of_ne hwv]
        exact H w (by simp [hwv, hw])
  simp_rw [hiff]
  by_cases hg : ∀ w ∉ insert v D, g w = h w
  · rw [if_pos hg, Finset.sum_eq_single (g v)]
    · rw [if_pos ⟨rfl, hg⟩]
    · intro b _ hb
      exact if_neg (fun hx => hb hx.1.symm)
    · intro hx; exact absurd (Finset.mem_univ _) hx
  · rw [if_neg hg]
    exact (Finset.sum_eq_zero (fun x _ => if_neg (fun hx => hg hx.2))).symm

/-- A factor that only reads values outside `D` comes out of the sum. -/
theorem sm_mul_left {D : Finset α} {S : Set α} (hS : ∀ w ∈ S, w ∉ D) (h : α → β)
    (f F : (α → β) → R) (hf : DependsOn f S) :
    sm D h (fun g => f g * F g) = f h * sm D h F := by
  unfold sm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  change f g * F g = f h * F g
  rw [hf g h (fun w hw => (mem_agree.mp hg) w (hS w hw))]

/-- Two disjoint regions with factors reading disjoint regions. -/
theorem sm_union {D₁ D₂ : Finset α} (hD : Disjoint D₁ D₂) {S₁ S₂ : Set α}
    (h₁ : ∀ w ∈ S₁, w ∉ D₂) (h₂ : ∀ w ∈ S₂, w ∉ D₁) (h : α → β)
    (f₁ f₂ : (α → β) → R) (hf₁ : DependsOn f₁ S₁) (hf₂ : DependsOn f₂ S₂) :
    sm (D₁ ∪ D₂) h (fun g => f₁ g * f₂ g) = sm D₁ h f₁ * sm D₂ h f₂ := by
  unfold sm
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p => fun w => if w ∈ D₁ then p.1 w else p.2 w)
    (fun g => (fun w => if w ∈ D₁ then g w else h w, fun w => if w ∈ D₂ then g w else h w))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨g₁, g₂⟩ hp
    rw [Finset.mem_product] at hp
    rw [mem_agree]
    intro w hw
    have hw2 : w ∉ D₂ := fun e => hw (Finset.mem_union_right _ e)
    have hw1 : w ∉ D₁ := fun e => hw (Finset.mem_union_left _ e)
    simp only [hw1, if_false]
    exact (mem_agree.mp hp.2) w hw2
  · intro g hg
    rw [mem_agree] at hg
    rw [Finset.mem_product, mem_agree, mem_agree]
    constructor
    · intro w hw; simp [hw]
    · intro w hw; simp [hw]
  · rintro ⟨g₁, g₂⟩ hp
    rw [Finset.mem_product, mem_agree, mem_agree] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only at hp1 hp2
    simp only [Prod.mk.injEq]
    constructor
    · funext w
      by_cases hw : w ∈ D₁
      · simp [hw]
      · simp [hw, hp1 w hw]
    · funext w
      by_cases hw : w ∈ D₂
      · have hw1 : w ∉ D₁ := fun e => Finset.disjoint_left.mp hD e hw
        simp [hw, hw1]
      · by_cases hw1 : w ∈ D₁
        · simp [hw, hw1, hp2 w hw]
        · simp [hw, hw1, hp2 w hw]
  · intro g hg
    rw [mem_agree] at hg
    funext w
    by_cases hw1 : w ∈ D₁
    · simp [hw1]
    · by_cases hw2 : w ∈ D₂
      · simp [hw1, hw2]
      · simp [hw1, hw2, hg w (by simp [hw1, hw2])]
  · rintro ⟨g₁, g₂⟩ hp
    rw [Finset.mem_product, mem_agree, mem_agree] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only at hp1 hp2
    congr 1
    · apply hf₁
      intro w hw
      have hw2 := h₁ w hw
      by_cases hw1 : w ∈ D₁
      · simp [hw1]
      · simp [hw1, hp1 w hw1, hp2 w hw2]
    · apply hf₂
      intro w hw
      have hw1 := h₂ w hw
      simp [hw1]

theorem dependsOn_mono {f : (α → β) → R} {S T : Set α} (hf : DependsOn f S) (hST : S ⊆ T) :
    DependsOn f T := fun g g' hg => hf g g' (fun w hw => hg w (hST hw))

theorem dependsOn_prod {ι : Type*} (s : Finset ι) (f : ι → (α → β) → R) (S : ι → Set α)
    (hf : ∀ i ∈ s, DependsOn (f i) (S i)) :
    DependsOn (fun g => ∏ i ∈ s, f i g) (⋃ i ∈ s, S i) := by
  intro g g' hg
  apply Finset.prod_congr rfl
  intro i hi
  apply hf i hi
  intro w hw
  exact hg w (Set.mem_biUnion hi hw)

/-- A product over a family of pairwise disjoint regions. -/
theorem sm_biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (D : ι → Finset α)
    (S : ι → Set α) (f : ι → (α → β) → R) (hf : ∀ i ∈ s, DependsOn (f i) (S i))
    (hD : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (D i) (D j))
    (hS : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ w ∈ S i, w ∉ D j) (h : α → β) :
    sm (s.biUnion D) h (fun g => ∏ i ∈ s, f i g) = ∏ i ∈ s, sm (D i) h (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [sm_empty]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    rw [Finset.biUnion_insert, Finset.prod_insert ha]
    simp_rw [Finset.prod_insert ha]
    rw [sm_union (S₁ := S a) (S₂ := ⋃ i ∈ s, S i)]
    · rw [ih (fun i hi => hf i (hs i hi)) (fun i hi j hj => hD i (hs i hi) j (hs j hj))
        (fun i hi j hj => hS i (hs i hi) j (hs j hj))]
    · rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hD a (Finset.mem_insert_self _ _) j (hs j hj) (fun e => ha (e ▸ hj))
    · intro w hw hw'
      obtain ⟨j, hj, hwj⟩ := Finset.mem_biUnion.mp hw'
      exact hS a (Finset.mem_insert_self _ _) j (hs j hj) (fun e => ha (e ▸ hj)) w hw hwj
    · intro w hw hw'
      obtain ⟨j, hj, hwj⟩ := Set.mem_iUnion₂.mp hw
      exact hS j (hs j hj) a (Finset.mem_insert_self _ _) (fun e => ha (e ▸ hj)) w hwj hw'
    · exact hf a (Finset.mem_insert_self _ _)
    · exact dependsOn_prod s f S (fun i hi => hf i (hs i hi))

end Lax461425Proofs.SymVFTreeSum
