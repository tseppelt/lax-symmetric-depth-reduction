import Lax461425.CircuitProperties
import Lax461425Proofs.BoundedDepthGlueComputes
import Lax461425Proofs.PatternsSupportBasic
import Lax461425Proofs.TaggedFormulaOrbit

/-!
The scaled-sum glue circuit of formulas is a formula. It is matrix-symmetric whenever its blocks
are, and if the scaling constants are pairwise distinct and do not occur in the blocks, every
automorphism fixes each block, so the orbit size is bounded by that of the blocks.
-/

namespace Lax461425Proofs.SymVFCharacterisationGlue

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.CircuitProperties
open scoped Classical

theorem sum_le_one_of_subsingleton {α : Type*} [Fintype α] (w : α → ℕ) (h1 : ∀ a, w a ≤ 1)
    (huniq : ∀ a b, 0 < w a → 0 < w b → a = b) : ∑ a, w a ≤ 1 := by
  by_cases hex : ∃ a, 0 < w a
  · obtain ⟨a, ha⟩ := hex
    rw [Finset.sum_eq_single a (fun b _ hb => by
      by_contra hne; exact hb (huniq b a (Nat.pos_of_ne_zero hne) ha)) (by simp)]
    exact h1 a
  · push_neg at hex
    have h0 : ∀ a, w a = 0 := fun a => Nat.le_zero.mp (hex a)
    simp [h0]

theorem parent_unique {V K : Type*} {C : Circuit V K} (hC : IsFormula C) {g : C.Gate}
    (hg : ¬ (C.label g).IsInput) {a b : C.Gate} (ha : 0 < C.wire a g) (hb : 0 < C.wire b g) :
    a = b := by
  by_contra hne
  have hs := hC.2 g hg
  have hsub := Finset.sum_le_sum_of_subset (f := fun h => C.wire h g)
    (Finset.subset_univ ({a, b} : Finset C.Gate))
  rw [Finset.sum_pair hne] at hsub
  omega

theorem wire_out_eq_zero {V K : Type*} (C : Circuit V K) (g : C.Gate) : C.wire g C.out = 0 := by
  by_contra h
  have hpos : 0 < C.wire g C.out := Nat.pos_of_ne_zero h
  apply C.acyclic C.out
  have h1 : Relation.TransGen (fun h g => 0 < C.wire g h) C.out g := .single hpos
  exact h1.trans_left (C.reaches_out g)

variable {n m : ℕ} {K : Type*} [Field K] [CharZero K] (D : Fin m → Circuit (Fin n × Fin n) K)
  (f : Fin m → K)

theorem gwire_le_one (hD : ∀ i, IsFormula (D i)) (g h : GGate D) : gwire D g h ≤ 1 := by
  rcases g with ⟨i, y⟩ | i | i | ⟨⟩ <;> rcases h with ⟨i', y'⟩ | i' | i' | ⟨⟩
  · rw [gwire_blk_blk]
    split_ifs with h
    · subst h; exact (hD i).1 _ _
    · omega
  · rw [gwire_blk_scaled]; omega
  · rw [gwire_blk_const]; omega
  · rw [gwire_blk_out]; omega
  · rw [gwire_scaled_blk]; split_ifs <;> omega
  · rw [gwire_scaled_scaled]; omega
  · rw [gwire_scaled_const]; split_ifs <;> omega
  · rw [gwire_scaled_out]; omega
  all_goals first
    | (rw [gwire_const_any]; omega)
    | (rw [gwire_out_blk]; omega)
    | (rw [gwire_out_scaled])
    | (rw [gwire_out_const]; omega)
    | (rw [gwire_out_out]; omega)

theorem parent_blk_cases {i : Fin m} {y : (D i).Gate} {a : GGate D}
    (ha : 0 < gwire D a (blk D i y)) :
    (∃ y', a = blk D i y' ∧ 0 < (D i).wire y' y) ∨ (a = scaledG D i ∧ y = (D i).out) := by
  rcases a with ⟨j, z⟩ | j | j | ⟨⟩
  · rw [gwire_blk_blk] at ha
    split_ifs at ha with h
    · subst h; exact Or.inl ⟨z, rfl, ha⟩
    · omega
  · rw [gwire_scaled_blk] at ha
    split_ifs at ha with h h'
    · subst h; exact Or.inr ⟨rfl, h'⟩
    · omega
    · omega
  · rw [gwire_const_any] at ha; omega
  · rw [gwire_out_blk] at ha; omega

theorem glue_isFormula (hD : ∀ i, IsFormula (D i)) : IsFormula (glueCircuit D f) := by
  refine ⟨gwire_le_one D hD, ?_⟩
  intro g hg
  apply sum_le_one_of_subsingleton _ (fun a => gwire_le_one D hD a g)
  intro a b ha hb
  change 0 < gwire D a g at ha
  change 0 < gwire D b g at hb
  rcases g with ⟨i, y⟩ | i | i | ⟨⟩
  · have hy : ¬ ((D i).label y).IsInput := hg
    rcases parent_blk_cases D ha with ⟨ya, rfl, hya⟩ | ⟨rfl, hyo⟩ <;>
      rcases parent_blk_cases D hb with ⟨yb, rfl, hyb⟩ | ⟨rfl, hyo'⟩
    · rw [parent_unique (hD i) hy hya hyb]
    · subst hyo'; rw [wire_out_eq_zero] at hya; omega
    · subst hyo; rw [wire_out_eq_zero] at hyb; omega
    · rfl
  · have key : ∀ a, 0 < gwire D a (scaledG D i) → a = outGG D := by
      intro a ha
      rcases a with ⟨j, z⟩ | j | j | ⟨⟩
      · rw [gwire_blk_scaled] at ha; omega
      · rw [gwire_scaled_scaled] at ha; omega
      · rw [gwire_const_any] at ha; omega
      · rfl
    rw [key a ha, key b hb]
  · exact absurd trivial hg
  · rcases a with ⟨j, z⟩ | j | j | ⟨⟩
    · rw [gwire_blk_out] at ha; omega
    · rw [gwire_scaled_out] at ha; omega
    · rw [gwire_const_any] at ha; omega
    · rw [gwire_out_out] at ha; omega

/-- Blockwise automorphisms, fixing all glue gates. -/
noncomputable def σG (σ : ∀ i, (D i).Gate ≃ (D i).Gate) : GGate D ≃ GGate D :=
  Equiv.sumCongr (Equiv.sigmaCongrRight σ) (Equiv.refl (Fin m ⊕ Fin m ⊕ Unit))

theorem σG_extends {π : Fin n × Fin n → Fin n × Fin n} (σ : ∀ i, (D i).Gate ≃ (D i).Gate)
    (hσ : ∀ i, Extends (D i) (σ i) π) : Extends (glueCircuit D f) (σG D σ) π := by
  constructor
  · rintro (⟨i, y⟩ | i | i | ⟨⟩)
    · exact (hσ i).1 y
    · rfl
    · rfl
    · rfl
  · rintro (⟨i, y⟩ | i | i | ⟨⟩) <;> rintro (⟨i', y'⟩ | i' | i' | ⟨⟩)
    · show gwire D (blk D i (σ i y)) (blk D i' (σ i' y')) = gwire D (blk D i y) (blk D i' y')
      rw [gwire_blk_blk, gwire_blk_blk]
      by_cases heq : i = i'
      · subst heq
        simp only [dif_pos rfl]
        exact (hσ i).2 y y'
      · simp [dif_neg heq]
    · rfl
    · rfl
    · rfl
    · show gwire D (scaledG D i) (blk D i' (σ i' y')) = gwire D (scaledG D i) (blk D i' y')
      rw [gwire_scaled_blk, gwire_scaled_blk]
      by_cases heq : i = i'
      · subst heq
        simp only [dif_pos rfl]
        have hfix : σ i (D i).out = (D i).out :=
          PatternsSupportBasic.extends_fixes_out (hσ i)
        by_cases hy : y' = (D i).out
        · subst hy; rw [hfix]
        · have hy' : σ i y' ≠ (D i).out := by
            intro hc
            exact hy ((σ i).injective (hc.trans hfix.symm))
          simp [hy, hy']
      · simp [dif_neg heq]
    · rfl
    · rfl
    · rfl
    · show gwire D (constG D i) (blk D i' (σ i' y')) = gwire D (constG D i) (blk D i' y')
      rw [gwire_const_any, gwire_const_any]
    · rfl
    · rfl
    · rfl
    · show gwire D (outGG D) (blk D i' (σ i' y')) = gwire D (outGG D) (blk D i' y')
      rw [gwire_out_blk, gwire_out_blk]
    · rfl
    · rfl
    · rfl

theorem glue_isMatrixSymmetric (hsym : ∀ i, IsMatrixSymmetric (D i)) :
    IsMatrixSymmetric (glueCircuit D f) := fun γ =>
  ⟨σG D (fun i => Classical.choose (hsym i γ)),
    σG_extends D f _ (fun i => Classical.choose_spec (hsym i γ))⟩

section Orbit

variable {D f}
variable (hinj : Function.Injective f)
  (hfresh : ∀ i j (y : (D j).Gate), (D j).label y ≠ .const (f i))
variable {τ : GGate D ≃ GGate D} {π : Fin n × Fin n → Fin n × Fin n}
  (hτ : Extends (glueCircuit D f) τ π)
include hinj hfresh hτ

theorem fix_const (i : Fin m) : τ (constG D i) = constG D i := by
  have hl := hτ.1 (constG D i)
  rcases hx : τ (constG D i) with ⟨j, y⟩ | j | j | ⟨⟩ <;> rw [hx] at hl
  · exact absurd hl (hfresh i j y)
  · cases hl
  · have := GateLabel.const.inj hl
    rw [hinj this]
  · cases hl

theorem fix_scaled (i : Fin m) : τ (scaledG D i) = scaledG D i := by
  have hw := hτ.2 (scaledG D i) (constG D i)
  rw [fix_const hinj hfresh hτ i] at hw
  rw [glueCircuit_wire] at hw
  rw [gwire_scaled_const D i i, if_pos rfl] at hw
  rcases hx : τ (scaledG D i) with ⟨j, y⟩ | j | j | ⟨⟩ <;> rw [hx] at hw
  · rw [gwire_blk_const] at hw; omega
  · rw [gwire_scaled_const] at hw
    split_ifs at hw with h
    rw [h]
  · rw [gwire_const_any] at hw; omega
  · rw [gwire_out_const] at hw; omega

theorem fix_blk_out (i : Fin m) : τ (blk D i (D i).out) = blk D i (D i).out := by
  have hw := hτ.2 (scaledG D i) (blk D i (D i).out)
  rw [fix_scaled hinj hfresh hτ i] at hw
  rw [glueCircuit_wire] at hw
  have h1 : gwire D (scaledG D i) (blk D i (D i).out) = 1 := by rw [gwire_scaled_blk]; simp
  rw [h1] at hw
  rcases hx : τ (blk D i (D i).out) with ⟨j, y⟩ | j | j | ⟨⟩ <;> rw [hx] at hw
  · rw [gwire_scaled_blk] at hw
    split_ifs at hw with h h'
    subst h; rw [h']
  · rw [gwire_scaled_scaled] at hw; omega
  · rw [gwire_scaled_const] at hw
    split_ifs at hw with h
    · subst h
      have := hx.trans (fix_const hinj hfresh hτ i).symm
      exact absurd (τ.injective this) (by simp [blk, constG])
  · rw [gwire_scaled_out] at hw; omega

omit hinj hfresh hτ in
theorem eq_blk_of_reach {x z : GGate D} {i : Fin m}
    (hr : Relation.ReflTransGen (fun a b => 0 < (glueCircuit D f).wire b a) x z)
    (hz : ∃ y, z = blk D i y) : ∃ y, x = blk D i y := by
  induction hr with
  | refl => exact hz
  | tail _ hstep ih =>
    apply ih
    obtain ⟨y, rfl⟩ := hz
    by_contra h
    push_neg at h
    have h0 := blk_wire_eq_zero_of_not_blk D (x := _) (y := y) (fun y' he => h y' he)
    change 0 < gwire D _ _ at hstep
    omega

omit hinj hfresh hτ in
theorem blk_reaches_out (i : Fin m) (y : (D i).Gate) :
    Relation.ReflTransGen (fun a b => 0 < (glueCircuit D f).wire b a)
      (blk D i y) (blk D i (D i).out) := by
  apply Relation.ReflTransGen.lift (blk D i) (fun a b hab => ?_) y (D i).out
    ((D i).reaches_out y)
  show 0 < gwire D (blk D i b) (blk D i a)
  rw [gwire_blk_blk]
  simpa using hab

theorem exists_blk_image (i : Fin m) (y : (D i).Gate) : ∃ y', τ (blk D i y) = blk D i y' := by
  have hp := TaggedFormulaOrbit.maps_path hτ (blk_reaches_out (f := f) i y)
  rw [fix_blk_out hinj hfresh hτ i] at hp
  exact eq_blk_of_reach hp ⟨_, rfl⟩

theorem exists_restrict (i : Fin m) :
    ∃ e : (D i).Gate ≃ (D i).Gate, Extends (D i) e π ∧ ∀ y, τ (blk D i y) = blk D i (e y) := by
  choose r hr using exists_blk_image hinj hfresh hτ i
  have hrinj : Function.Injective r := by
    intro a b hab
    have : τ (blk D i a) = τ (blk D i b) := by rw [hr, hr, hab]
    have := τ.injective this
    simpa [blk] using this
  let e := Equiv.ofBijective r ⟨hrinj, Finite.surjective_of_injective hrinj⟩
  refine ⟨e, ⟨fun y => ?_, fun y y' => ?_⟩, hr⟩
  · have hl := hτ.1 (blk D i y)
    rw [hr] at hl
    exact hl
  · have hw := hτ.2 (blk D i y) (blk D i y')
    rw [hr, hr] at hw
    rw [glueCircuit_wire] at hw
    rw [gwire_blk_blk_self, gwire_blk_blk_self] at hw
    exact hw

end Orbit

theorem glue_orbitSize_le (hinj : Function.Injective f)
    (hfresh : ∀ i j (y : (D j).Gate), (D j).label y ≠ .const (f i))
    (B : ℕ) (hB : 1 ≤ B) (hD : ∀ i, orbitSize (D i) ≤ B) :
    orbitSize (glueCircuit D f) ≤ B := by
  apply Finset.sup_le
  intro g _
  have hsingle : ∀ g : GGate D, (∀ γ σ, Extends (glueCircuit D f) σ (actVar γ) → σ g = g) →
      (orbit (glueCircuit D f) g).ncard ≤ B := by
    intro g hg
    have hs : orbit (glueCircuit D f) g ⊆ {g} := by
      rintro _ ⟨γ, σ, hσ, rfl⟩
      exact hg γ σ hσ
    exact (Set.ncard_le_ncard hs).trans (by simpa using hB)
  rcases g with ⟨i, y⟩ | i | i | ⟨⟩
  · have hs : orbit (glueCircuit D f) (blk D i y) ⊆ blk D i '' orbit (D i) y := by
      rintro _ ⟨γ, σ, hσ, rfl⟩
      obtain ⟨e, he, hey⟩ := exists_restrict hinj hfresh hσ i
      exact ⟨e y, ⟨γ, e, he, rfl⟩, (hey y).symm⟩
    calc
      _ ≤ (blk D i '' orbit (D i) y).ncard := Set.ncard_le_ncard hs
      _ ≤ (orbit (D i) y).ncard := Set.ncard_image_le
      _ ≤ orbitSize (D i) :=
        Finset.le_sup (f := fun h => (orbit (D i) h).ncard) (Finset.mem_univ y)
      _ ≤ B := hD i
  · exact hsingle _ (fun γ σ hσ => fix_scaled hinj hfresh hσ i)
  · exact hsingle _ (fun γ σ hσ => fix_const hinj hfresh hσ i)
  · exact hsingle _ (fun γ σ hσ => PatternsSupportBasic.extends_fixes_out hσ)

end Lax461425Proofs.SymVFCharacterisationGlue
