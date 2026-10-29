import Lax461425Proofs.RigidConstruction
import Lax461425.MatrixSymmetry

/-!
Helper material for the rigidification proof: the reduced circuit `C'` is matrix-symmetric
whenever `C` is. Every circuit automorphism of `C` preserves the equivalence relation and the
height function, hence induces an automorphism of `C'` extending the same renaming.
-/

namespace Lax461425Proofs.RigidSymmetric

open Lax461425.Circuits Lax461425.MatrixSymmetry RigidHeight RigidEquiv RigidWeight RigidRep
  RigidConstruction

open scoped Classical

variable {V K : Type*} {n : ℕ}

/-- Mapping a label along the identity does nothing. -/
theorem gateLabel_map_id (l : GateLabel V K) : l.map id = l := by cases l <;> rfl

/-- Mapping a label twice composes the renamings. -/
theorem gateLabel_map_map (π π' : V → V) (l : GateLabel V K) :
    (l.map π).map π' = l.map (π' ∘ π) := by cases l <;> rfl

/-- Mapping a label along an injective renaming is injective. -/
theorem gateLabel_map_injective {π : V → V} (hπ : Function.Injective π) :
    Function.Injective (GateLabel.map π : GateLabel V K → GateLabel V K) := by
  intro l l' h
  cases l <;> cases l' <;> simp_all [GateLabel.map, hπ.eq_iff]

variable (C : Circuit V K)

/-- If `σ` extends `π`, then `σ.symm` extends `π.symm`. -/
theorem extends_symm {σ : C.Gate ≃ C.Gate} {π : V ≃ V} (hext : Extends C σ (⇑π)) :
    Extends C σ.symm (⇑π.symm) := by
  constructor
  · intro g
    have h1 := hext.1 (σ.symm g)
    rw [Equiv.apply_symm_apply] at h1
    have h2 : (C.label g).map (⇑π.symm) = ((C.label (σ.symm g)).map π).map (⇑π.symm) := by
      rw [h1]
    rw [gateLabel_map_map, Equiv.symm_comp_self, gateLabel_map_id] at h2
    exact h2.symm
  · intro g h
    have hw := hext.2 (σ.symm g) (σ.symm h)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hw
    exact hw.symm

/-- A circuit automorphism does not increase the height of a gate. -/
theorem height_extends_le {σ : C.Gate ≃ C.Gate} {π : V ≃ V} (hext : Extends C σ (⇑π))
    (g : C.Gate) : height C (σ g) ≤ height C g := by
  induction g using (wellFounded_child C).induction with
  | _ g ih =>
    rw [height_eq C (σ g)]
    apply Finset.sup_le
    intro h' _
    by_cases hc : Child C (σ g) h'
    · rw [dif_pos hc]
      have hc' : Child C g (σ.symm h') := by
        have hw := hext.2 g (σ.symm h')
        rw [Equiv.apply_symm_apply] at hw
        show 0 < C.wire g (σ.symm h')
        rw [← hw]
        exact hc
      have hih : height C (σ (σ.symm h')) ≤ height C (σ.symm h') := ih (σ.symm h') hc'
      rw [Equiv.apply_symm_apply] at hih
      have hlt : height C (σ.symm h') < height C g := height_child_lt C hc'
      omega
    · rw [dif_neg hc]; exact Nat.zero_le _

/-- A circuit automorphism preserves the height of every gate. -/
theorem height_extends_eq {σ : C.Gate ≃ C.Gate} {π : V ≃ V} (hext : Extends C σ (⇑π))
    (g : C.Gate) : height C (σ g) = height C g := by
  apply le_antisymm (height_extends_le C hext g)
  have := height_extends_le C (extends_symm C hext) (σ g)
  rwa [Equiv.symm_apply_apply] at this

/-- A circuit automorphism preserves the equivalence relation, at every level. -/
theorem equivRel_extends {σ : C.Gate ≃ C.Gate} {π : V ≃ V} (hext : Extends C σ (⇑π)) :
    ∀ (k : ℕ) (g g' : C.Gate), EquivRel C k (σ g) (σ g') ↔ EquivRel C k g g' := by
  intro k
  induction k with
  | zero =>
    intro g g'
    constructor
    · rintro ⟨hl, hg0, hg'0⟩
      refine ⟨?_, (height_extends_eq C hext g) ▸ hg0, (height_extends_eq C hext g') ▸ hg'0⟩
      rw [hext.1 g, hext.1 g'] at hl
      exact gateLabel_map_injective π.injective hl
    · rintro ⟨hl, hg0, hg'0⟩
      exact ⟨by rw [hext.1 g, hext.1 g', hl], by rwa [height_extends_eq C hext],
        by rwa [height_extends_eq C hext]⟩
  | succ k ih =>
    intro g g'
    constructor
    · rintro (h | h)
      · exact Or.inl ((ih g g').mp h)
      · obtain ⟨hl, hgk, hg'k, hcond⟩ := h
        refine Or.inr ⟨?_, by rwa [height_extends_eq C hext] at hgk,
          by rwa [height_extends_eq C hext] at hg'k, ?_⟩
        · rw [hext.1 g, hext.1 g'] at hl
          exact gateLabel_map_injective π.injective hl
        · intro b hb
          have hb' : height C (σ b) ≤ k := by rwa [height_extends_eq C hext]
          have hcondb := hcond (σ b) hb'
          have keyg : (∑ h, if EquivRel C k h b then C.wire g h else 0) =
              ∑ h, if EquivRel C k h (σ b) then C.wire (σ g) h else 0 :=
            Fintype.sum_equiv σ _ _ (fun h' => by
              rw [hext.2 g h']
              congr 1
              exact propext (ih h' b).symm)
          have keyg' : (∑ h, if EquivRel C k h b then C.wire g' h else 0) =
              ∑ h, if EquivRel C k h (σ b) then C.wire (σ g') h else 0 :=
            Fintype.sum_equiv σ _ _ (fun h' => by
              rw [hext.2 g' h']
              congr 1
              exact propext (ih h' b).symm)
          rw [keyg, keyg', hcondb]
    · rintro (h | h)
      · exact Or.inl ((ih g g').mpr h)
      · obtain ⟨hl, hgk, hg'k, hcond⟩ := h
        refine Or.inr ⟨by rw [hext.1 g, hext.1 g', hl],
          by rwa [height_extends_eq C hext], by rwa [height_extends_eq C hext], ?_⟩
        intro b hb
        have hbe : height C b = height C (σ.symm b) := by
          have := height_extends_eq C hext (σ.symm b)
          rwa [Equiv.apply_symm_apply] at this
        have hb' : height C (σ.symm b) ≤ k := hbe ▸ hb
        have hcondb := hcond (σ.symm b) hb'
        have keyg : (∑ h, if EquivRel C k h b then C.wire (σ g) h else 0) =
            ∑ h, if EquivRel C k h (σ.symm b) then C.wire g h else 0 := by
          rw [← Equiv.sum_comp σ (fun h => if EquivRel C k h b then C.wire (σ g) h else 0)]
          apply Finset.sum_congr rfl
          intro h' _
          rw [hext.2 g h']
          congr 1
          have hiff : EquivRel C k (σ h') (σ (σ.symm b)) ↔ EquivRel C k h' (σ.symm b) :=
            ih h' (σ.symm b)
          rw [Equiv.apply_symm_apply] at hiff
          exact propext hiff
        have keyg' : (∑ h, if EquivRel C k h b then C.wire (σ g') h else 0) =
            ∑ h, if EquivRel C k h (σ.symm b) then C.wire g' h else 0 := by
          rw [← Equiv.sum_comp σ (fun h => if EquivRel C k h b then C.wire (σ g') h else 0)]
          apply Finset.sum_congr rfl
          intro h' _
          rw [hext.2 g' h']
          congr 1
          have hiff : EquivRel C k (σ h') (σ (σ.symm b)) ↔ EquivRel C k h' (σ.symm b) :=
            ih h' (σ.symm b)
          rw [Equiv.apply_symm_apply] at hiff
          exact propext hiff
        rw [keyg, keyg', hcondb]

/-- A circuit automorphism preserves the equivalence relation. -/
theorem equiv_extends {σ : C.Gate ≃ C.Gate} {π : V ≃ V} (hext : Extends C σ (⇑π))
    (g g' : C.Gate) : Equiv C (σ g) (σ g') ↔ Equiv C g g' := by
  show EquivRel C (height C (σ g)) (σ g) (σ g') ↔ EquivRel C (height C g) g g'
  rw [height_extends_eq C hext]
  exact equivRel_extends C hext (height C g) g g'

/-- A circuit automorphism preserves aggregated weight. -/
theorem W_extends {σ : C.Gate ≃ C.Gate} {π : V ≃ V} (hext : Extends C σ (⇑π)) (x y : C.Gate) :
    W C (σ x) (σ y) = W C x y := by
  unfold W
  rw [← Equiv.sum_comp σ (fun h => if Equiv C h (σ y) then C.wire (σ x) h else 0)]
  apply Finset.sum_congr rfl
  intro h' _
  rw [hext.2 x h']
  congr 1
  exact propext (equiv_extends C hext h' y)

/-- `toC'` only depends on the equivalence class. -/
theorem toC'_eq_of_equiv {x y : C.Gate} (h : Equiv C x y) : toC' C x = toC' C y :=
  Subtype.ext (rep_eq_of_equiv C h)

/-- The automorphism of the reduced circuit induced by a circuit automorphism of `C`. -/
noncomputable def toC'Equiv {σ : C.Gate ≃ C.Gate} {π : V ≃ V} (hext : Extends C σ (⇑π)) :
    (reduced C).Gate ≃ (reduced C).Gate where
  toFun a := toC' C (σ a.1)
  invFun a := toC' C (σ.symm a.1)
  left_inv a := by
    have step1 : Equiv C (σ.symm (rep C (σ a.1))) (σ.symm (σ a.1)) :=
      (equiv_extends C (extends_symm C hext) (rep C (σ a.1)) (σ a.1)).mpr
        (equiv_symm C (rep_equiv C (σ a.1)))
    rw [Equiv.symm_apply_apply] at step1
    have heq := toC'_eq_of_equiv C step1
    rw [toC'_self C a] at heq
    exact heq
  right_inv a := by
    have step1 : Equiv C (σ (rep C (σ.symm a.1))) (σ (σ.symm a.1)) :=
      (equiv_extends C hext (rep C (σ.symm a.1)) (σ.symm a.1)).mpr
        (equiv_symm C (rep_equiv C (σ.symm a.1)))
    rw [Equiv.apply_symm_apply] at step1
    have heq := toC'_eq_of_equiv C step1
    rw [toC'_self C a] at heq
    exact heq

/-- The automorphism of the reduced circuit induced by a circuit automorphism of `C` extending
`γ` also extends `γ`. -/
theorem extends_toC'Equiv {n : ℕ} {C : Circuit (Fin n × Fin n) K} {γ : Γ n} {σ : C.Gate ≃ C.Gate}
    (hext : Extends C σ (actVar γ)) :
    Extends (reduced C) (toC'Equiv C (show Extends C σ (⇑(Equiv.prodCongr γ.1 γ.2)) from hext))
      (actVar γ) := by
  constructor
  · intro a
    show C.label (rep C (σ a.1)) = (C.label a.1).map (actVar γ)
    rw [← equiv_label_eq C (rep_equiv C (σ a.1))]
    exact hext.1 a.1
  · intro a b
    show W C (rep C (σ a.1)) (rep C (σ b.1)) = W C a.1 b.1
    rw [← W_eq_of_equiv C (rep_equiv C (σ a.1)), ← W_eq_rep_right C (σ a.1) (σ b.1)]
    exact W_extends C (show Extends C σ (⇑(Equiv.prodCongr γ.1 γ.2)) from hext) a.1 b.1

/-- The reduced circuit is matrix-symmetric whenever `C` is. -/
theorem isMatrixSymmetric_reduced (C : Circuit (Fin n × Fin n) K)
    (hsym : IsMatrixSymmetric C) : IsMatrixSymmetric (reduced C) := by
  intro γ
  obtain ⟨σ, hext⟩ := hsym γ
  exact ⟨_, extends_toC'Equiv hext⟩

end Lax461425Proofs.RigidSymmetric
