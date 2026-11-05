import Lax461425.CircuitProperties
import Lax461425Proofs.RigidSymmetric
import Lax461425Proofs.SymVFSupportDepthBasic
import Mathlib.Logic.Equiv.Fintype

/-!
Orbit lower bounds for formulas via their rigidification. A path of the rigidification lifts to
a path of the formula. In a formula, every non-input gate has a unique parent, so the image of
the lifted end gate under an automorphism determines the images of all classes on the path.
Hence the gate orbit is at least the number of translates of the path, which is at least the
number of translates of the union of the supports along the path.
-/

namespace Lax461425Proofs.SymVFSupportDepthOrbit

open Lax461425.Circuits Lax461425.CircuitProperties Lax461425.MatrixSymmetry Lax461425.Supports
open Lax461425Proofs.PatternsSupportAction Lax461425Proofs.PatternsSupportBasic
open RigidEquiv RigidWeight RigidRep RigidConstruction RigidSymmetric SymVFSupportDepthBasic

open scoped Classical

variable {K : Type*} {n : ℕ}

/-- In a formula, a non-input gate has at most one parent. -/
theorem parent_unique {V : Type*} {C : Circuit V K} (hf : IsFormula C) {g a b : C.Gate}
    (hg : ¬ (C.label g).IsInput) (ha : 0 < C.wire a g) (hb : 0 < C.wire b g) : a = b := by
  by_contra hne
  have h1 := hf.2 g hg
  have h2 := Finset.sum_le_sum_of_subset (f := fun h => C.wire h g) (Finset.subset_univ {a, b})
  rw [Finset.sum_pair hne] at h2
  omega

theorem isInput_map {V : Type*} (l : GateLabel V K) (π : V → V) :
    (l.map π).IsInput ↔ l.IsInput := by cases l <;> rfl

theorem not_isInput_of_wire_pos {V : Type*} {C : Circuit V K} {g h : C.Gate}
    (hw : 0 < C.wire g h) : ¬ (C.label g).IsInput := by
  intro hi
  rw [C.wire_eq_zero_of_isInput g h hi] at hw
  exact lt_irrefl 0 hw

variable (C : Circuit (Fin n × Fin n) K)

/-- The equivariance of the quotient map onto the rigidification. -/
theorem σOf_toC' (hrig : IsRigid (reduced C)) {γ : Γ n} {σ : C.Gate ≃ C.Gate}
    (hσ : Extends C σ (actVar γ)) (g : C.Gate) :
    σOf hrig γ (toC' C g) = toC' C (σ g) := by
  have hσ2 : Extends C σ (⇑(Equiv.prodCongr γ.1 γ.2)) := hσ
  rw [← σOf_unique hrig (extends_toC'Equiv hσ)]
  show toC' C (σ (rep C g)) = toC' C (σ g)
  exact RigidSymmetric.toC'_eq_of_equiv C
    ((equiv_extends C hσ2 (rep C g) g).mpr (equiv_symm C (rep_equiv C g)))

theorem equiv_of_toC'_eq {g : C.Gate} {b : (reduced C).Gate} (h : toC' C g = b) :
    RigidEquiv.Equiv C g b.1 := by
  have : rep C g = b.1 := congrArg Subtype.val h
  rw [← this]
  exact rep_equiv C g

/-- Paths of the rigidification lift to paths of the circuit. -/
theorem lift (q : ℕ → (reduced C).Gate) (k : ℕ)
    (hq : ∀ l < k, 0 < (reduced C).wire (q l) (q (l + 1))) :
    ∃ h : ℕ → C.Gate, (∀ l ≤ k, toC' C (h l) = q l) ∧ ∀ l < k, 0 < C.wire (h l) (h (l + 1)) := by
  induction k with
  | zero =>
    refine ⟨fun _ => (q 0).1, ?_, fun l hl => absurd hl (Nat.not_lt_zero _)⟩
    intro l hl
    rw [Nat.le_zero.mp hl]
    exact toC'_self C (q 0)
  | succ k ih =>
    obtain ⟨h, hh, hw⟩ := ih (fun l hl => hq l (by omega))
    have hW : 0 < W C (q k).1 (q (k + 1)).1 := hq k (by omega)
    rw [← W_eq_of_equiv C (equiv_of_toC'_eq C (hh k le_rfl))] at hW
    obtain ⟨x, hx, hwx⟩ := exists_of_W_pos C hW
    refine ⟨fun l => if l ≤ k then h l else x, ?_, ?_⟩
    · intro l hl
      by_cases hlk : l ≤ k
      · simp only [hlk, if_true]; exact hh l hlk
      · simp only [hlk, if_false]
        rw [show l = k + 1 by omega]
        exact RigidConstruction.toC'_eq_of_equiv C hx
    · intro l hl
      by_cases hlk : l + 1 ≤ k
      · simp only [hlk, show l ≤ k by omega, if_true]; exact hw l (by omega)
      · have hl' : l = k := by omega
        subst hl'
        simp only [le_refl, if_true, show ¬ l + 1 ≤ l by omega, if_false]
        exact hwx

/-- The number of translates of a path of the rigidification ending in a non-input gate is at
most the orbit size of the formula. -/
theorem ncard_range_le (hf : IsFormula C) (hsym : IsMatrixSymmetric C)
    (hrig : IsRigid (reduced C)) (q : ℕ → (reduced C).Gate) (k : ℕ)
    (hq : ∀ l < k, 0 < (reduced C).wire (q l) (q (l + 1)))
    (hint : ¬ ((reduced C).label (q k)).IsInput) :
    (Set.range fun γ : Γ n => fun l : Fin (k + 1) => σOf hrig γ (q l)).ncard ≤ orbitSize C := by
  obtain ⟨h, hh, hw⟩ := lift C q k hq
  choose σ hσ using hsym
  let f : Γ n → C.Gate := fun γ => σ γ (h k)
  let Φ : Γ n → (Fin (k + 1) → (reduced C).Gate) := fun γ l => σOf hrig γ (q l)
  have hint' : ∀ l ≤ k, ¬ (C.label (h l)).IsInput := by
    intro l hl
    rcases Nat.lt_or_ge l k with hlt | hge
    · exact not_isInput_of_wire_pos (hw l hlt)
    · have hlk : l = k := by omega
      subst hlk
      rw [equiv_label_eq C (equiv_of_toC'_eq C (hh l le_rfl))]
      exact hint
  have key : ∀ γ δ, f γ = f δ → Φ γ = Φ δ := by
    intro γ δ hfe
    have hdown : ∀ d ≤ k, σ γ (h (k - d)) = σ δ (h (k - d)) := by
      intro d
      induction d with
      | zero => intro _; exact hfe
      | succ d ih =>
        intro hd
        have ih' := ih (by omega)
        have hl1 : k - d = (k - (d + 1)) + 1 := by omega
        rw [hl1] at ih'
        have hwl := hw (k - (d + 1)) (by omega)
        have hnin : ¬ (C.label (σ γ (h (k - (d + 1) + 1)))).IsInput := by
          rw [(hσ γ).1, isInput_map]
          exact hint' _ (by omega)
        apply parent_unique hf hnin
        · rw [(hσ γ).2]; exact hwl
        · rw [ih', (hσ δ).2]; exact hwl
    funext l
    have hl := hdown (k - l.val) (by omega)
    rw [show k - (k - l.val) = l.val by omega] at hl
    show σOf hrig γ (q l) = σOf hrig δ (q l)
    rw [← hh l.val (by omega), σOf_toC' C hrig (hσ γ), σOf_toC' C hrig (hσ δ), hl]
  have hrange : Set.range Φ ⊆ (Φ ∘ Function.invFun f) '' Set.range f := by
    rintro _ ⟨γ, rfl⟩
    refine ⟨f γ, ⟨γ, rfl⟩, ?_⟩
    exact key _ _ (Function.invFun_eq ⟨γ, rfl⟩)
  have horb : Set.range f ⊆ orbit C (h k) := by
    rintro _ ⟨γ, rfl⟩
    exact ⟨γ, σ γ, hσ γ, rfl⟩
  calc (Set.range Φ).ncard ≤ ((Φ ∘ Function.invFun f) '' Set.range f).ncard :=
        Set.ncard_le_ncard hrange (Set.toFinite _)
    _ ≤ (Set.range f).ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ (orbit C (h k)).ncard := Set.ncard_le_ncard horb (Set.toFinite _)
    _ ≤ orbitSize C := Finset.le_sup (f := fun g => (orbit C g).ncard) (Finset.mem_univ _)

/-- The union of the minimal supports along the first `k + 1` gates. -/
def pathUnion {D : Circuit (Fin n × Fin n) K} (q : ℕ → D.Gate) (k : ℕ) : Set (Fin n ⊕ Fin n) :=
  {x | ∃ l ≤ k, x ∈ minSupport D (q l)}

/-- A permutation of `Fin n` mapping a finite set onto another set of the same size. -/
theorem exists_perm_image (L T : Finset (Fin n)) (h : L.card = T.card) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, i ∈ T ↔ ∃ j ∈ L, e j = i := by
  have hc : Fintype.card {x // x ∈ L} = Fintype.card {x // x ∈ T} := by simpa using h
  let e0 : {x // x ∈ L} ≃ {x // x ∈ T} := Fintype.equivOfCardEq hc
  refine ⟨_root_.Equiv.extendSubtype e0, fun i => ⟨fun hi => ?_, ?_⟩⟩
  · refine ⟨(e0.symm ⟨i, hi⟩).1, (e0.symm ⟨i, hi⟩).2, ?_⟩
    rw [_root_.Equiv.extendSubtype_apply_of_mem e0 _ (e0.symm ⟨i, hi⟩).2]
    simp
  · rintro ⟨j, hj, rfl⟩
    rw [_root_.Equiv.extendSubtype_apply_of_mem e0 _ hj]
    exact (e0 ⟨j, hj⟩).2

variable {D : Circuit (Fin n × Fin n) K}

theorem card_finset_le_ncard {α β : Type*} [Finite β] (S : Finset α) (R : Set β) (G : β → α)
    (hS : ∀ T ∈ S, ∃ b ∈ R, G b = T) : S.card ≤ R.ncard := by
  have hsub : (↑S : Set α) ⊆ G '' R := fun T hT => by
    obtain ⟨b, hb, rfl⟩ := hS T hT
    exact ⟨b, hb, rfl⟩
  rw [← Set.ncard_coe_finset]
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))

/-- The translates of a path realise every left side of the size of the left part of the union
of the supports along it. -/
theorem choose_left_le (hrig : IsRigid D) (hn : 2 * supportSize D < n) (q : ℕ → D.Gate)
    (k : ℕ) :
    n.choose (leftPart (pathUnion q k)).ncard ≤
      (Set.range fun γ : Γ n => fun l : Fin (k + 1) => σOf hrig γ (q l)).ncard := by
  set L := (leftPart (pathUnion q k)).toFinset with hL
  have hLc : (leftPart (pathUnion q k)).ncard = L.card := Set.ncard_eq_toFinset_card' _
  have hch : n.choose L.card = (Finset.univ.powersetCard L.card : Finset (Finset (Fin n))).card := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [hLc, hch]
  apply card_finset_le_ncard _ _
    (fun ψ : Fin (k + 1) → D.Gate =>
      Finset.univ.filter fun i => ∃ l : Fin (k + 1), Sum.inl i ∈ minSupport D (ψ l))
  intro T hT
  obtain ⟨-, hTc⟩ := Finset.mem_powersetCard.mp hT
  obtain ⟨e, he⟩ := exists_perm_image L T hTc.symm
  refine ⟨_, ⟨(e, 1), rfl⟩, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he i]
  constructor
  · rintro ⟨l, hl⟩
    rw [minSupport_smul hrig hn] at hl
    obtain ⟨x, hx, hxi⟩ := hl
    cases x with
    | inl j =>
      refine ⟨j, ?_, Sum.inl_injective hxi⟩
      rw [hL, Set.mem_toFinset]
      exact ⟨l.val, by omega, hx⟩
    | inr j => cases hxi
  · rintro ⟨j, hj, rfl⟩
    rw [hL, Set.mem_toFinset] at hj
    obtain ⟨l, hl, hx⟩ := hj
    refine ⟨⟨l, by omega⟩, ?_⟩
    rw [minSupport_smul hrig hn]
    exact ⟨Sum.inl j, hx, rfl⟩

/-- The right-hand analogue of `choose_left_le`. -/
theorem choose_right_le (hrig : IsRigid D) (hn : 2 * supportSize D < n) (q : ℕ → D.Gate)
    (k : ℕ) :
    n.choose (rightPart (pathUnion q k)).ncard ≤
      (Set.range fun γ : Γ n => fun l : Fin (k + 1) => σOf hrig γ (q l)).ncard := by
  set L := (rightPart (pathUnion q k)).toFinset with hL
  have hLc : (rightPart (pathUnion q k)).ncard = L.card := Set.ncard_eq_toFinset_card' _
  have hch : n.choose L.card = (Finset.univ.powersetCard L.card : Finset (Finset (Fin n))).card := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [hLc, hch]
  apply card_finset_le_ncard _ _
    (fun ψ : Fin (k + 1) → D.Gate =>
      Finset.univ.filter fun i => ∃ l : Fin (k + 1), Sum.inr i ∈ minSupport D (ψ l))
  intro T hT
  obtain ⟨-, hTc⟩ := Finset.mem_powersetCard.mp hT
  obtain ⟨e, he⟩ := exists_perm_image L T hTc.symm
  refine ⟨_, ⟨(1, e), rfl⟩, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he i]
  constructor
  · rintro ⟨l, hl⟩
    rw [minSupport_smul hrig hn] at hl
    obtain ⟨x, hx, hxi⟩ := hl
    cases x with
    | inr j =>
      refine ⟨j, ?_, Sum.inr_injective hxi⟩
      rw [hL, Set.mem_toFinset]
      exact ⟨l.val, by omega, hx⟩
    | inl j => cases hxi
  · rintro ⟨j, hj, rfl⟩
    rw [hL, Set.mem_toFinset] at hj
    obtain ⟨l, hl, hx⟩ := hj
    refine ⟨⟨l, by omega⟩, ?_⟩
    rw [minSupport_smul hrig hn]
    exact ⟨Sum.inr j, hx, rfl⟩

end Lax461425Proofs.SymVFSupportDepthOrbit
