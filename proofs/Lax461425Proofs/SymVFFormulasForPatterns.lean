import Lax461425.FormulasForPatterns
import Lax461425Proofs.SymVFPatternFormulaTree
import Lax461425Proofs.SymVFSumOrbit
import Lax461425Proofs.PatternFormulaSymmetry

/-!
Symmetric formulas for homomorphism polynomials of patterns of bounded treedepth. The
formula along an elimination forest is matrix-symmetric: a row and column permutation acts on
the assignments, which permutes the summands of every sum gate. Every sum gate multiplies the
orbit bound by `n`, and the tagged products do not increase it, so all gate orbits have size
at most `n ^ t`.
-/

namespace Lax461425Proofs.SymVFFormulasForPatterns

open Lax461425.Circuits Lax461425.CircuitProperties Lax461425.MatrixSymmetry
open Lax461425.SymmetricFamilies Lax461425.HomomorphismPolynomials Lax461425.PatternWidths
open Lax183560.AncestorForest
open TreeFormulaCircuit TreeFormulaOperations TreeFormulaIsomorphism ComputedFormula
open SymVFTreeSum SymVFPatternFormula
open scoped Classical

noncomputable section

variable {F : Pattern} {n : ℕ} (fo : AncestorForest (Vx F)) (K : Type*) [Field K]

local notation "anc" => fo.ancestor
local notation "ρ" => Lax461425.SymmetricVNP.matrixAction n

/-! ### Orbits -/

theorem orbit_leaf (x : Fin n × Fin n) :
    Lax461425.SymmetricVNP.orbitSize ρ (circuit (leaf K x).tree) ≤ 1 := by
  change Lax461425.SymmetricVNP.orbitSize ρ
    (circuit (join (fun _ : Unit => (var (K := K) x).tree) true)) ≤ 1
  apply TreeFormulaOrbit.join_orbitSize_le _ true ρ 1 le_rfl
  · intro j
    refine (CircuitFamilyFacts.orbitSize_le_card ρ _).trans ?_
    change Fintype.card Unit ≤ 1
    simp
  · intro γ τ hτ j
    obtain ⟨j', hj'⟩ := SymVFSumOrbit.maps_child_root _ true hτ j
    cases j; cases j'
    exact hj'

theorem Q_root_noninput (k : ℕ) (v : Vx F) (h : Vx F → Fin n) :
    ¬ ((Q fo K k v h).tree.label (Q fo K k v h).tree.out).IsInput := by
  cases k <;> exact id

theorem leaf_root_noninput (x : Fin n × Fin n) :
    ¬ ((leaf K x).tree.label (leaf K x).tree.out).IsInput := id

theorem blk_root_noninput (k : ℕ) (v : Vx F) (g : Vx F → Fin n)
    (j : EO fo v ⊕ KidT fo (some v)) :
    ¬ ((blk fo K (Q fo K k) v g j).tree.label (blk fo K (Q fo K k) v g j).tree.out).IsInput := by
  cases j with
  | inl e => exact leaf_root_noninput K _
  | inr c => exact Q_root_noninput fo K k c.1 g

theorem key_fst (lvl : ℕ) (v : Vx F) (j : EO fo v ⊕ KidT fo (some v)) :
    (key fo lvl v j).1 = lvl := by
  cases j <;> rfl

variable [CharZero K]

theorem goodTags_P (k : ℕ) (v : Vx F) (g : Vx F → Fin n) :
    FormulaTags.GoodTags (blk fo K (Q fo K k) v g) (fun j => tg K (key fo (k + 1) v j)) where
  nonzero j := tg_ne_zero K _
  fresh i j hc := by
    cases j with
    | inl e => exact not_mem_constants_leaf K _ _ hc
    | inr c =>
      exact tg_not_low K (k := k) (by rw [key_fst]; omega) (constants_Q fo K k c.1 g _ hc)
  inverse_fresh i j hc := by
    cases j with
    | inl e => exact not_mem_constants_leaf K _ _ hc
    | inr c =>
      exact tg_inv_not_low K (k := k) (by rw [key_fst]; omega) (constants_Q fo K k c.1 g _ hc)
  injective := (tg_injective K).comp (key_injective fo _ v)
  inverse_ne_tag i j := tg_inv_ne K _ _

theorem orbit_Q (hn : 1 ≤ n) (k : ℕ) : ∀ (v : Vx F) (h : Vx F → Fin n),
    Lax461425.SymmetricVNP.orbitSize ρ (circuit (Q fo K k v h).tree) ≤ n ^ k := by
  induction k with
  | zero =>
    intro v h
    refine (CircuitFamilyFacts.orbitSize_le_card ρ _).trans ?_
    change Fintype.card (Unit ⊕ (Σ e : Empty, _)) ≤ 1
    apply Fintype.card_le_one_iff.mpr
    intro a b
    rcases a with a | ⟨e, _⟩
    · rcases b with b | ⟨e', _⟩
      · rfl
      · exact e'.elim
    · exact e.elim
  | succ k ih =>
    intro v h
    have hB : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn
    have hP : ∀ g : Vx F → Fin n, Lax461425.SymmetricVNP.orbitSize ρ
        (circuit (P fo K (Q fo K k) (k + 1) v g).tree) ≤ n ^ k := by
      intro g
      apply FormulaTags.orbit_bound ρ (blk fo K (Q fo K k) v g) _ (goodTags_P fo K k v g) true
        (n ^ k) hB
      intro j
      apply ComputedFormulaOrbit.tag_orbitSize_le ρ _ _ (blk_root_noninput fo K k v g j) _ hB
      cases j with
      | inl e => exact (orbit_leaf K _).trans hB
      | inr c => exact ih c.1 g
    change Lax461425.SymmetricVNP.orbitSize ρ (circuit (join (fun i : Fin n =>
      (P fo K (Q fo K k) (k + 1) v (Function.update h v i)).tree) false)) ≤ n ^ (k + 1)
    refine (SymVFSumOrbit.join_orbitSize_le_card_mul ρ _ false (n ^ k) (by simpa using hn) hB
      (fun i => hP _)).trans ?_
    simp [pow_succ, mul_comm]

theorem keyTop_injective (t : ℕ) : Function.Injective (keyTop fo t) := by
  intro r r' h
  simp only [keyTop, Prod.mk.injEq, Sum.inr.injEq, true_and] at h
  exact Subtype.ext (ι_injective h)

theorem goodTags_top (t : ℕ) (h₀ : Vx F → Fin n) :
    FormulaTags.GoodTags (fun r : KidT fo none => Q fo K t r.1 h₀)
      (fun r => tg K (keyTop fo t r)) where
  nonzero r := tg_ne_zero K _
  fresh i j hc := tg_not_low K (k := t) (by simp [keyTop]) (constants_Q fo K t _ h₀ _ hc)
  inverse_fresh i j hc :=
    tg_inv_not_low K (k := t) (by simp [keyTop]) (constants_Q fo K t _ h₀ _ hc)
  injective := (tg_injective K).comp (keyTop_injective fo t)
  inverse_ne_tag i j := tg_inv_ne K _ _

theorem orbit_top (hn : 1 ≤ n) (t : ℕ) (h₀ : Vx F → Fin n) :
    Lax461425.SymmetricVNP.orbitSize ρ (circuit (top fo K t h₀).tree) ≤ n ^ t := by
  have hB : 1 ≤ n ^ t := Nat.one_le_pow _ _ hn
  apply FormulaTags.orbit_bound ρ (fun r : KidT fo none => Q fo K t r.1 h₀) _
    (goodTags_top fo K t h₀) true (n ^ t) hB
  intro r
  exact ComputedFormulaOrbit.tag_orbitSize_le ρ _ _ (Q_root_noninput fo K t r.1 h₀) _ hB
    (orbit_Q fo K hn t r.1 h₀)

/-! ### Symmetry -/

omit [CharZero K] in
/-- A variable leaf transforms into the leaf of the image variable. -/
noncomputable def leafIso (γ : Γ n) (x : Fin n × Fin n) :
    Iso (actVar γ) (leaf K x).tree (leaf K (actVar γ x)).tree :=
  joinIso _ (fun _ : Unit => (var (K := K) x).tree)
    (fun _ : Unit => (var (K := K) (actVar γ x)).tree) (Equiv.refl Unit)
    (fun _ => varIso _ x) true

omit [CharZero K] in
theorem iso_Q (γ : Γ n) (k : ℕ) : ∀ (v : Vx F) (h : Vx F → Fin n),
    Nonempty (Iso (actVar γ) (Q fo K k v h).tree (Q fo K k v (act γ h)).tree) := by
  induction k with
  | zero =>
    intro v h
    exact ⟨joinIso _ (fun e : Empty => (e.elim : Formula (Fin n × Fin n) K).tree)
      (fun e : Empty => (e.elim : Formula (Fin n × Fin n) K).tree) (Equiv.refl Empty)
      (fun e => e.elim) false⟩
  | succ k ih =>
    intro v h
    have hblk : ∀ (g : Vx F → Fin n) (j : EO fo v ⊕ KidT fo (some v)),
        Nonempty (Iso (actVar γ) (blk fo K (Q fo K k) v g j).tree
          (blk fo K (Q fo K k) v (act γ g) j).tree) := by
      intro g j
      cases j with
      | inl e =>
        have hm : mm F e.1.1 v ≠ 0 := by
          have := e.2.isLt
          omega
        simp only [blk]
        rw [ev_act γ g hm]
        exact ⟨leafIso K γ _⟩
      | inr c => exact ih c.1 g
    have hP : ∀ g : Vx F → Fin n, Nonempty (Iso (actVar γ)
        (P fo K (Q fo K k) (k + 1) v g).tree (P fo K (Q fo K k) (k + 1) v (act γ g)).tree) :=
      fun g => ⟨joinIso _ _ _ (Equiv.refl _)
        (fun j => PatternFormulaSymmetry.tagIso _ _ _ _ (Classical.choice (hblk g j))) true⟩
    have hP' : ∀ i : Fin n, Nonempty (Iso (actVar γ)
        (P fo K (Q fo K k) (k + 1) v (Function.update h v i)).tree
        (P fo K (Q fo K k) (k + 1) v (Function.update (act γ h) v (sidePerm γ v i))).tree) := by
      intro i
      rw [← act_update]
      exact hP _
    exact ⟨joinIso _ (fun i => (P fo K (Q fo K k) (k + 1) v (Function.update h v i)).tree)
      (fun i => (P fo K (Q fo K k) (k + 1) v (Function.update (act γ h) v i)).tree)
      (sidePerm γ v) (fun i => Classical.choice (hP' i)) false⟩

omit [CharZero K] in
theorem iso_top (γ : Γ n) (t : ℕ) (h₀ : Vx F → Fin n) :
    Nonempty (Iso (actVar γ) (top fo K t h₀).tree (top fo K t h₀).tree) := by
  have hr : ∀ r : KidT fo none,
      Nonempty (Iso (actVar γ) (Q fo K t r.1 h₀).tree (Q fo K t r.1 h₀).tree) := by
    intro r
    have he : Q fo K t r.1 (act γ h₀) = Q fo K t r.1 h₀ :=
      Q_congr fo K t r.1 _ _ (fun u hu => (r.2.2 u trivial hu).elim)
    have := iso_Q fo K γ t r.1 h₀
    rw [he] at this
    exact this
  exact ⟨joinIso _ _ _ (Equiv.refl _)
    (fun r => PatternFormulaSymmetry.tagIso _ _ _ _ (Classical.choice (hr r))) true⟩

/-! ### Polynomial -/

theorem polynomial_top (t : ℕ) (rank : Vx F → ℕ) (hrank : ∀ u v, anc u v → rank u < rank v)
    (hlt : ∀ v, rank v < t) (hclos : ∀ ⦃u v : Vx F⦄, (underlying F).Adj u v → anc u v ∨ anc v u)
    (h₀ : Vx F → Fin n) :
    polynomial (top fo K t h₀) = hom K F n := by
  simp only [top, polynomial_op, if_true]
  simp_rw [polynomial_tag _ (tg_ne_zero K _) _]
  rw [hom_eq_sm fo K hclos h₀, sm_sdesc fo K rank hrank]
  apply Finset.prod_congr rfl
  intro r _
  exact polynomial_Q fo K t rank hrank hlt t r.1 h₀ (by omega)

end

/--
---
conclusion: Lax461425.FormulasForPatterns.exists_formula
---
The homomorphism polynomial of a pattern of treedepth at most `t` has a matrix-symmetric
formula of orbit size at most `n ^ t ≤ n ^ (t + 2)`: sum gates over the values of the vertices
of an elimination forest, with tagged products of edge variables and child formulas.
-/
theorem exists_formula {K : Type*} [Field K] [CharZero K] {n t : ℕ} (hn : 1 ≤ n)
    (F : Pattern) (hF : TreedepthLE t F) :
    ∃ C : Circuit (Fin n × Fin n) K,
      C.Computes (hom K F n) ∧ IsFormula C ∧ IsMatrixSymmetric C ∧ orbitSize C ≤ n ^ (t + 2) := by
  obtain ⟨fo, hclos, rank, hrank⟩ := hF
  let h₀ : Vx F → Fin n := fun _ => ⟨0, hn⟩
  let G := top fo K t h₀
  refine ⟨circuit G.tree, ?_, ComputedFormula.isFormula G, ?_, ?_⟩
  · rw [← polynomial_top fo K t (fun v => (rank v : ℕ)) (fun u v h => hrank h)
      (fun v => (rank v).isLt) hclos h₀]
    exact ComputedFormula.computes G
  · intro γ
    let e := Classical.choice (iso_top fo K γ t h₀)
    exact ⟨e.equiv, TreeFormulaIsomorphism.extends_circuit e⟩
  · have h := orbit_top fo K hn t h₀
    have hle : n ^ t ≤ n ^ (t + 2) := Nat.pow_le_pow_right hn (by omega)
    exact h.trans hle

end Lax461425Proofs.SymVFFormulasForPatterns
