import Lax461425Proofs.PathRefinementDecomposition
import Lax461425Proofs.PathRefinementNewRoot
import Lax461425Proofs.PatternsLabelledGlue
import Lax461425Proofs.PatternsRestrictedMono

/-!
The existing labelled-pattern spans, refined by a linear certificate for the decomposition
tree. Depth-one terms are already linear. Gluing such a term to a linear term preserves
linearity: the old gluing construction merely attaches leaves to the old root.
-/

namespace Lax461425Proofs.PathRefinementClass

open PatternsLabelledBasic PatternsLabelledOps PatternsLabelledGlue PatternsRestrictedMono
open PathRefinementDecomposition PathRefinementSchedule
open scoped Classical

noncomputable section

variable {ℓ r Δ k : ℕ} {G : LabelledPattern ℓ r}
variable {P : Finset (Fin ℓ ⊕ Fin r)}

def InLinearClassP (Δ k : ℕ) (P : Finset (Fin ℓ ⊕ Fin r)) (G : LabelledPattern ℓ r) : Prop :=
  Nonempty (LinearDecomposition G Δ k) ∧
    G.labelSupport ⊆ Finset.univ.image (fun p : P => G.labelVertex p)

def spanLinear (K : Type*) [Field K] (Δ k n : ℕ) (P : Finset (Fin ℓ ⊕ Fin r)) :
    Submodule K ((Fin ℓ → Fin n) → (Fin r → Fin n) → MvPolynomial (Fin n × Fin n) K) :=
  Submodule.span K {f | ∃ G : LabelledPattern ℓ r,
    InLinearClassP Δ k P G ∧ labelledHom K G n = f}

theorem forget (h : InLinearClassP Δ k (ℓ := ℓ) (r := r) P G) : InClassP Δ k P G :=
  ⟨h.1.elim (fun D => ⟨D.tree⟩), h.2⟩

def monoLinear {Δ' : ℕ} (hle : Δ ≤ Δ') (D : LinearDecomposition G Δ k) :
    LinearDecomposition G Δ' k where
  tree := monoDecomposition hle D.tree
  schedule := D.schedule

theorem mono_class {Δ' : ℕ} (hle : Δ ≤ Δ')
    (h : InLinearClassP Δ k (ℓ := ℓ) (r := r) P G) : InLinearClassP Δ' k P G := by
  obtain ⟨D⟩ := h.1
  exact ⟨⟨monoLinear hle D⟩, h.2⟩

theorem span_forget {K : Type*} [Field K] {n : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)} :
    spanLinear K Δ k n P ≤ span𝔗P K Δ k n P := by
  apply Submodule.span_mono
  rintro f ⟨G, hG, rfl⟩
  exact ⟨G, forget hG, rfl⟩

theorem span_mono {K : Type*} [Field K] {n Δ' : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)}
    (hle : Δ ≤ Δ') : spanLinear K Δ k n P ≤ spanLinear K Δ' k n P := by
  apply Submodule.span_mono
  rintro f ⟨G, hG, rfl⟩
  exact ⟨G, mono_class hle hG, rfl⟩

theorem parent_eq_root_of_depth_le_one (D : RootExactDecomposition G Δ k) (hΔ : Δ ≤ 1) :
    ∀ t, D.parent t = D.root := by
  intro t
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hΔ with h | h
  · subst Δ
    have ht : t = D.root := D.depth_le t
    rw [ht, D.parent_root]
  · subst Δ
    exact D.depth_le t

def starLinear (D : RootExactDecomposition G Δ k) (hΔ : Δ ≤ 1) :
    LinearDecomposition G Δ k where
  tree := D
  schedule := star D.parent D.root (parent_eq_root_of_depth_le_one D hΔ)

theorem star_class (hΔ : Δ ≤ 1) (h : InClassP Δ k (ℓ := ℓ) (r := r) P G) :
    InLinearClassP Δ k P G := by
  obtain ⟨D⟩ := h.1
  exact ⟨⟨starLinear D hΔ⟩, h.2⟩

/-- Every depth-one (or depth-zero) term in Tim's existing span already has a linear certificate. -/
theorem star_span {K : Type*} [Field K] {n : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)}
    (hΔ : Δ ≤ 1) : span𝔗P K Δ k n P ≤ spanLinear K Δ k n P := by
  apply Submodule.span_mono
  rintro f ⟨G, hG, rfl⟩
  exact ⟨G, star_class hΔ hG, rfl⟩

def glueLinear {G' : LabelledPattern ℓ r} {P : Finset (Fin ℓ ⊕ Fin r)}
    (hP : P.card ≤ k) (D : LinearDecomposition G Δ k) (D' : RootExactDecomposition G' Δ k)
    (hs : ∀ t, D'.parent t = D'.root)
    (hG : InClassP Δ k P G) (hG' : InClassP Δ k P G') :
    LinearDecomposition (glue G G') Δ k where
  tree := glueDecomposition G G' hP D.tree D' hG hG'
  schedule := by
    change Schedule (glueParent G G' D.tree D') (glueRoot G G' D.tree D')
    have hp : glueParent G G' D.tree D' =
        leafParent (B := {t : D'.Node // t ≠ D'.root})
          (parent := D.tree.parent) (root := D.tree.root) := by
      funext t
      cases t with
      | inl a => rfl
      | inr b => simp [glueParent, leafParent, hs]
    rw [hp]
    exact leaves D.schedule

/-- One arbitrary linear factor may be multiplied by a star factor. -/
theorem class_mul_star {G' : LabelledPattern ℓ r} {δ : ℕ} {P : Finset (Fin ℓ ⊕ Fin r)}
    (hP : P.card ≤ k) (hδ : δ ≤ 1) (hle : δ ≤ Δ)
    (hG : InLinearClassP Δ k P G) (hG' : InClassP δ k P G') :
    InLinearClassP Δ k P (glue G G') := by
  obtain ⟨D⟩ := hG.1
  obtain ⟨D'⟩ := hG'.1
  have hG₀ := forget hG
  have hG'₀ := mono_inClassP hle hG'
  refine ⟨⟨glueLinear hP D (monoDecomposition hle D') ?_ hG₀ hG'₀⟩,
    labelSupport_glue_subset G G' hG₀ hG'₀⟩
  exact parent_eq_root_of_depth_le_one D' hδ

end

end Lax461425Proofs.PathRefinementClass
