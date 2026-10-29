import Lax461425.MatrixSymmetry
import Lax461425Proofs.ConverseGates

/-!
Matrix symmetry of the circuit built in `ConverseGates.lean`: for every `π : Γ n`, relabelling
every admissible map `γ` (on any bag) by `π` (acting coordinatewise as rows on left/`A`-points
and columns on right/`B`-points), relabelling the input gate `inp i j` to `inp (π.1 i) (π.2 j)`,
and leaving the node/non-root-node parameters `t`, `c` untouched, gives a circuit automorphism
extending `actVar π`. This uses only the structure of the gates and wires, not correctness.
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.HomomorphismPolynomials Lax461425.Forestwidth
open Lax461425.MatrixSymmetry

variable {F : Pattern} {Δ k : ℕ}

section Symmetry

variable (N : NormDecomp F Δ k) (n : ℕ)

/-- The coordinate on which `Γₙ` acts at a point `v : F.A ⊕ F.B`: via the row-permutation
`π.1` if `v` is a left/`A`-point, via the column-permutation `π.2` if `v` is a right/`B`-point.
-/
def actCoord (π : Γ n) : (F.A ⊕ F.B) → Fin n → Fin n
  | Sum.inl _, y => π.1 y
  | Sum.inr _, y => π.2 y

theorem actCoord_injective (π : Γ n) (v : F.A ⊕ F.B) : Function.Injective (actCoord n π v) := by
  cases v with
  | inl a => exact π.1.injective
  | inr b => exact π.2.injective

theorem actCoord_symm_apply (π : Γ n) (v : F.A ⊕ F.B) (y : Fin n) :
    actCoord n (π.1.symm, π.2.symm) v (actCoord n π v y) = y := by
  cases v with
  | inl a => exact π.1.symm_apply_apply y
  | inr b => exact π.2.symm_apply_apply y

theorem actCoord_apply_symm (π : Γ n) (v : F.A ⊕ F.B) (y : Fin n) :
    actCoord n π v (actCoord n (π.1.symm, π.2.symm) v y) = y := by
  cases v with
  | inl a => exact π.1.apply_symm_apply y
  | inr b => exact π.2.apply_symm_apply y

/-- The action of `Γₙ` on admissible maps: relabel the value at each point according to
whether it names a row- or a column-coordinate. -/
def actAdm (π : Γ n) {S : Finset (F.A ⊕ F.B)} (γ : Adm F n S) : Adm F n S :=
  fun x => actCoord n π x.1 (γ x)

theorem actAdm_symm_apply (π : Γ n) {S : Finset (F.A ⊕ F.B)} (γ : Adm F n S) :
    actAdm n (π.1.symm, π.2.symm) (actAdm n π γ) = γ := by
  funext x
  exact actCoord_symm_apply n π x.1 (γ x)

theorem actAdm_apply_symm (π : Γ n) {S : Finset (F.A ⊕ F.B)} (γ : Adm F n S) :
    actAdm n π (actAdm n (π.1.symm, π.2.symm) γ) = γ := by
  funext x
  exact actCoord_apply_symm n π x.1 (γ x)

/-- The action of `Γₙ` on gates: relabel admissible maps on `R`/`S`-gates, and relabel the
indices of input gates, while leaving the node/non-root-node parameter unchanged. -/
def actGate (π : Γ n) : CGate N n → CGate N n
  | .R t γ => .R t (actAdm n π γ)
  | .S c δ => .S c (actAdm n π δ)
  | .inp i j => .inp (π.1 i) (π.2 j)

theorem actGate_symm_apply (π : Γ n) (g : CGate N n) :
    actGate N n (π.1.symm, π.2.symm) (actGate N n π g) = g := by
  cases g with
  | R t γ => show CGate.R t (actAdm n (π.1.symm, π.2.symm) (actAdm n π γ)) = CGate.R t γ
             rw [actAdm_symm_apply]
  | S c δ => show CGate.S c (actAdm n (π.1.symm, π.2.symm) (actAdm n π δ)) = CGate.S c δ
             rw [actAdm_symm_apply]
  | inp i j => show CGate.inp (π.1.symm (π.1 i)) (π.2.symm (π.2 j)) = CGate.inp i j
               rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem actGate_apply_symm (π : Γ n) (g : CGate N n) :
    actGate N n π (actGate N n (π.1.symm, π.2.symm) g) = g := by
  cases g with
  | R t γ => show CGate.R t (actAdm n π (actAdm n (π.1.symm, π.2.symm) γ)) = CGate.R t γ
             rw [actAdm_apply_symm]
  | S c δ => show CGate.S c (actAdm n π (actAdm n (π.1.symm, π.2.symm) δ)) = CGate.S c δ
             rw [actAdm_apply_symm]
  | inp i j => show CGate.inp (π.1 (π.1.symm i)) (π.2 (π.2.symm j)) = CGate.inp i j
               rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- `actGate N n π` is a bijection of the gates, with inverse `actGate N n π⁻¹`. -/
noncomputable def actGateEquiv (π : Γ n) : CGate N n ≃ CGate N n where
  toFun := actGate N n π
  invFun := actGate N n (π.1.symm, π.2.symm)
  left_inv := actGate_symm_apply N n π
  right_inv := actGate_apply_symm N n π

theorem actGate_label {K : Type*} (π : Γ n) (g : CGate N n) :
    CGate.label (N := N) (n := n) (K := K) (actGate N n π g)
      = (CGate.label (N := N) (n := n) (K := K) g).map (actVar π) := by
  cases g with
  | R t γ => rfl
  | S c δ => rfl
  | inp i j => rfl

/-- The action of `Γₙ` on gates preserves all wire multiplicities. -/
theorem actGate_wire (π : Γ n) (g h : CGate N n) :
    wire N n (actGate N n π g) (actGate N n π h) = wire N n g h := by
  cases g with
  | R t γ =>
    cases h with
    | R t' γ' => simp [wire, actGate]
    | S c δ =>
        show wireRtoS N n t (actAdm n π γ) c (actAdm n π δ) = wireRtoS N n t γ c δ
        unfold wireRtoS
        by_cases hpar : N.parent c.1 = t
        · rw [dif_pos hpar, dif_pos hpar]
          have hiff : (∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
              actAdm n π γ ⟨x, hpar ▸ Finset.inter_subset_left hx⟩ = actAdm n π δ ⟨x, hx⟩) ↔
              (∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
                γ ⟨x, hpar ▸ Finset.inter_subset_left hx⟩ = δ ⟨x, hx⟩) := by
            constructor
            · intro hm x hx
              exact actCoord_injective n π x (hm x hx)
            · intro hm x hx
              show actCoord n π x (γ ⟨x, hpar ▸ Finset.inter_subset_left hx⟩)
                  = actCoord n π x (δ ⟨x, hx⟩)
              rw [hm x hx]
          by_cases horg : ∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
              γ ⟨x, hpar ▸ Finset.inter_subset_left hx⟩ = δ ⟨x, hx⟩
          · rw [if_pos horg, if_pos (hiff.mpr horg)]
          · rw [if_neg horg, if_neg (fun hc => horg (hiff.mp hc))]
        · rw [dif_neg hpar, dif_neg hpar]
    | inp i j =>
        show wireRtoInp N n t (actAdm n π γ) (π.1 i) (π.2 j) = wireRtoInp N n t γ i j
        unfold wireRtoInp
        refine Finset.sum_congr rfl (fun ab _ => ?_)
        have hiff : (actAdm n π γ ⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩ = π.1 i ∧
            actAdm n π γ ⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩ = π.2 j) ↔
            (γ ⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩ = i ∧
              γ ⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩ = j) := by
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨actCoord_injective n π _ h1, actCoord_injective n π _ h2⟩
          · rintro ⟨h1, h2⟩
            refine ⟨?_, ?_⟩
            · simp [actAdm, actCoord, h1]
            · simp [actAdm, actCoord, h2]
        by_cases horg : γ ⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩ = i ∧
            γ ⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩ = j
        · rw [if_pos horg, if_pos (hiff.mpr horg)]
        · rw [if_neg horg, if_neg (fun hc => horg (hiff.mp hc))]
  | S c δ =>
    cases h with
    | R t γ =>
        show wireStoR N n c (actAdm n π δ) t (actAdm n π γ) = wireStoR N n c δ t γ
        unfold wireStoR
        by_cases heq : c.1 = t
        · rw [dif_pos heq, dif_pos heq]
          have hiff : (∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
              actAdm n π γ ⟨x, heq ▸ Finset.inter_subset_right hx⟩ = actAdm n π δ ⟨x, hx⟩) ↔
              (∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
                γ ⟨x, heq ▸ Finset.inter_subset_right hx⟩ = δ ⟨x, hx⟩) := by
            constructor
            · intro hm x hx
              exact actCoord_injective n π x (hm x hx)
            · intro hm x hx
              show actCoord n π x (γ ⟨x, heq ▸ Finset.inter_subset_right hx⟩)
                  = actCoord n π x (δ ⟨x, hx⟩)
              rw [hm x hx]
          by_cases horg : ∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
              γ ⟨x, heq ▸ Finset.inter_subset_right hx⟩ = δ ⟨x, hx⟩
          · rw [if_pos horg, if_pos (hiff.mpr horg)]
          · rw [if_neg horg, if_neg (fun hc => horg (hiff.mp hc))]
        · rw [dif_neg heq, dif_neg heq]
    | S c' δ' => simp [wire, actGate]
    | inp i j => simp [wire, actGate]
  | inp i j => cases h <;> simp [wire, actGate]

/-- **Item B.** The constructed circuit is matrix-symmetric: every `π : Γₙ` extends to the
circuit automorphism `actGateEquiv N n π`. -/
theorem isMatrixSymmetric_circuit {K : Type*} (hn0 : 0 < n) (hE : ∃ a b, F.mult a b ≠ 0) :
    IsMatrixSymmetric (circuit N n K hn0 hE) :=
  fun π => ⟨actGateEquiv N n π, actGate_label N n π, actGate_wire N n π⟩

end Symmetry

end Lax461425Proofs
