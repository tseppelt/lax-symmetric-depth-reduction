import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Lax461425.Supports

/-!
Rigidity turns `Γₙ` into an actual group acting on the gates of a rigid circuit `C`, and also
registers the (already implicit) action of `Γₙ` on `[n] ⊎ [n]` via `actPoint` as a genuine
`MulAction` instance, so that `fixingSubgroup` and friends apply to it directly.

This is the first layer needed to turn the abstract, quantifier-heavy definitions in
`Lax461425.Supports` into something a later induction can compute with.
-/

namespace Lax461425Proofs.PatternsSupportAction

open Lax461425.Circuits Lax461425.MatrixSymmetry

variable {V K : Type*}

/-- Labels are fixed by the identity renaming. -/
theorem label_map_id (l : GateLabel V K) : l.map id = l := by
  cases l <;> rfl

/-- Renaming is functorial: renaming along `π₂` and then `π₁` is the same as renaming along the
composite `π₁ ∘ π₂`. -/
theorem label_map_map (π₁ π₂ : V → V) (l : GateLabel V K) :
    (l.map π₂).map π₁ = l.map (π₁ ∘ π₂) := by
  cases l <;> rfl

variable {C : Circuit V K}

/-- A circuit automorphism extending the identity renaming always exists: the identity
automorphism. -/
theorem extends_one : Extends C 1 (id : V → V) := by
  refine ⟨fun g => ?_, fun g h => ?_⟩
  · show C.label g = (C.label g).map id
    rw [label_map_id]
  · show C.wire g h = C.wire g h
    rfl

/-- Extending composes: if `σ₁` extends `π₁` and `σ₂` extends `π₂`, then `σ₁ * σ₂` (apply `σ₂`
first, then `σ₁`, matching `Equiv.Perm`'s multiplication convention) extends `π₁ ∘ π₂`. -/
theorem extends_comp {σ₁ σ₂ : C.Gate ≃ C.Gate} {π₁ π₂ : V → V}
    (h₁ : Extends C σ₁ π₁) (h₂ : Extends C σ₂ π₂) : Extends C (σ₁ * σ₂) (π₁ ∘ π₂) := by
  refine ⟨fun g => ?_, fun g h => ?_⟩
  · show C.label (σ₁ (σ₂ g)) = (C.label g).map (π₁ ∘ π₂)
    rw [h₁.1 (σ₂ g), h₂.1 g, label_map_map]
  · show C.wire (σ₁ (σ₂ g)) (σ₁ (σ₂ h)) = C.wire g h
    rw [h₁.2 (σ₂ g) (σ₂ h), h₂.2 g h]

variable {n : ℕ}

/-- `actVar` sends the identity of `Γₙ` to the identity renaming. -/
theorem actVar_one : actVar (1 : Γ n) = id := by
  funext x
  simp [actVar]

/-- `actVar` is a monoid homomorphism `Γₙ → Function.End (Fin n × Fin n)` for the composition
convention `actVar (γ₁ * γ₂) = actVar γ₁ ∘ actVar γ₂`. -/
theorem actVar_mul (γ₁ γ₂ : Γ n) : actVar (γ₁ * γ₂) = actVar γ₁ ∘ actVar γ₂ := by
  funext x
  simp [actVar, Equiv.Perm.mul_apply]

/-- `actPoint` sends the identity of `Γₙ` to the identity map. -/
theorem actPoint_one : actPoint (1 : Γ n) = id := by
  funext x
  cases x <;> simp [actPoint]

/-- `actPoint` is a monoid homomorphism `Γₙ → Function.End (Fin n ⊕ Fin n)` for the same
composition convention as `actVar`. -/
theorem actPoint_mul (γ₁ γ₂ : Γ n) : actPoint (γ₁ * γ₂) = actPoint γ₁ ∘ actPoint γ₂ := by
  funext x
  cases x <;> simp [actPoint, Equiv.Perm.mul_apply]

/-- The (genuine, unconditional) action of `Γₙ` on `[n] ⊎ [n]` by `actPoint`. -/
instance instMulActionPoint (n : ℕ) : MulAction (Γ n) (Fin n ⊕ Fin n) where
  smul γ x := actPoint γ x
  one_smul x := congrFun actPoint_one x
  mul_smul γ₁ γ₂ x := congrFun (actPoint_mul γ₁ γ₂) x

/-- Unfolding `•` for the `Γₙ`-action on `[n] ⊎ [n]`. -/
theorem smul_point_def (γ : Γ n) (x : Fin n ⊕ Fin n) : γ • x = actPoint γ x := rfl

variable {C : Circuit (Fin n × Fin n) K}

/-- `σOf hrig γ` is *the* circuit automorphism extending `γ`, obtained from rigidity. -/
noncomputable def σOf (hrig : IsRigid C) (γ : Γ n) : C.Gate ≃ C.Gate :=
  (hrig γ).choose

/-- `σOf hrig γ` extends `γ`. -/
theorem σOf_extends (hrig : IsRigid C) (γ : Γ n) : Extends C (σOf hrig γ) (actVar γ) :=
  (hrig γ).choose_spec.1

/-- `σOf hrig γ` is the *unique* automorphism extending `γ`. -/
theorem σOf_unique (hrig : IsRigid C) {γ : Γ n} {σ : C.Gate ≃ C.Gate}
    (h : Extends C σ (actVar γ)) : σ = σOf hrig γ :=
  (hrig γ).choose_spec.2 σ h

/-- `σOf hrig` sends `1` to `1`. -/
theorem σOf_one (hrig : IsRigid C) : σOf hrig (1 : Γ n) = 1 := by
  refine (σOf_unique hrig ?_).symm
  rw [actVar_one]
  exact extends_one

/-- `σOf hrig` is a monoid homomorphism `Γₙ → Equiv.Perm C.Gate`. -/
theorem σOf_mul (hrig : IsRigid C) (γ₁ γ₂ : Γ n) :
    σOf hrig (γ₁ * γ₂) = σOf hrig γ₁ * σOf hrig γ₂ := by
  refine (σOf_unique hrig ?_).symm
  rw [actVar_mul]
  exact extends_comp (σOf_extends hrig γ₁) (σOf_extends hrig γ₂)

/-- `σOf hrig` packaged as a monoid homomorphism. -/
noncomputable def σOfHom (hrig : IsRigid C) : Γ n →* Equiv.Perm C.Gate where
  toFun := σOf hrig
  map_one' := σOf_one hrig
  map_mul' := σOf_mul hrig

/-- Rigidity turns `Γₙ` into a genuine group acting on the gates of `C`, via `σOf`. -/
noncomputable def gateMulAction (hrig : IsRigid C) : MulAction (Γ n) C.Gate where
  smul γ g := σOf hrig γ g
  one_smul g := by show σOf hrig 1 g = g; rw [σOf_one]; rfl
  mul_smul γ₁ γ₂ g := by
    show σOf hrig (γ₁ * γ₂) g = σOf hrig γ₁ (σOf hrig γ₂ g)
    rw [σOf_mul]; rfl

/-- Unfolding `•` for `gateMulAction`. -/
theorem gateMulAction_smul_def (hrig : IsRigid C) (γ : Γ n) (g : C.Gate) :
    letI := gateMulAction hrig
    γ • g = σOf hrig γ g :=
  rfl

end Lax461425Proofs.PatternsSupportAction
