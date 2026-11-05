import Lax461425Proofs.SymVFPatternFormula
import Lax461425Proofs.FormulaTags

/-!
The tagged formulas along an elimination forest, the polynomials they compute, their
constants, and their independence of the values outside the ancestors.
-/

namespace Lax461425Proofs.SymVFPatternFormula

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open Lax461425.HomomorphismPolynomials Lax183560.AncestorForest
open TreeFormulaCircuit TreeFormulaOperations ComputedFormula SymVFTreeSum
open scoped Classical

noncomputable section

variable {F : Pattern} {n : ℕ} (fo : AncestorForest (Vx F)) (K : Type*) [Field K]

local notation "anc" => fo.ancestor

/-- Keys of tags: level, vertex, and the factor. -/
abbrev TagKey := ℕ × ℕ × (ℕ × ℕ ⊕ ℕ)

/-- Tag constants, pairwise distinct with all inverses distinct from all tags. -/
def tg (x : TagKey) : K := ((Encodable.encode x + 2 : ℕ) : K)

/-- An injective numbering of the vertices. -/
def ι (v : Vx F) : ℕ := (Fintype.equivFin (Vx F) v : ℕ)

theorem ι_injective : Function.Injective (ι (F := F)) :=
  Fin.val_injective.comp (Fintype.equivFin (Vx F)).injective

/-- The key of a factor of the product at `v`. -/
def key (lvl : ℕ) (v : Vx F) : EO fo v ⊕ KidT fo (some v) → TagKey
  | .inl e => (lvl, ι v, .inl (ι e.1.1, e.2.val))
  | .inr c => (lvl, ι v, .inr (ι c.1))

theorem key_injective (lvl : ℕ) (v : Vx F) : Function.Injective (key fo lvl v) := by
  intro j j' h
  rcases j with ⟨⟨u, hu⟩, k⟩ | ⟨c, hc⟩ <;> rcases j' with ⟨⟨u', hu'⟩, k'⟩ | ⟨c', hc'⟩ <;>
    simp only [key, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
      false_and] at h
  · obtain ⟨-, -, h1, h2⟩ := h
    have := ι_injective h1
    subst this
    have : k = k' := Fin.ext h2
    subst this
    rfl
  · obtain ⟨-, -, h1⟩ := h
    have := ι_injective h1
    subst this
    rfl

/-- A private variable leaf under a product gate, so the root is not an input. -/
def leaf (x : Fin n × Fin n) : Formula (Fin n × Fin n) K := op true (fun _ : Unit => var x)

/-- The factors of the product at `v`: edge leaves and the formulas of the children. -/
def blk (R : Vx F → (Vx F → Fin n) → Formula (Fin n × Fin n) K) (v : Vx F)
    (g : Vx F → Fin n) : EO fo v ⊕ KidT fo (some v) → Formula (Fin n × Fin n) K
  | .inl e => leaf K (ev g e.1.1 v)
  | .inr c => R c.1 g

/-- The tagged product at `v`. -/
def P (R : Vx F → (Vx F → Fin n) → Formula (Fin n × Fin n) K) (lvl : ℕ) (v : Vx F)
    (g : Vx F → Fin n) : Formula (Fin n × Fin n) K :=
  op true (fun j => tag (tg K (key fo lvl v j)) (blk fo K R v g j))

/-- The formula for the subtree of `v` at level `k`. -/
def Q : ℕ → Vx F → (Vx F → Fin n) → Formula (Fin n × Fin n) K
  | 0, _, _ => op false (fun e : Empty => e.elim)
  | k + 1, v, h => op false (fun i : Fin n => P fo K (Q k) (k + 1) v (Function.update h v i))

/-- The key of a root factor. -/
def keyTop (t : ℕ) (r : KidT fo none) : TagKey := (t + 1, 0, .inr (ι r.1))

/-- The whole formula: the tagged product over the roots. -/
def top (t : ℕ) (h₀ : Vx F → Fin n) : Formula (Fin n × Fin n) K :=
  op true (fun r : KidT fo none => tag (tg K (keyTop fo t r)) (Q fo K t r.1 h₀))

/-! ### Tags -/

variable [CharZero K]

theorem tg_ne_zero (x : TagKey) : tg K x ≠ 0 := by
  unfold tg
  exact Nat.cast_ne_zero.mpr (by omega)

theorem tg_injective : Function.Injective (tg K) := by
  intro x y h
  unfold tg at h
  have h' : Encodable.encode x + 2 = Encodable.encode y + 2 := by exact_mod_cast h
  exact Encodable.encode_injective (by omega)

theorem tg_inv_ne (x y : TagKey) : (tg K x)⁻¹ ≠ tg K y := by
  intro h
  have hx := tg_ne_zero K x
  have h1 : tg K x * tg K y = 1 := by rw [← h, mul_inv_cancel₀ hx]
  unfold tg at h1
  have h2 : (Encodable.encode x + 2) * (Encodable.encode y + 2) = 1 := by exact_mod_cast h1
  have : 2 * 2 ≤ (Encodable.encode x + 2) * (Encodable.encode y + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-! ### Polynomials -/

omit [CharZero K] in
theorem polynomial_leaf (x : Fin n × Fin n) : polynomial (leaf K x) = MvPolynomial.X x := by
  simp [leaf]

theorem polynomial_P (R : Vx F → (Vx F → Fin n) → Formula (Fin n × Fin n) K) (lvl : ℕ)
    (v : Vx F) (g : Vx F → Fin n) :
    polynomial (P fo K R lvl v g) =
      E fo K g v * ∏ c : KidT fo (some v), polynomial (R c.1 g) := by
  simp only [P, polynomial_op, if_true]
  simp_rw [polynomial_tag _ (tg_ne_zero K _) _]
  rw [Fintype.prod_sum_type]
  congr 1
  simp only [blk, polynomial_leaf, Fintype.prod_sigma, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  unfold E
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype (p := fun u => anc u v) _ (fun u => by simp)
    (fun a => MvPolynomial.X (ev g a v) ^ mm F a v)).symm

/-- The formula computes the subtree polynomial once the level is large enough. -/
theorem polynomial_Q (t : ℕ) (rank : Vx F → ℕ) (hrank : ∀ u v, anc u v → rank u < rank v)
    (hlt : ∀ v, rank v < t) (k : ℕ) :
    ∀ v (h : Vx F → Fin n), t ≤ rank v + k → polynomial (Q fo K k v h) = T fo K v h := by
  induction k with
  | zero => intro v h hv; have := hlt v; omega
  | succ k ih =>
    intro v h hv
    rw [T_eq fo K rank hrank]
    simp only [Q, polynomial_op]
    simp only [Bool.false_eq_true, if_false]
    apply Finset.sum_congr rfl
    intro i _
    rw [polynomial_P]
    congr 1
    apply Finset.prod_congr rfl
    intro c _
    apply ih
    have := hrank v c.1 c.2.1
    omega

/-! ### Constants -/

omit [CharZero K] in
theorem mem_constants_iff (G : Formula (Fin n × Fin n) K) (c : K) :
    c ∈ FormulaTags.constants G ↔ ∃ g, G.tree.label g = .const c := by
  constructor
  · intro hc
    obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp hc
    refine ⟨g, ?_⟩
    revert hg
    cases G.tree.label g <;> simp [FormulaTags.labelConstants]
    intro h; rw [h]
  · rintro ⟨g, hg⟩
    exact FormulaTags.mem_constants_of_label G g hg

omit [CharZero K] in
theorem constants_op {I : Type} [Fintype I] (mul : Bool) (G : I → Formula (Fin n × Fin n) K)
    {c : K} (hc : c ∈ FormulaTags.constants (op mul G)) :
    ∃ i, c ∈ FormulaTags.constants (G i) := by
  obtain ⟨g, hg⟩ := (mem_constants_iff K _ c).mp hc
  cases g with
  | inl u => cases mul <;> cases hg
  | inr p => exact ⟨p.1, (mem_constants_iff K _ c).mpr ⟨p.2, hg⟩⟩

omit [CharZero K] in
theorem constants_tag (s : K) (G : Formula (Fin n × Fin n) K) {c : K}
    (hc : c ∈ FormulaTags.constants (tag s G)) :
    c = s⁻¹ ∨ c = s ∨ c ∈ FormulaTags.constants G := by
  obtain ⟨g, hg⟩ := (mem_constants_iff K _ c).mp hc
  exact FormulaTags.tag_constant_cases s G g hg

omit [CharZero K] in
theorem not_mem_constants_leaf (x : Fin n × Fin n) (c : K) :
    c ∉ FormulaTags.constants (leaf K x) := by
  intro hc
  obtain ⟨i, hi⟩ := constants_op K _ _ hc
  obtain ⟨g, hg⟩ := (mem_constants_iff K _ c).mp hi
  cases hg

/-- The constants below level `k`. -/
def Low (k : ℕ) (c : K) : Prop := ∃ x : TagKey, x.1 ≤ k ∧ (c = tg K x ∨ c = (tg K x)⁻¹)

omit [CharZero K] in
theorem constants_Q (k : ℕ) : ∀ v (h : Vx F → Fin n) c,
    c ∈ FormulaTags.constants (Q fo K k v h) → Low K k c := by
  induction k with
  | zero =>
    intro v h c hc
    obtain ⟨i, -⟩ := constants_op K _ _ hc
    exact i.elim
  | succ k ih =>
    intro v h c hc
    obtain ⟨i, hi⟩ := constants_op K _ _ hc
    obtain ⟨j, hj⟩ := constants_op K _ _ hi
    rcases constants_tag K _ _ hj with hc | hc | hc
    · exact ⟨_, by cases j <;> simp [key], Or.inr hc⟩
    · exact ⟨_, by cases j <;> simp [key], Or.inl hc⟩
    · cases j with
      | inl e => exact (not_mem_constants_leaf K _ c hc).elim
      | inr r =>
        obtain ⟨x, hx, hcx⟩ := ih r.1 _ c hc
        exact ⟨x, by omega, hcx⟩

/-- The tags at level `lvl` avoid the constants of lower levels. -/
theorem tg_not_low {k : ℕ} {x : TagKey} (hx : k < x.1) : ¬ Low K k (tg K x) := by
  rintro ⟨y, hy, h | h⟩
  · have := tg_injective K h
    subst this
    omega
  · exact tg_inv_ne K y x h.symm

theorem tg_inv_not_low {k : ℕ} {x : TagKey} (hx : k < x.1) : ¬ Low K k (tg K x)⁻¹ := by
  rintro ⟨y, hy, h | h⟩
  · exact tg_inv_ne K x y h
  · have := tg_injective K (inv_injective h)
    subst this
    omega

/-! ### Independence of non-ancestors -/

omit [CharZero K] in
theorem Q_congr (k : ℕ) : ∀ (v : Vx F) (h h' : Vx F → Fin n),
    (∀ u, anc u v → h u = h' u) → Q fo K k v h = Q fo K k v h' := by
  induction k with
  | zero => intro v h h' _; rfl
  | succ k ih =>
    intro v h h' hh
    simp only [Q]
    congr 1
    funext i
    simp only [P]
    congr 1
    funext j
    congr 1
    cases j with
    | inl e =>
      simp only [blk]
      congr 1
      apply ev_congr
      · have hne : e.1.1 ≠ v := by
          intro he
          have h2 := e.1.2
          rw [he] at h2
          exact anc_irrefl fo v h2
        simp [Function.update_of_ne hne, hh _ e.1.2]
      · simp
    | inr c =>
      simp only [blk]
      apply ih
      intro u hu
      by_cases huv : u = v
      · subst huv; simp
      · rw [Function.update_of_ne huv, Function.update_of_ne huv]
        rcases fo.ancestors_linearly_ordered u v c.1 ⟨hu, c.2.1⟩ with h1 | h1 | h1
        · exact (huv h1).elim
        · exact hh u h1
        · exact (c.2.2 u h1 hu).elim

end

end Lax461425Proofs.SymVFPatternFormula
