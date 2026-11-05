import Lax461425.PatternWidths
import Lax461425Proofs.SymVFTreeSum
import Lax461425Proofs.ComputedFormula
import Mathlib.Logic.Encodable.Basic

/-!
The formula for a homomorphism polynomial along an elimination forest. For a vertex `v` and
an assignment `h` (only read at the proper ancestors of `v`), the formula `Q k v h` sums over
the value `i` of `v` the product of the edge variables from `v` to its ancestors and of the
formulas of the children of `v`. Each factor is tagged by a constant that depends only on the
level, the vertex and the factor, never on the assignment. This file contains the definitions,
the forest combinatorics, and the polynomial computed by the formula.
-/

namespace Lax461425Proofs.SymVFPatternFormula

open Lax461425.Circuits Lax461425.MatrixSymmetry Lax461425.SymmetricFamilies
open Lax461425.HomomorphismPolynomials Lax183560.AncestorForest
open TreeFormulaCircuit TreeFormulaOperations ComputedFormula SymVFTreeSum
open scoped Classical

noncomputable section

/-- The vertices of a pattern. -/
abbrev Vx (F : Pattern) := F.A ⊕ F.B

/-- The symmetric edge multiplicity; vertices on the same side are never adjacent. -/
def mm (F : Pattern) : Vx F → Vx F → ℕ
  | .inl a, .inr b => F.mult a b
  | .inr b, .inl a => F.mult a b
  | .inl _, .inl _ => 0
  | .inr _, .inr _ => 0

variable {F : Pattern} {n : ℕ}

/-- The matrix variable of the edge between `u` and `w` under the assignment `g`. -/
def ev (g : Vx F → Fin n) : Vx F → Vx F → Fin n × Fin n
  | .inl a, .inr b => (g (.inl a), g (.inr b))
  | .inr b, .inl a => (g (.inl a), g (.inr b))
  | u, w => (g u, g w)

theorem ev_congr {g g' : Vx F → Fin n} {u w : Vx F} (hu : g u = g' u) (hw : g w = g' w) :
    ev g u w = ev g' u w := by
  cases u <;> cases w <;> simp [ev, hu, hw]

/-- The permutation of `[n]` acting on the values of a vertex of the given side. -/
def sidePerm (γ : Γ n) : Vx F → Equiv.Perm (Fin n)
  | .inl _ => γ.1
  | .inr _ => γ.2

/-- The action of `Γₙ` on assignments. -/
def act (γ : Γ n) (g : Vx F → Fin n) : Vx F → Fin n := fun w => sidePerm γ w (g w)

theorem act_update (γ : Γ n) (g : Vx F → Fin n) (v : Vx F) (i : Fin n) :
    act γ (Function.update g v i) = Function.update (act γ g) v (sidePerm γ v i) := by
  funext w
  by_cases hw : w = v
  · subst hw; simp [act]
  · simp [act, Function.update_of_ne hw]

theorem ev_act (γ : Γ n) (g : Vx F → Fin n) {u w : Vx F} (h : mm F u w ≠ 0) :
    ev (act γ g) u w = actVar γ (ev g u w) := by
  cases u <;> cases w <;> simp_all [ev, act, sidePerm, actVar, mm]

variable (fo : AncestorForest (Vx F))

local notation "anc" => fo.ancestor

theorem anc_trans {u v w : Vx F} (h₁ : anc u v) (h₂ : anc v w) : anc u w :=
  fo.transitive.trans _ _ _ h₁ h₂

theorem anc_irrefl (u : Vx F) : ¬ anc u u := fo.irreflexive.irrefl u

/-- The vertices strictly below `o`; every vertex for the virtual root `none`. -/
def Above : Option (Vx F) → Vx F → Prop
  | none, _ => True
  | some v, u => anc v u

/-- The children of `o`: the roots for `none`. -/
def Kid (o : Option (Vx F)) (c : Vx F) : Prop :=
  Above fo o c ∧ ∀ u, Above fo o u → ¬ anc u c

/-- The children of `o` as a type. -/
abbrev KidT (o : Option (Vx F)) := {c // Kid fo o c}

/-- The edge occurrences from `v` to its proper ancestors. -/
abbrev EO (v : Vx F) := Σ u : {u // anc u v}, Fin (mm F u.1 v)

/-- The vertex `v` and its descendants. -/
def desc (v : Vx F) : Finset (Vx F) := Finset.univ.filter fun w => w = v ∨ anc v w

/-- The vertices strictly below `o`. -/
def sdesc (o : Option (Vx F)) : Finset (Vx F) := Finset.univ.filter (Above fo o)

/-- The set of vertices read by the edge factors of the vertices in `D`. -/
def up (D : Finset (Vx F)) : Set (Vx F) := {u | ∃ w ∈ D, u = w ∨ anc u w}

/-! ### Forest combinatorics -/

theorem above_of_anc {o : Option (Vx F)} {c w : Vx F} (hc : Above fo o c) (h : anc c w) :
    Above fo o w := by
  cases o with
  | none => trivial
  | some v => exact anc_trans fo hc h

theorem mem_desc {v w : Vx F} : w ∈ desc fo v ↔ w = v ∨ anc v w := by simp [desc]

theorem kid_eq_of_mem {o : Option (Vx F)} {c c' w : Vx F} (hc : Kid fo o c) (hc' : Kid fo o c')
    (hw : w ∈ desc fo c) (hw' : w ∈ desc fo c') : c = c' := by
  rw [mem_desc] at hw hw'
  rcases hw with rfl | hw <;> rcases hw' with rfl | hw'
  · rfl
  · exact (hc.2 c' hc'.1 hw').elim
  · exact (hc'.2 c hc.1 hw).elim
  · rcases fo.ancestors_linearly_ordered c c' w ⟨hw, hw'⟩ with h | h | h
    · exact h
    · exact (hc'.2 c hc.1 h).elim
    · exact (hc.2 c' hc'.1 h).elim

theorem desc_disjoint {o : Option (Vx F)} {c c' : Vx F} (hc : Kid fo o c) (hc' : Kid fo o c')
    (hne : c ≠ c') : Disjoint (desc fo c) (desc fo c') :=
  Finset.disjoint_left.mpr fun _ hw hw' => hne (kid_eq_of_mem fo hc hc' hw hw')

theorem up_disjoint {o : Option (Vx F)} {c c' : Vx F} (hc : Kid fo o c) (hc' : Kid fo o c')
    (hne : c ≠ c') : ∀ u ∈ up fo (desc fo c), u ∉ desc fo c' := by
  rintro u ⟨w, hw, hu⟩ hu'
  apply hne
  apply kid_eq_of_mem fo hc hc' hw
  rw [mem_desc] at hu' ⊢
  rcases hu with rfl | hu
  · exact hu'
  · rcases hu' with rfl | hu'
    · exact Or.inr hu
    · exact Or.inr (anc_trans fo hu' hu)

theorem sdesc_eq_biUnion (rank : Vx F → ℕ) (hrank : ∀ u v, anc u v → rank u < rank v)
    (o : Option (Vx F)) :
    sdesc fo o = Finset.univ.biUnion fun c : KidT fo o => desc fo c.1 := by
  ext w
  simp only [sdesc, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
  constructor
  · intro hw
    obtain ⟨c, hcs, hmin⟩ := Finset.exists_min_image
      (Finset.univ.filter fun u => Above fo o u ∧ (u = w ∨ anc u w)) rank
      ⟨w, by simp [hw]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcs hmin
    refine ⟨⟨c, hcs.1, fun u hu huc => ?_⟩, ?_⟩
    · have huw : anc u w := by
        rcases hcs.2 with rfl | h
        · exact huc
        · exact anc_trans fo huc h
      have := hmin u ⟨hu, Or.inr huw⟩
      have := hrank u c huc
      omega
    · rw [mem_desc]
      rcases hcs.2 with rfl | h
      · exact Or.inl rfl
      · exact Or.inr h
  · rintro ⟨⟨c, hc⟩, hw⟩
    rw [mem_desc] at hw
    rcases hw with rfl | hw
    · exact hc.1
    · exact above_of_anc fo hc.1 hw

theorem desc_eq_insert (v : Vx F) : desc fo v = insert v (sdesc fo (some v)) := by
  ext w
  simp [desc, sdesc, Above]

theorem not_mem_sdesc_self (v : Vx F) : v ∉ sdesc fo (some v) := by
  simp [sdesc, Above, anc_irrefl fo]

/-! ### Polynomials -/

variable (K : Type*) [Field K]

/-- The product of the edge variables from `w` to its proper ancestors. -/
def E (g : Vx F → Fin n) (w : Vx F) : MatrixPolynomial n K :=
  ∏ u : Vx F, if anc u w then MvPolynomial.X (ev g u w) ^ mm F u w else 1

theorem E_dependsOn (w : Vx F) :
    SymVFTreeSum.DependsOn (fun g => E fo K (n := n) g w) {u | u = w ∨ anc u w} := by
  intro g g' hg
  apply Finset.prod_congr rfl
  intro u _
  by_cases hu : anc u w
  · simp only [hu, if_true]
    rw [ev_congr (hg u (Or.inr hu)) (hg w (Or.inl rfl))]
  · simp [hu]

/-- The polynomial computed for the subtree of `v`. -/
def T (v : Vx F) (h : Vx F → Fin n) : MatrixPolynomial n K :=
  sm (desc fo v) h fun g => ∏ w ∈ desc fo v, E fo K g w

theorem prod_desc_dependsOn (D : Finset (Vx F)) :
    SymVFTreeSum.DependsOn (fun g => ∏ w ∈ D, E fo K (n := n) g w) (up fo D) := by
  have := dependsOn_prod D (fun w g => E fo K (n := n) g w) (fun w => {u | u = w ∨ anc u w})
    (fun w _ => E_dependsOn fo K w)
  refine dependsOn_mono this ?_
  intro u hu
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hu
  obtain ⟨w, hw, hu⟩ := hu
  exact ⟨w, hw, hu⟩

/-- Products over the subtrees of the children of `o`. -/
theorem sm_sdesc (rank : Vx F → ℕ) (hrank : ∀ u v, anc u v → rank u < rank v)
    (o : Option (Vx F)) (h : Vx F → Fin n) :
    sm (sdesc fo o) h (fun g => ∏ w ∈ sdesc fo o, E fo K g w) =
      ∏ c : KidT fo o, T fo K c.1 h := by
  have hdis : ∀ c ∈ (Finset.univ : Finset (KidT fo o)), ∀ c' ∈ (Finset.univ : Finset (KidT fo o)),
      c ≠ c' → Disjoint (desc fo c.1) (desc fo c'.1) :=
    fun c _ c' _ hne => desc_disjoint fo c.2 c'.2 (fun e => hne (Subtype.ext e))
  have hprod : ∀ g, ∏ w ∈ sdesc fo o, E fo K (n := n) g w =
      ∏ c : KidT fo o, ∏ w ∈ desc fo c.1, E fo K g w := by
    intro g
    rw [sdesc_eq_biUnion fo rank hrank o, Finset.prod_biUnion hdis]
  simp_rw [hprod]
  rw [sdesc_eq_biUnion fo rank hrank o]
  exact sm_biUnion Finset.univ (fun c : KidT fo o => desc fo c.1)
    (fun c => up fo (desc fo c.1)) (fun c g => ∏ w ∈ desc fo c.1, E fo K g w)
    (fun c _ => prod_desc_dependsOn fo K _) hdis
    (fun c _ c' _ hne => up_disjoint fo c.2 c'.2 (fun e => hne (Subtype.ext e))) h

/-- The recursion for the subtree polynomials. -/
theorem T_eq (rank : Vx F → ℕ) (hrank : ∀ u v, anc u v → rank u < rank v)
    (v : Vx F) (h : Vx F → Fin n) :
    T fo K v h = ∑ i, E fo K (Function.update h v i) v *
      ∏ c : KidT fo (some v), T fo K c.1 (Function.update h v i) := by
  unfold T
  rw [desc_eq_insert fo v]
  simp_rw [Finset.prod_insert (not_mem_sdesc_self fo v)]
  rw [sm_insert (not_mem_sdesc_self fo v)]
  apply Finset.sum_congr rfl
  intro i _
  rw [sm_mul_left (S := {u | u = v ∨ anc u v}) ?_ _ _ _ (E_dependsOn fo K v)]
  · rw [sm_sdesc fo K rank hrank]
    rfl
  · rintro u hu hu'
    simp only [sdesc, Above, Finset.mem_filter, Finset.mem_univ, true_and] at hu'
    rcases hu with rfl | hu
    · exact anc_irrefl fo u hu'
    · exact anc_irrefl fo v (anc_trans fo hu' hu)

/-- The homomorphism polynomial as the sum over all assignments of the edge factors. -/
theorem hom_eq_sm (hclos : ∀ ⦃u v : Vx F⦄, (underlying F).Adj u v → anc u v ∨ anc v u)
    (h₀ : Vx F → Fin n) :
    hom K F n = sm (sdesc fo none) h₀ (fun g => ∏ w ∈ sdesc fo none, E fo K g w) := by
  have hs : sdesc fo none = Finset.univ := by ext; simp [sdesc, Above]
  have hagree : agree (Finset.univ : Finset (Vx F)) h₀ = Finset.univ := by
    ext g; simp [agree]
  rw [hs]
  unfold sm
  rw [hagree]
  unfold hom
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow F.A F.B (Fin n)).symm _ _ ?_)
  rintro ⟨hA, hB⟩
  -- Rewrite the product over vertices as a product over pairs.
  simp only [E, Fintype.prod_sum_type, mm, ev, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, pow_zero, ite_self, Finset.prod_const_one,
    one_mul, mul_one]
  rw [Finset.prod_comm (s := (Finset.univ : Finset F.B)), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro b _
  by_cases hm : F.mult a b = 0
  · simp [hm]
  · have hadj : (underlying F).Adj (.inl a) (.inr b) := by
      rw [underlying, SimpleGraph.fromRel_adj]
      exact ⟨by simp, Or.inl ⟨a, b, rfl, rfl, hm⟩⟩
    rcases hclos hadj with h | h
    · have h' : ¬ anc (.inr b) (.inl a) := fun h' => anc_irrefl fo _ (anc_trans fo h h')
      simp [h, h']
    · have h' : ¬ anc (.inl a) (.inr b) := fun h' => anc_irrefl fo _ (anc_trans fo h h')
      simp [h, h']

end

end Lax461425Proofs.SymVFPatternFormula
