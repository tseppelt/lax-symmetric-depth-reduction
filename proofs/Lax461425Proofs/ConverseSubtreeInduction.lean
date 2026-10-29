import Lax461425Proofs.ConverseSubtreeGlue

/-!
**Step 1, concluded.** The main theorem `P_eq_sum_ExtV`:
$$
  P\,t\,\gamma = \sum_{h \supseteq \gamma \text{ admissible on } V\,t}
    \ \prod_{ab : \mathrm{rep}(a,b) \succeq t} x_{h(a),h(b)}^{F.mult\,a\,b},
$$
proved by well-founded recursion on `Δ - level t`, mirroring `P`'s own recursion. The inductive
step combines: `Gval_eq_mul_prod`/`GvalAt_eq_of_ExtV` (the pointwise edge decomposition),
`Q_eq_sum_ExtVchild` (collapsing `Q`'s defining sum through the inductive hypothesis), the
gluing bijection of `ConverseSubtreeGlue.lean` (via `Finset.sum_bij'`), and
`Finset.prod_univ_sum` (distributing a product of sums into a sum, over a `piFinset`, of
products).
-/

namespace Lax461425Proofs

open Classical Lax461425.Circuits Lax461425.Circuits.Circuit Lax461425.HomomorphismPolynomials
open Lax461425.Forestwidth
open MvPolynomial

variable {F : Pattern} {Δ k : ℕ}

section Collapse

/-- Collapsing a sum over a sum indexed by fiber: summing `G x` over those `x` whose `ρ x` lies
in `S`, grouped first by the value `ρ x`, is the same as summing directly over that filtered
set. -/
theorem sum_filter_comp_eq_sum_fiber {α β M : Type*} [AddCommMonoid M] [Fintype α] [DecidableEq β]
    (ρ : α → β) (S : Finset β) (G : α → M) :
    ∑ y ∈ S, ∑ x ∈ (Finset.univ : Finset α).filter (fun x => ρ x = y), G x =
      ∑ x ∈ (Finset.univ : Finset α).filter (fun x => ρ x ∈ S), G x := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset α).filter (fun x => ρ x ∈ S)) (t := S) (g := ρ)
    (fun x hx => (Finset.mem_filter.mp hx).2) G]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro heq; exact ⟨heq ▸ hy, heq⟩
  · rintro ⟨_, heq⟩; exact heq

end Collapse

section QCollapse

variable (N : NormDecomp F Δ k) (n : ℕ) {K : Type*} [CommSemiring K]

/-- Collapsing `Q`'s own defining sum (over `γ'` extending `δ` on `bag c`, of `P c γ'`) into a
sum over `ExtVchild c δ`, given the inductive hypothesis relating `P c γ'` to a sum over
`ExtV c γ'`. -/
theorem Q_eq_sum_ExtVchild (c : NonRoot N) (δ : Adm F n (N.bag (N.parent c.1) ∩ N.bag c.1))
    (hIH : ∀ γ' : Adm F n (N.bag c.1),
      P N n (K := K) c.1 γ' = ∑ h ∈ ExtV N n c.1 γ', Gval N n (K := K) c.1 h) :
    Q N n (K := K) c δ = ∑ h ∈ ExtVchild N n c δ, Gval N n (K := K) c.1 h := by
  have hQ : Q N n (K := K) c δ =
      ∑ γ' ∈ (Finset.univ : Finset (Adm F n (N.bag c.1))).filter
        (fun γ' => ∀ (x : F.A ⊕ F.B) (hx : x ∈ N.bag (N.parent c.1) ∩ N.bag c.1),
          γ' ⟨x, Finset.inter_subset_right hx⟩ = δ ⟨x, hx⟩),
      ∑ h ∈ (Finset.univ : Finset (Adm F n (V N c.1))).filter (fun h => restrictV N n h = γ'),
        Gval N n (K := K) c.1 h := by
    unfold Q
    exact Finset.sum_congr rfl (fun γ' _ => hIH γ')
  rw [hQ, sum_filter_comp_eq_sum_fiber (restrictV N n) _ (Gval N n (K := K) c.1)]
  congr 1
  ext h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_ExtVchild]
  constructor
  · intro hmem x hx; exact hmem x hx
  · intro hmem x hx; exact hmem x hx

end QCollapse

section MainInduction

variable (N : NormDecomp F Δ k) (n : ℕ) {K : Type*} [CommSemiring K]

theorem Gval_eq_mul_prod' (t : N.Node) (h : Adm F n (V N t)) :
    Gval N n (K := K) t h = GvalAt N n (K := K) t h *
      ∏ cc : ↥(children N t),
        Gval N n (K := K) cc.1.1 (restrictVchild' N n ((mem_children N).mp cc.2) h) := by
  rw [Gval_eq_mul_prod, Finset.univ_eq_attach]

theorem extendToNonRoot_toChildren_eq_toChildrenFull (hn0 : 0 < n) {t : N.Node}
    (h : Adm F n (V N t)) :
    extendToNonRoot N n hn0
        (fun cc : ↥(children N t) => restrictVchild' N n ((mem_children N).mp cc.2) h) =
      toChildrenFull N n hn0 h := by
  funext c
  by_cases hc : c ∈ children N t
  · rw [extendToNonRoot_apply_of_mem N n hn0 _ hc, toChildrenFull_apply_of_mem N n hn0 h hc]
  · unfold extendToNonRoot toChildrenFull
    rw [dif_neg hc]

/-- `GvalAt t h` agrees with the first factor of `P_eq` whenever `h` extends `γ` on `bag t`. -/
theorem GvalAt_eq_of_ExtV {t : N.Node} (γ : Adm F n (N.bag t)) (h : Adm F n (V N t))
    (hh : h ∈ ExtV N n t γ) :
    GvalAt N n (K := K) t h =
      ∏ ab ∈ (edgesAt N t).attach,
        (X (γ ⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩, γ ⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩) :
          MvPolynomial (Fin n × Fin n) K) ^ F.mult ab.1.1 ab.1.2 := by
  unfold GvalAt
  apply Finset.prod_congr rfl
  intro ab _
  have h1 := congrFun ((mem_ExtV N n).mp hh) ⟨Sum.inl ab.1.1, mem_bag_left N ab.2⟩
  have h2 := congrFun ((mem_ExtV N n).mp hh) ⟨Sum.inr ab.1.2, mem_bag_right N ab.2⟩
  simp only [restrictV] at h1 h2
  rw [h1, h2]

/-- **The gluing bijection, as a sum identity.** Reindexing the sum over `ExtV t γ` by
restricting to each child recovers the sum over the `piFinset` of the children's `ExtVchild`
Finsets. -/
theorem sum_ExtV_eq_sum_piFinset (hn0 : 0 < n) {t : N.Node} (γ : Adm F n (N.bag t)) :
    ∑ h ∈ ExtV N n t γ,
        ∏ cc : ↥(children N t),
          Gval N n (K := K) cc.1.1 (restrictVchild' N n ((mem_children N).mp cc.2) h) =
      ∑ x ∈ Fintype.piFinset (fun cc : ↥(children N t) =>
          ExtVchild N n cc.1 (restrictFromParent N n cc.1 ((mem_children N).mp cc.2) γ)),
        ∏ cc : ↥(children N t), Gval N n (K := K) cc.1.1 (x cc) := by
  apply Finset.sum_bij'
    (i := fun h _ => fun cc : ↥(children N t) => restrictVchild' N n ((mem_children N).mp cc.2) h)
    (j := fun x _ => glueBack N n γ (extendToNonRoot N n hn0 x))
  · intro h hh
    rw [Fintype.mem_piFinset]
    intro cc
    exact restrictVchild'_mem_ExtVchild N n γ h hh cc.1 ((mem_children N).mp cc.2)
  · intro x _
    exact (mem_ExtV N n).mpr (restrictV_glueBack N n γ (extendToNonRoot N n hn0 x))
  · intro h hh
    rw [extendToNonRoot_toChildren_eq_toChildrenFull]
    exact glueBack_toChildrenFull N n hn0 γ h hh
  · intro x hx
    funext cc
    have hxc : (extendToNonRoot N n hn0 x) cc.1 ∈
        ExtVchild N n cc.1 (restrictFromParent N n cc.1 ((mem_children N).mp cc.2) γ) := by
      rw [extendToNonRoot_apply_of_mem N n hn0 x cc.2]
      exact Fintype.mem_piFinset.mp hx cc
    rw [restrictVchild'_glueBack N n γ (extendToNonRoot N n hn0 x) cc.1
      ((mem_children N).mp cc.2) hxc]
    exact extendToNonRoot_apply_of_mem N n hn0 x cc.2
  · intro h _
    rfl

/-- Collapsing the product, over all children of `t`, of `Q`'s values at the right
restrictions of `γ`, into a product over `ExtVchild`'s sums, given the inductive hypothesis at
every child. -/
theorem prod_Q_eq_prod_sum_ExtVchild (t : N.Node) (γ : Adm F n (N.bag t))
    (hIH : ∀ (c : NonRoot N), N.parent c.1 = t → ∀ γ' : Adm F n (N.bag c.1),
      P N n (K := K) c.1 γ' = ∑ h ∈ ExtV N n c.1 γ', Gval N n (K := K) c.1 h) :
    ∏ cc ∈ (children N t).attach,
        Q N n (K := K) cc.1 (restrictFromParent N n cc.1 ((mem_children N).mp cc.2) γ) =
      ∏ cc : ↥(children N t),
        ∑ h ∈ ExtVchild N n cc.1 (restrictFromParent N n cc.1 ((mem_children N).mp cc.2) γ),
          Gval N n (K := K) cc.1.1 h := by
  rw [← Finset.univ_eq_attach]
  apply Finset.prod_congr rfl
  intro cc _
  exact Q_eq_sum_ExtVchild N n cc.1 _ (fun γ' => hIH cc.1 ((mem_children N).mp cc.2) γ')

/-- **Step 1, the main theorem.** `P t γ` equals the sum, over admissible maps `h` on the
subtree vertex set `V t` extending `γ` on `bag t`, of the product over all edges represented
at-or-below `t` of the corresponding variable. -/
theorem P_eq_sum_ExtV (hn0 : 0 < n) : ∀ t : N.Node, ∀ γ : Adm F n (N.bag t),
    P N n (K := K) t γ = ∑ h ∈ ExtV N n t γ, Gval N n (K := K) t h
  | t => by
      intro γ
      rw [P_eq,
        prod_Q_eq_prod_sum_ExtVchild N n t γ (fun c hp γ' => by
          have hlt : Δ - level N.depth_le c.1 < Δ - level N.depth_le t := by
            have hlev : level N.depth_le c.1 = level N.depth_le t + 1 := by
              rw [level_succ N.depth_le N.parent_root c.2, hp]
            have hle : level N.depth_le c.1 ≤ Δ := level_le N.depth_le c.1
            omega
          exact P_eq_sum_ExtV hn0 c.1 γ'),
        Finset.prod_univ_sum, ← sum_ExtV_eq_sum_piFinset N n hn0 γ, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun h hh => ?_)
      rw [Gval_eq_mul_prod' N n t h, GvalAt_eq_of_ExtV N n γ h hh]
  termination_by t => Δ - level N.depth_le t
  decreasing_by assumption

end MainInduction

end Lax461425Proofs
